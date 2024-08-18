#lang rosette/safe

(require
 "machine.rkt"
 "register.rkt"
 "environment.rkt"
 "instruction.rkt"
 "value.rkt"
 "lib.rkt"
 "types.rkt"
 "memory.rkt"
 "memory-data.rkt"
 "builtins.rkt"
 "parameters.rkt"
 rosette/lib/destruct
 (only-in racket/base current-inexact-milliseconds))

(provide get-current-instruction get-branch-cases step run run* halted?)

(define (halted? state)
  (equal? (regfile-pc (machine-registers state))
          (if (strict-compcert-semantics) nullptr undef)))

(define (nextinstr state)
  (define rf (machine-registers state))
  (define rf* (write-pc rf (offset-pointer (read-pc rf) (bv 1 32))))
  (machine rf* (machine-memory state)))

;; Asm.exec_load
;;
;; Returns a new machine
(define (exec-load chunk rf mem rd ra ofs)
  (define addr-base (read-ireg rf ra))
  (define v (loadv chunk mem (offset-pointer addr-base ofs)))
  (unless v
    (assert #f "exec-load: failed to load"))
  (nextinstr (machine (write-ireg rf rd v) mem)))

;; Asm.exec_store
;;
;; Returns a new machine
(define (exec-store chunk rf mem rs ra ofs)
  (define addr-base (read-ireg rf ra))
  (define mem* (storev chunk mem (offset-pointer addr-base ofs) (read-ireg rf rs)))
  (unless mem*
    (assert #f "exec-store: failed to store"))
  (nextinstr (machine rf mem*)))

;; Asm.label_pos
(define (label-pos lbl pos code)
  (if (>= pos (vector-length code))
      #f
      (let ([instr (vector-ref code pos)])
        (if (and (Plabel? instr) (equal? (Plabel-lbl instr) lbl))
            (add1 pos)
            (label-pos lbl (add1 pos) code)))))

;; Asm.goto_label
;;
;; Though we pass code directly
(define (goto-label code lbl rf mem)
  (define pos (label-pos lbl 0 code))
  (unless pos
    (assert #f "goto-label: cannot find label"))
  (define pc (read-pc rf))
  (unless (pointer? pc)
    (assert #f "goto-label: pc is not a pointer"))
  (define pc* (pointer (pointer-block pc) (integer->bitvector pos (bitvector 32))))
  (define rf* (write-pc rf pc*))
  (machine rf* mem))

;; Asm.eval_branch
(define (eval-branch code lbl rf mem res)
  (if (some? res)
      (if (some-value res)
          (goto-label code lbl rf mem)
          (nextinstr (machine rf mem)))
      (assert #f "eval-branch: comparison result is invalid")))

;; Events.eval_builtin_args
;;
;; We don't need to pass environment here because our symbol -> block mapping
;; is the identity mapping
(define (eval-builtin-arg ba rf mem)
  (destruct
   ba
   [(BA x) (read-ireg rf x)]
   [(BA_int n) n]
   [(BA_long n) n]
   [(BA_loadstack chunk ofs)
    (or (loadv chunk mem (offset-pointer (read-ireg rf sp) ofs))
        (assert #f "eval-builtin-arg: load stack failed"))]
   [(BA_addrstack ofs)
    (offset-pointer (read-ireg rf sp) ofs)]
   [(BA_loadglobal chunk id ofs)
    (or (loadv chunk mem (pointer id ofs))
        (assert #f "eval-builtin-arg: load global failed"))]
   [(BA_addrglobal id ofs)
    (pointer id ofs)]
   [(BA_splitlong hi lo)
    (let ([vhi (eval-builtin-arg hi rf mem)]
          [vlo (eval-builtin-arg lo rf mem)])
      (value-longofwords vhi vlo))]
   [(BA_addptr a1 a2)
    (let ([va1 (eval-builtin-arg a1 rf mem)]
          [va2 (eval-builtin-arg a2 rf mem)])
      (value-add va1 va2))]))

;; Asm.set_res
(define (set-res res v rf)
  (destruct
   res
   [(BR r) (write-ireg rf r v)]
   [(BR_none) rf]
   [(BR_splitlong hi lo)
    (set-res lo (value-loword v) (set-res hi (value-hiword v) rf))]))

(define (exec-builtin rf mem ef args res)
  (define vargs (map (lambda (ba) (eval-builtin-arg ba rf mem)) args))
  ;; Events.external_call, though we've done some simplification and flattening
  (destruct
   ef
   ;; Events.known_builtin_sem: calls builtin_function_sem, only uses vargs and produces a vres,
   [(EF_builtin f)
    ;; doesn't access registers or memory
    (define vres (eval-builtin f vargs))
    (define rf* (set-res res vres rf))
    (machine rf* mem)]
   ;; Events.extcall_memcpy_sem
   [(EF_memcpy sz al)
    ;; get arguments
    (define v1 (first vargs))
    (define v2 (second vargs))
    (unless (and (pointer? v1) (pointer? v2))
      (assert #f "exec-builtin: memcpy with non-pointer values"))
    (define bdst (pointer-block v1))
    (define odst (bitvector->natural (pointer-offset v1)))
    (define bsrc (pointer-block v2))
    (define osrc (bitvector->natural (pointer-offset v2)))
    ;; check alignment and other preconditions
    (unless (and
             (or (equal? al 1) (equal? al 2) (equal? al 4) (equal? al 8))
             (>= sz 0)
             (zero? (modulo sz al))
             (if (> sz 0) (zero? (modulo osrc al)) #t)
             (if (> sz 0) (zero? (modulo odst al)) #t)
             (or (not (equal? bsrc bdst))
                 (equal? osrc odst)
                 (<= (+ osrc sz) odst)
                 (<= (+ odst sz) osrc)))
      (assert #f "exec-builtin: memcpy precondition not satisfied"))
    (define bs (loadbytes mem bsrc osrc sz))
    (unless bs
      (assert #f "exec-builtin: memcpy loadbytes failed"))
    (define mem* (storebytes mem bdst odst bs))
    (unless mem*
      (assert #f "exec-builtin: memcpy storebytes failed"))
    (machine rf mem*)]
   [else (assert #f "exec-builtin: unsupported external function")]))

;; for debugging/convenience
(define (get-current-instruction state environment)
  (define rf (machine-registers state))
  (define pc (read-pc rf))
  (unless (pointer? pc)
    (assert #f "get-current-instruction: pc is not a pointer"))
  (define block (pointer-block pc))
  (define defs (global-environment-definitions environment))
  (when (>= block (length defs))
    (assert #f "get-current-instruction: pc points to an invalid block"))
  (define def (list-ref defs block))
  (unless (function-definition? def)
    (assert #f "get-current-instruction: pc does not point to a function"))
  (define code (function-definition-code def))
  (when (>= (bitvector->natural (pointer-offset pc)) (vector-length code))
    (assert #f "get-current-instruction: pc points beyonds the bounds of a function"))
  (define instr (vector-ref-bv code (pointer-offset pc)))
  instr)

;; for proofs, for case analysis on branching
;;
;; assumes that instruction is a branch, and semantics does not throw an error
(define (get-branch-cases state environment)
  (define instr (get-current-instruction state environment))
  (define rf (machine-registers state))
  (define mem (machine-memory state))
  (define c
    (destruct
     instr
     [(Pbeqw rs1 rs2 lbl)
      (some-value (value-cmpu-bool (valid-pointer?* mem) Ceq (read-ireg rf rs1) (read-ireg rf rs2)))]
     [(Pbnew rs1 rs2 lbl)
      (some-value (value-cmpu-bool (valid-pointer?* mem) Cne (read-ireg rf rs1) (read-ireg rf rs2)))]
     [(Pbltw rs1 rs2 lbl)
      (some-value (value-cmp-bool Clt (read-ireg rf rs1) (read-ireg rf rs2)))]
     [(Pbltuw rs1 rs2 lbl)
      (some-value (value-cmpu-bool (valid-pointer?* mem) Clt (read-ireg rf rs1) (read-ireg rf rs2)))]
     [(Pbgew rs1 rs2 lbl)
      (some-value (value-cmp-bool Cge (read-ireg rf rs1) (read-ireg rf rs2)))]
     [(Pbgeuw rs1 rs2 lbl)
      (some-value (value-cmpu-bool (valid-pointer?* mem) Cge (read-ireg rf rs1) (read-ireg rf rs2)))]))
  (if (concrete? c) (list #t) (list c (! c))))

;; compcert.riscV.Asm.exec_instr
(define (step state environment)
  (define rf (machine-registers state))
  (define mem (machine-memory state))
  (define pc (read-pc rf))
  (unless (pointer? pc)
    (assert #f "step: pc is not a pointer"))
  (define block (pointer-block pc))
  (define defs (global-environment-definitions environment))
  (when (>= block (length defs))
    (assert #f "step: pc points to an invalid block"))
  (define def (list-ref defs block))
  (unless (function-definition? def)
    (assert #f "step: pc does not point to a function"))
  (define code (function-definition-code def))
  (when (>= (bitvector->natural (pointer-offset pc)) (vector-length code))
    (assert #f "step: pc points beyonds the bounds of a function"))
  (define instr (vector-ref-bv code (pointer-offset pc)))

  (destruct
   instr
   ;; there's a case here for each case in instruction.rkt
   [(Pmv rd rs)
    (nextinstr (machine (write-ireg rf rd (read-ireg rf rs)) mem))]

    ;; 32-bit integer register-immediate instructions
   [(Paddiw rd rs imm)
    (nextinstr (machine (write-ireg rf rd (value-add (read-ireg rf rs) imm)) mem))]
   [(Psltiw rd rs imm)
    (nextinstr (machine (write-ireg rf rd (value-cmp Clt (read-ireg rf rs) imm)) mem))]
   [(Psltiuw rd rs imm)
    (nextinstr (machine (write-ireg rf rd (value-cmpu (valid-pointer?* mem) Clt (read-ireg rf rs) imm)) mem))]
   [(Pandiw rd rs imm)
    (nextinstr (machine (write-ireg rf rd (value-and (read-ireg rf rs) imm)) mem))]
   [(Poriw rd rs imm)
    (nextinstr (machine (write-ireg rf rd (value-or (read-ireg rf rs) imm)) mem))]
   [(Pxoriw rd rs imm)
    (nextinstr (machine (write-ireg rf rd (value-xor (read-ireg rf rs) imm)) mem))]
   [(Pslliw rd rs imm)
    (nextinstr (machine (write-ireg rf rd (value-shl (read-ireg rf rs) imm)) mem))]
   [(Psrliw rd rs imm)
    (nextinstr (machine (write-ireg rf rd (value-shru (read-ireg rf rs) imm)) mem))]
   [(Psraiw rd rs imm)
    (nextinstr (machine (write-ireg rf rd (value-shr (read-ireg rf rs) imm)) mem))]
   [(Pluiw rd imm)
    (nextinstr (machine (write-ireg rf rd (bvshl imm (bv 12 32))) mem))]

   ;; 32-bit integer register-register instructions
   [(Paddw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-add (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Psubw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-sub (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Pmulw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-mul (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Pmulhw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-mulhs (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Pmulhuw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-mulhu (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Pdivw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-divs-total (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Pdivuw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-divu-total (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Premw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-mods-total (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Premuw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-modu-total (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Psltw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-cmp Clt (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Psltuw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-cmpu (valid-pointer?* mem) Clt (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Pseqw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-cmpu (valid-pointer?* mem) Ceq (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Psnew rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-cmpu (valid-pointer?* mem) Cne (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Pandw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-and (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Porw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-or (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Pxorw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-xor (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Psllw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-shl (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Psrlw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-shru (read-ireg rf rs1) (read-ireg rf rs2))) mem))]
   [(Psraw rd rs1 rs2)
    (nextinstr (machine (write-ireg rf rd (value-shr (read-ireg rf rs1) (read-ireg rf rs2))) mem))]

   ;; unconditional jumps
   [(Pj_l l)
    (goto-label code l rf mem)]
   [(Pj_s s)
    ;; convert this symbol to an address (but we use an identity mapping)
    ;; just need to make sure it's valid
    (when (>= s (length defs))
      (assert #f "step: Pj_s: invalid symbol"))
    (machine (write-pc rf (pointer s (bv 0 32))) mem)]
   [(Pj_r r)
    (machine (write-pc rf (read-ireg rf r)) mem)]
   [(Pjal_s s)
    (when (>= s (length defs))
      (assert #f "step: Pjal_s: invalid symbol"))
    (let ([ret-addr (offset-pointer (read-pc rf) (bv 1 32))]
          [new-pc (pointer s (bv 0 32))])
      (machine (write-ireg (write-pc rf new-pc) ra ret-addr) mem))]
   [(Pjal_r r)
    (let ([ret-addr (offset-pointer (read-pc rf) (bv 1 32))]
          [new-pc (read-ireg rf r)])
      (machine (write-ireg (write-pc rf new-pc) ra ret-addr) mem))]

   ;; conditional branches, 32-bit comparisons
   [(Pbeqw rs1 rs2 lbl)
    (eval-branch code lbl rf mem (value-cmpu-bool (valid-pointer?* mem) Ceq (read-ireg rf rs1) (read-ireg rf rs2)))]
   [(Pbnew rs1 rs2 lbl)
    (eval-branch code lbl rf mem (value-cmpu-bool (valid-pointer?* mem) Cne (read-ireg rf rs1) (read-ireg rf rs2)))]
   [(Pbltw rs1 rs2 lbl)
    (eval-branch code lbl rf mem (value-cmp-bool Clt (read-ireg rf rs1) (read-ireg rf rs2)))]
   [(Pbltuw rs1 rs2 lbl)
    (eval-branch code lbl rf mem (value-cmpu-bool (valid-pointer?* mem) Clt (read-ireg rf rs1) (read-ireg rf rs2)))]
   [(Pbgew rs1 rs2 lbl)
    (eval-branch code lbl rf mem (value-cmp-bool Cge (read-ireg rf rs1) (read-ireg rf rs2)))]
   [(Pbgeuw rs1 rs2 lbl)
    (eval-branch code lbl rf mem (value-cmpu-bool (valid-pointer?* mem) Cge (read-ireg rf rs1) (read-ireg rf rs2)))]

   ;; loads and stores
   [(Plb rd ra ofs)
    (exec-load chunk-int8signed rf mem rd ra ofs)]
   [(Plbu rd ra ofs)
    (exec-load chunk-int8unsigned rf mem rd ra ofs)]
   [(Plh rd ra ofs)
    (exec-load chunk-int16signed rf mem rd ra ofs)]
   [(Plhu rd ra ofs)
    (exec-load chunk-int16unsigned rf mem rd ra ofs)]
   [(Plw rd ra ofs)
    (exec-load chunk-int32 rf mem rd ra ofs)]
   [(Plw_a rd ra ofs)
    (exec-load chunk-any32 rf mem rd ra ofs)]
   [(Psb rs ra ofs)
    (exec-store chunk-int8signed rf mem rs ra ofs)]
   [(Psh rs ra ofs)
    (exec-store chunk-int16unsigned rf mem rs ra ofs)]
   [(Psw rs ra ofs)
    (exec-store chunk-int32 rf mem rs ra ofs)]
   [(Psw_a rs ra ofs)
    (exec-store chunk-any32 rf mem rs ra ofs)]

    ;; pseudo-instructions
   [(Pallocframe sz pos)
    ;; allocate a memory block with bounds [0, sz)
    (let* ([r (alloc mem sz)]
           [b (car r)]
           [m1 (cdr r)]
           ;; set the stack pointer to the address of the bottom of this block
           [vsp (pointer b (bv 0 32))]
           ;; store the value of the old stack pointer at offset pos in this block
           [m2 (storev chunk-int32 m1 (offset-pointer vsp pos) (read-ireg rf sp))]
           ;; update register values
           [rf1 (write-ireg rf t5 (read-ireg rf sp))] ; gets clobbered because asm uses it to store sp temporarily
           [rf2 (write-ireg rf1 sp vsp)]
           [rf3 (write-ireg rf2 t6 undef)])
      (unless m2
        (assert #f "step: Pallocframe: storev failed")) ; should never happen
      (nextinstr (machine rf3 m2)))]
   [(Pfreeframe sz pos)
    (let ([prev-sp (loadv chunk-int32 mem (offset-pointer (read-ireg rf sp) pos))]
          [curr-sp (read-ireg rf sp)])
      (unless prev-sp
        (assert #f "step: Pfreeframe: loadv failed"))
      (unless (pointer? curr-sp)
        (assert #f "step: Pfreeframe: sp not a pointer"))
      (let* ([m1 (free mem (pointer-block curr-sp))]
             [rf1 (write-ireg rf sp prev-sp)]
             [rf2 (write-ireg rf1 t6 undef)])
        (unless m1
          (assert #f "step: Pfreeframe: free failed"))
        (nextinstr (machine rf2 m1))))]
   [(Plabel lbl)
    (nextinstr state)]
   [(Ploadsymbol rd id ofs)
    (nextinstr (machine (write-ireg rf rd (pointer id ofs)) mem))]
   [(Ploadsymbol_high rd id ofs)
    (nextinstr (machine (write-ireg rf rd (high-half (pointer id ofs))) mem))]
   [(Pbtbl r tbl)
    (let ([n (read-ireg rf r)]
          [rf1 (write-ireg (write-ireg rf t0 undef) t6 undef)])
      (unless (int32? n)
        (assert #f "step: Pbtbl: register is not an int32"))
      (when (bvuge n (length-bv tbl (bitvector 32)))
        (assert #f "step: Pbtbl: out-of-bounds index"))
      (for/all ([lbl (list-ref-bv tbl n) #:exhaustive])
        (goto-label code lbl rf1 mem)))]
   [(Pbuiltin ef args res)
    (define machine1 (exec-builtin rf mem ef args res))
    (define rf2
      (foldl (lambda (r rf) (write-ireg rf r undef)) (machine-registers machine1) (destroyed-by-builtin ef)))
    (define rf3 (write-ireg (write-ireg rf2 ra undef) t6 undef))
    (nextinstr (machine rf3 (machine-memory machine1)))]

   [else
    (assert #f (format "step: illegal instruction ~v" instr))]))

(define (run state environment)
  (if (halted? state)
      state
      (begin
        (unless (pointer? (read-pc (machine-registers state)))
          (assert #f "run: pc is not a pointer"))
        ;; we can't just do a for/all over the pc, because the pc is a
        ;; struct pointer, and if there's a common block (or a common offset),
        ;; the ite will be pushed inside the struct, and this won't do any decomposition;
        ;; so we do a for/all over the block and the offset individually as well;
        ;; the outer layer is unnecessary unless pc is a symbolic union, which I don't
        ;; think it should ever be (it's always a pointer, so the
        ;; symbolics will be pushed inside), but the extra for/all doesn't hurt
        (for/all ([pc (read-pc (machine-registers state)) #:exhaustive])
          (for/all ([block (pointer-block pc) #:exhaustive])
            (for/all ([offset (pointer-offset pc) #:exhaustive])
              (define pc* (pointer block offset))
              (define state* (machine (write-pc (machine-registers state) pc*) (machine-memory state)))
              (run (step state* environment) environment)))))))

;; for benchmarking
(define (run* state environment)
  (define start (current-inexact-milliseconds))
  (define res
    (let rec ([state state]
              [environment environment]
              [instr-count 0])
      (if (halted? state)
          (cons state instr-count)
          (begin
            (unless (pointer? (read-pc (machine-registers state)))
              (assert #f "run: pc is not a pointer"))
            (for/all ([pc (read-pc (machine-registers state)) #:exhaustive])
              (for/all ([block (pointer-block pc) #:exhaustive])
                (for/all ([offset (pointer-offset pc) #:exhaustive])
                  (define pc* (pointer block offset))
                  (define state* (machine (write-pc (machine-registers state) pc*) (machine-memory state)))
                  (set! instr-count (add1 instr-count))
                  (rec (step state* environment) environment (add1 instr-count)))))))))
  (define end (current-inexact-milliseconds))
  (define r (car res))
  (define instr-count (cdr res))
  (define dur (- end start))
  (printf "finished in ~a milliseconds, ~a instructions, ~a instructions per second~n"
          dur
          instr-count
          (* (/ instr-count dur) 1000))
  r)
