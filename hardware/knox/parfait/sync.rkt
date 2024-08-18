#lang racket/base

(require
 crv32
 crv32/instruction crv32/builtins
 (only-in crv32/types int32?)
 (only-in crv32/lib vector-set)
 (only-in crv32/memory block-size loadbytes valid-pointer?)
 (only-in crv32/memory-data byte?)
 "spec.rkt"
 (prefix-in @ (combine-in rosette/safe rosutil))
 racket/match racket/list)


(provide
 (struct-out mapping)
 new-sync-state
 sync)

(struct mapping
  (
   ;; just the cpu part of the circuit
   cpu-lens
   ;; instruction mapping
   instruction ; ckt -> #f or (bitvector 32)
   symbolic-branch? ; ckt -> boolean?
   branch-delay ; integer?
   memcpy-delay ; integer? > 0
   ;; register mapping
   registers ; symbol? or (vectorof symbol?)
   ;; memory mapping
   ram ; symbol?
   ram-pointer? ; (bitvector 32) -> boolean?
   ram-base ; (bitvector 32)
   ;; for debugging:
   program-counter ; symbol?
   ))

(struct sync-branch (n))
(struct sync-symbolic-branch ())
(struct sync-arithmetic ())
(struct sync-arithmetic-2 ()) ; sync after seeing one more hardware instruction
(struct sync-memcpy (n))

(struct sync-state
  (mapping flag))

(define (new-sync-state mapping)
  (sync-state mapping #f))

;; returns a list of lists,
;; where each component list has a (circuit state, spec state, sync state, path condition)
;;
;; returns a list because sync might decide to do case analysis
;; returns new circuit state too because it might case-split/concretize/abstract, though this function
;; will only step the spec, never the circuit
;;
;; note: for now, we don't actually track the branch condition here, for any splits done here,
;; to keep things simple; shouldn't be necessary for Parfait VMs; this is sound, but it might
;; prevent us from verifying some circuits
(define (sync c s state spec #:verbose [verbose #f])
  (match-define (sync-state mapping flag) state)
  (cond
    [(halted? s)
     (printf "SYNC halted @ ~v~n"
             (@get-field c (mapping-program-counter mapping)))
     (list (list c s #f #t))]
    [(sync-symbolic-branch? flag)
     (cond
       [((mapping-symbolic-branch? mapping) c)
        (when verbose
          (printf "SYNC symbolic-branch @ ~v --- ~v [~v]~n"
                  (@get-field c (mapping-program-counter mapping))
                  (regfile-pc (machine-registers s))
                  (get-current-instruction s (spec-environment spec))))
        (define s1 (step1 s spec))
        (define cases (get-branch-cases s (spec-environment spec)))
        (for/list ([path-cond cases])
          (define s2 (@lens-transform (@lens 'registers 'pc) s1 (lambda (view) (@concretize view path-cond))))
          (define c1 (@lens-transform (mapping-cpu-lens mapping)
                                      c
                                      (lambda (view) (@concretize view path-cond #:piecewise #t))))
          (define-values (c2 s3) (sync-registers c1 s2 mapping #:verbose verbose))
          (define-values (c3 s4) (sync-all-buffers c2 s3 mapping #:verbose verbose))
          (list c3 s4 (sync-state mapping #f) path-cond))]
       [else
        ;; keep waiting
        (list (list c s state #t))])]
    ;; memcpy is early, to intercept everything that happens between nops
    [(sync-memcpy? flag)
     (cond
       [(eqv? (sync-memcpy-n flag) #f)
        (cond
          [(is-hardware-nop? c mapping)
           ;; now, start counting down
           (list (list c s (sync-state mapping (sync-memcpy (mapping-memcpy-delay mapping))) #t))]
          [else
           ;; keep waiting
           (list (list c s state #t))])]
       [(> (sync-memcpy-n flag) 0)
        ;; keep waiting
        (list (list c s (sync-state mapping (sync-memcpy (sub1 (sync-memcpy-n flag)))) #t))]
       [else
        (when verbose
          (printf "SYNC memcpy @ ~v --- ~v [~v]~n"
                  (@get-field c (mapping-program-counter mapping))
                  (regfile-pc (machine-registers s))
                  (get-current-instruction s (spec-environment spec))))
        (define-values (c1 s1) (sync-all-buffers c s mapping #:verbose verbose))
        (list (list c1 s1 (sync-state mapping #f) #t))])]
    [(and (sync-arithmetic? flag) (is-hardware-valid-instruction? c mapping))
     ;; sync registers, clear flag, and re-run sync (to do any other steps we might do)
     ;; spec side: find arithmetic instruction and execute it, because impl already has executed
     (define s1 (step1 (step-until s is-software-arithmetic? spec) spec))
     (cond
       [(halted? s1) (list (list c s1 #f #t))]
       [else
        (when verbose
          (printf "SYNC arithmetic @ ~v --- ~v [~v]~n"
                  (@get-field c (mapping-program-counter mapping))
                  (regfile-pc (machine-registers s1))
                  (get-current-instruction s1 (spec-environment spec))))
        (define-values (c1 s2) (sync-registers c s1 mapping #:verbose verbose))
        (sync c1 s2 (sync-state mapping #f) spec #:verbose verbose)])]
    [(and (sync-branch? flag) (> (sync-branch-n flag) 0))
     (list (list c s (sync-state mapping (sync-branch (sub1 (sync-branch-n flag)))) #t))]
    [(or (and (sync-branch? flag) (= (sync-branch-n flag) 0))
         (and (eqv? flag #f) (is-hardware-branch? c mapping) (= (mapping-branch-delay mapping) 0)))
     (define s1 (step-until s is-software-branch? spec))
     (cond
       [(halted? s1) (list (list c s1 #f #t))]
       [else
        (define conds (get-branch-cases s1 (spec-environment spec)))
        (cond
          [(> (length conds) 1)
           ;; register symbolic branch, deal with it later (or now, if triggered)
           (sync c s1 (sync-state mapping (sync-symbolic-branch)) spec #:verbose verbose)]
          [else
           (when verbose
             (printf "SYNC branch @ ~v --- ~v [~v]~n"
                     (@get-field c (mapping-program-counter mapping))
                     (regfile-pc (machine-registers s1))
                     (get-current-instruction s1 (spec-environment spec))))
           (define-values (c1 s2) (sync-registers c s1 mapping #:verbose verbose))
           (define-values (c2 s3) (sync-all-buffers c1 s2 mapping #:verbose verbose))
           (define s4 (step1 s3 spec))
           (list (list c2 s4 (sync-state mapping #f) #t))])])]
    [(is-hardware-entry-exit? c mapping)
     ;; step until the pallocframe/pfreeframe
     (define s1 (step-until s is-software-entry-exit? spec))
     (cond
       [(halted? s1) (list (list c s1 #f #t))]
       [else
        (when verbose
          (printf "SYNC entry/exit @ ~v --- ~v [~v]~n"
                  (@get-field c (mapping-program-counter mapping))
                  (regfile-pc (machine-registers s1))
                  (get-current-instruction s1 (spec-environment spec))))
        (define-values (c1 s2) (sync-registers c s1 mapping #:verbose verbose))
        (define-values (c2 s3) (sync-buffer-args c1 s2 mapping #:verbose verbose))
        (define s4 (step1 s3 spec))
        (list (list c2 s4 state #t))])]
    [(is-hardware-branch? c mapping)
     ;; delay > 1 at this point, just register to do this later
     (list
      (list c s (sync-state mapping (sync-branch (sub1 (mapping-branch-delay mapping)))) #t))]
    ;; have to check nop before arithmetic, because nop is arithmetic
    [(is-hardware-nop? c mapping)
     ;; step spec until it's past memcpy
     (define s1 (step1 (step-until s is-software-memcpy? spec) spec))
     (list
      (list c s1 (sync-state mapping (sync-memcpy #f)) #t))]
    [(is-hardware-arithmetic? c mapping)
     (define s1 (step-until s is-software-arithmetic? spec))
     (cond
       [(and (is-software-arithmetic-builtin-2? s1 spec) (eqv? flag #f))
        ;; don't sync at this hardware instruction, sync at the next one
        (list (list c s1 (sync-state mapping (sync-arithmetic-2)) #t))]
       [else
        ;; sync at next instruction, once this completes
        (list
         (list c s1 (sync-state mapping (sync-arithmetic)) #t))])]
    [else
     (list (list c s state #t))]))

;; synchronization

;; returns two values, a new c and a new s
(define (sync-registers c s mapping #:verbose [verbose #f] #:abstract [abstract #t])
  (when verbose
    (printf "sync-registers!~n"))
  (define impl-registers-name (mapping-registers mapping))
  (define spec-regs (regfile-iregs (machine-registers s)))
  (define impl-reg-updates (make-hash))
  (for ([i (in-range 1 32)])
    (define spec-v (vector-ref spec-regs i))
    (define impl-v (if (vector? impl-registers-name)
                       (@get-field c (vector-ref impl-registers-name i))
                       (vector-ref (@get-field c impl-registers-name) i)))
    (if (int32? spec-v)
        (cond
          [(and (equal? spec-v impl-v) (or (@concrete? spec-v) (@constant? spec-v)))
           (when verbose
             (printf "  x~a already equal, ~v~n" i spec-v))]
          [(equivalent? spec-v impl-v)
           (cond
             ;; should we try concretizing first?
             [(and abstract (@symbolic? spec-v))
              (define make-fresh (not (@constant? spec-v)))
              (define fresh (if make-fresh (@fresh-symbolic (format "x~a_abs" i) (@bitvector 32)) spec-v))
              (when verbose
                (printf "  x~a ~v -> ~a~v~n" i impl-v (if make-fresh "(fresh) " "") fresh))
              (define s* (machine (write-ireg (machine-registers s) (@bv i 5) fresh) (machine-memory s)))
              (set! s s*)
              (hash-set! impl-reg-updates i fresh)]
             [else
              (when verbose
                (printf "  x~a ~v -> ~v~n" i impl-v spec-v))
              (hash-set! impl-reg-updates i spec-v)])]
          [else
           (when verbose
             (printf "  x~a impl ~v != spec ~v~n" i impl-v spec-v))])
        (when verbose (printf "  x~a not int~n" i))))
  (unless (hash-empty? impl-reg-updates)
    (cond
      [(vector? impl-registers-name)
       (set! c (@update-fields c (for/list ([(i v) (in-hash impl-reg-updates)])
                                   (cons (vector-ref impl-registers-name i) v))))]
      [else
       (define impl-regs (list->vector (vector->list (@get-field c impl-registers-name))))
       (for ([(i v) (in-hash impl-reg-updates)])
         (vector-set! impl-regs i v))
       (set! c (@update-field c impl-registers-name (vector->immutable-vector impl-regs)))]))
  (values c s))

;; for arguments that are pointers, sync up buffers
(define (sync-buffer-args c s mapping #:verbose [verbose #f] #:abstract [abstract #t])
  (when verbose
    (printf "sync-buffer-args!~n"))
  (sync-buffers c s mapping (range 10 17) #:verbose verbose #:abstract abstract))

(define (sync-all-buffers c s mapping #:verbose [verbose #f] #:abstract [abstract #t])
  (when verbose
    (printf "sync-all-buffers!~n"))
  (sync-buffers c s mapping (range 2 31) #:verbose verbose #:abstract abstract))

(define (sync-current-stack-frame c s mapping #:verbose [verbose #f] #:abstract [abstract #t])
  (when verbose
    (printf "sync-current-stack-frame!~n"))
  (sync-buffers c s mapping (list 2) #:verbose verbose #:abstract abstract))

;; returns two values, a new c and a new s
(define (sync-buffers c s mapping iregs #:verbose [verbose #f] #:abstract [abstract #t])
  (define impl-registers-name (mapping-registers mapping))
  (define ram (@get-field c (mapping-ram mapping)))
  ;; updates in terms of blocks, mapping from addr%4 -> list of (3, 2, 1, 0)
  (define ram-updates (make-hash))
  (define (update-ram! addr byte)
    (let* ([word (quotient addr 4)]
           [offset (remainder addr 4)])
      (cond
        [(hash-has-key? ram-updates word)
         (define v (hash-ref ram-updates word))
         (hash-set! ram-updates word (list-set v (- 3 offset) byte))]
        [else
         (define v (vector-ref ram word))
         (hash-set! ram-updates word
                    (list
                     (@extract 31 24 v)
                     (@extract 23 16 v)
                     (@extract 15 8 v)
                     (@extract 7 0 v)))
         (update-ram! addr byte)])))
  (define mem (machine-memory s))
  ;; mapping from abstract memory block number to concrete base
  (define blocks-to-sync (make-hash))
  (for ([i iregs])
    (define impl-ptr (if (vector? impl-registers-name)
                         (@get-field c (vector-ref impl-registers-name i))
                         (vector-ref (@get-field c impl-registers-name) i)))
    (define spec-ptr (vector-ref (regfile-iregs (machine-registers s)) i))
    (when (and (pointer? spec-ptr)
               (valid-pointer? mem (pointer-block spec-ptr) (@bitvector->natural (pointer-offset spec-ptr)))
               ((mapping-ram-pointer? mapping) impl-ptr))
      (when verbose
        (printf "  x~a: ~v -> ~v~n" i spec-ptr impl-ptr))
      (define block (pointer-block spec-ptr))
      (define impl-base (@bvsub impl-ptr (pointer-offset spec-ptr)))
      (hash-set! blocks-to-sync block impl-base)))

  (for ([(block impl-ptr) blocks-to-sync])
    (define alloc-size (block-size mem block))
    (when verbose
      (printf "  syncing block ~v [sz ~a], impl ~v~n" block alloc-size impl-ptr))
    (define spec-bytes (loadbytes mem block 0 alloc-size))
    (for ([i (in-range alloc-size)]
          [spec-byte spec-bytes])
      (when (byte? spec-byte)
        (define impl-addr (+ (@bitvector->natural (@bvsub impl-ptr (@bv #x20000000 32))) i))
        (define impl-byte (read ram impl-addr))
        (cond
          [(not (byte? spec-byte))
           (void)]
          [(and (equal? impl-byte spec-byte) (or (@concrete? spec-byte) (@constant? spec-byte)))
           (void)]
          [(equivalent? impl-byte spec-byte)
           (cond
             [(and abstract (@symbolic? spec-byte))
              (define make-fresh (not (@constant? spec-byte)))
              (define fresh (if make-fresh (@fresh-symbolic (format "ram[~a]_abs" impl-addr) (@bitvector 8)) spec-byte))
              (when verbose
                (printf "  [~a] ~v -> ~a~v~n" i impl-byte (if make-fresh "(fresh) " "") fresh))
              (update-ram! impl-addr fresh)
              (set! mem (storebytes mem block i (list fresh)))]
             [else
              (when verbose
                (printf "    [~a] ~v -> ~v~n" i impl-byte spec-byte))
              (update-ram! impl-addr spec-byte)])]
          [else
           (void)
           (printf "    [~a] impl ~v != spec ~v~n" i impl-byte spec-byte)]))))
  (unless (hash-empty? ram-updates)
    ;; copy RAM, mutable
    (define ram-copy (list->vector (vector->list ram)))
    (for ([(i v) (in-hash ram-updates)])
      (vector-set! ram-copy i (@apply @concat v)))
    (set! c (@update-field c (mapping-ram mapping) (vector->immutable-vector ram-copy)))
    (set! s (machine (machine-registers s) mem)))
  (values c s))

(define (read mem addr)
  (define ofs (remainder addr 4))
  (@extract (sub1 (* 8 (add1 ofs))) (* 8 ofs) (vector-ref mem (quotient addr 4))))

(define (write! mem addr byte)
  (let* ([word (quotient addr 4)]
         [offset (remainder addr 4)]
         [old (vector-ref mem word)])
    (vector-set! mem word
                 (cond
                   [(equal? offset 0) (@concat (@extract 31 8 old) byte)]
                   [(equal? offset 1) (@concat (@extract 31 16 old) byte (@extract 7 0 old))]
                   [(equal? offset 2) (@concat (@extract 31 24 old) byte (@extract 15 0 old))]
                   [(equal? offset 3) (@concat byte (@extract 23 0 old))]))))

;; stepping spec

(define (step-until s pred spec)
  (cond
    [(halted? s) s]
    [(pred s spec) s]
    [else (step-until (step1 s spec) pred spec)]))

(define (step1 s spec)
  (if (halted? s) s (step s (spec-environment spec))))

;; lining up spec and impl

(define (is-hardware-valid-instruction? c mapping)
  (define instr ((mapping-instruction mapping) c))
  instr)

(define (is-software-entry-exit? s spec)
  (let* ([instr (get-current-instruction s (spec-environment spec))]
         [is-entry-or-exit (or (Pallocframe? instr) (Pfreeframe? instr))])
    is-entry-or-exit))

(define (is-hardware-entry-exit? c mapping)
  (define instr ((mapping-instruction mapping) c))
  (and instr
       (let* ([opcode (@extract 6 0 instr)]
              [rd (@extract 11 7 instr)]
              [funct3 (@extract 14 12 instr)]
              [rs1 (@extract 19 15 instr)]
              [is-addi-sp-sp (and (@bveq opcode (@bv #b0010011 7))
                                  (@bveq funct3 (@bv #b000 3))
                                  (@bveq rd (@bv 2 5))
                                  (@bveq rs1 (@bv 2 5)))])
         is-addi-sp-sp)))

(define (is-software-branch? s spec)
  (let* ([instr (get-current-instruction s (spec-environment spec))]
         [is-branch (or (Pbeqw? instr)
                        (Pbgeuw? instr)
                        (Pbgew? instr)
                        (Pbltuw? instr)
                        (Pbltw? instr)
                        (Pbnew? instr))])
    is-branch))

(define (is-hardware-branch? c mapping)
  (define instr ((mapping-instruction mapping) c))
  (and instr
       (let* ([opcode (@extract 6 0 instr)]
              [is-branch (@bveq opcode (@bv #b1100011 7))])
         is-branch)))

;; only sync certain instructions, e.g., don't sync addiw but sync andiw
(define (is-hardware-arithmetic? c mapping)
  (define instr ((mapping-instruction mapping) c))
  (and instr
       (let* ([opcode (@extract 6 0 instr)]
              [funct7 (@extract 31 25 instr)]
              [funct3 (@extract 14 12 instr)]
              [is-rv32m (and (@bveq opcode (@bv #b0110011 7)) (@bveq funct7 (@bv #b0000001 7)))]
              [is-bitwise (and (or (@bveq opcode (@bv #b0010011 7)) ; register-immediate
                                   (@bveq opcode (@bv #b0110011 7))) ; register-register
                               (or (@bveq funct3 (@bv #b100 3)) ; xor[i]
                                   (@bveq funct3 (@bv #b110 3)); or[i]
                                   (@bveq funct3 (@bv #b111 3)) ; and[i]
                                   (@bveq funct3 (@bv #b001 3)) ; sll[i]
                                   (@bveq funct3 (@bv #b101 3))))]) ; sr{l,a}[i]
         (or is-rv32m is-bitwise))))

(define (is-software-arithmetic-builtin-2? s spec)
  (let* ([instr (get-current-instruction s (spec-environment spec))])
    (and (Pbuiltin? instr) (equal? (Pbuiltin-ef instr) (EF_builtin (BI_mull))))))

(define (is-software-arithmetic? s spec)
  (let* ([instr (get-current-instruction s (spec-environment spec))]
         [is-arith (or (and (Pbuiltin? instr) (equal? (Pbuiltin-ef instr) (EF_builtin (BI_mull))))
                       (Pmulhuw? instr)
                       (Pmulhw? instr)
                       (Pmulw? instr)
                       (Pdivuw? instr)
                       (Pdivw? instr)
                       (Premuw? instr)
                       (Premw? instr)
                       (Pxoriw? instr)
                       (Pxorw? instr)
                       (Poriw? instr)
                       (Porw? instr)
                       (Pandiw? instr)
                       (Pandw? instr)
                       (Pslliw? instr)
                       (Psllw? instr)
                       (Psraiw? instr)
                       (Psraw? instr)
                       (Psrliw? instr)
                       (Psrlw? instr))])
    is-arith))

(define (is-hardware-nop? c mapping)
  (define instr ((mapping-instruction mapping) c))
  (and instr
       (let* ([opcode (@extract 6 0 instr)]
              [is-nop (@bveq instr (@bv #x00000013 32))])
         is-nop)))

(define (is-software-memcpy? s spec)
  (let* ([instr (get-current-instruction s (spec-environment spec))]
         [is-memcpy (and (Pbuiltin? instr) (EF_memcpy? (Pbuiltin-ef instr)))])
    is-memcpy))

;; equivalence checking

(define CACHE-SIZE 256)
(define equivalence-cache (list))
(define hits 0)
(define misses 0)
(define (equivalent? a b)
  (define is-eq (@equal? a b))
  (cond
    [(eqv? is-eq #t) #t]
    [(eqv? is-eq #f) #f]
    [else
     #;(printf "  issuing solver query...~n")
     (define cached-answer
       (let loop ([i 1]
                  [remaining equivalence-cache]
                  [checked '()])
         (cond
           [(empty? remaining)
            #;(set! misses (add1 misses))
            #;(when (> (+ hits misses) 0)
                (printf "cache miss, loop iter ~a, hit rate ~a / ~a = ~v%~n" i hits (+ hits misses) (truncate (* (/ hits (+ hits misses)) 100))))
            (void)] ; represents cache miss; (or #f (void)) -> (void), so this does the right thing
           [(@equivalent-up-to-renaming is-eq (car (first remaining)))
            (set! equivalence-cache (cons (first remaining) (append (reverse checked) (rest remaining))))
            #;(set! hits (add1 hits))
            #;(when (> (+ hits misses) 0)
                (printf "cache loop iter ~a, hit rate ~a / ~a = ~v%~n" i hits (+ hits misses) (truncate (* (/ hits (+ hits misses)) 100))))
            (cdr (first remaining))]
           [else
            ;; keep looking
            (loop (add1 i) (rest remaining) (cons (first remaining) checked))])))
     (cond
       [(not (void? cached-answer)) cached-answer]
       [else
        (define solver-proved-equivalence (@unsat? (@verify (@assert is-eq))))
        ;; update cache, store yes/no answers (we treat unknown as no, because we can't do anything in that case)
        (set! equivalence-cache (cons (cons is-eq solver-proved-equivalence)
                                      (if (> (length equivalence-cache) CACHE-SIZE)
                                          (take equivalence-cache CACHE-SIZE)
                                          equivalence-cache)))
        solver-proved-equivalence])]))
