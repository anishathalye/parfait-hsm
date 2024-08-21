#lang knox/correctness

#:spec "../spec/spec.rkt"
#:circuit "circuit.rkt"
#:driver "../spec/driver.rkt"
#:R R
#:hints hints
#:only 'handle
#|
#:override-args (list
                 (fresh-symbolic 'cmd1 (bitvector 8))
                 (fresh-symbolic 'cmd2 (bitvector 8))
                 (fresh-symbolic 'cmd3 (bitvector 8))
                 (fresh-symbolic 'cmd4 (bitvector 8)))
|#
#|
#:override-args (list (bv #x02 8) (bv #x5 8) (bv #x6 8) (bv #x7 8))
#:override-f1 (list (bv #x1 8) (bv #x2 8) (bv #x3 8) (bv #x4 8)
                    (bv #x5 8) (bv #x6 8) (bv #x7 8) (bv #x8 8)
                    (bv #x9 8) (bv #xa 8) (bv #xb 8) (bv #xc 8)
                    (bv #xd 8) (bv #xe 8) (bv #xf 8) (bv #x10 8)
                    (bv #x11 8) (bv #x12 8) (bv #x13 8) (bv #x14 8))
|#
#:without-yield #t
#:verbose #t

(require
 "shared.rkt"
 racket/match
 knox/correctness/hint
 rosette/safe
 yosys/meta
 yosys/parameters
 knox/circuit
 parfait/sync
 (prefix-in parfait: parfait/spec)
 (prefix-in ! racket/base)
 (only-in rosette/base/core/polymorphic ite)
 (only-in racket/list range)
 (only-in racket/string string-contains?)
 rosutil)

(define (hints method c1 f1)
  (common-hintdb c1 f1))

(define (common-hintdb c1 f1)
  (make-hintdb
   [concretize-init
    (concretize! (lens 'circuit (field-filter/or "pwrmgr_state" "rom")) #:use-pc #t)]
   [concretize-uart
    ;; need to use pc here because we want to concretize slot in case split
    (concretize! (lens 'circuit (field-filter/or 'wrapper.soc.uart.simpleuart.recv_buf_data 'wrapper.soc.uart.simpleuart.recv_pattern)) #:use-pc #t)]
   [maybe-split-read
    (tactic
     (define ckt (lens-view (lens 'interpreter 'globals 'circuit) (get-state)))
     ;; at the slli just after the snez
     (when (and (equal? (get-field ckt 'wrapper.soc.cpu.u_ibex_core.if_stage_i.pc_id_o) (bv #x258 32)))
       (let ([fram0 (lens-view (lens 'wrapper.soc.fram.fram 0) ckt)])
         (displayln "case split on active = 0 or active = 1")
         (case-split! (list (bvzero? fram0) (! (bvzero? fram0))))
         (concretize! (lens 'circuit '|wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[6].rf_reg_q|) #:use-pc #t))))]
   [maybe-merge-after-read
    (tactic
     (define ckt (lens-view (lens 'interpreter 'globals 'circuit) (get-state)))
     ;; add the addi just before ret
     (when (and (equal? (get-field ckt 'wrapper.soc.cpu.u_ibex_core.if_stage_i.pc_id_o) (bv #x278 32)))
       (displayln "merging after read")
       (define (spec-word i)
         (concat
          (list-ref f1 (+ (* i 4) 3))
          (list-ref f1 (+ (* i 4) 2))
          (list-ref f1 (+ (* i 4) 1))
          (list-ref f1 (+ (* i 4) 0))))
       ;; state gets laid out after command in ram, need to find it in data section
       ;; take address, subtract ram offset, and divide by 4, e.g., 0x20000830 -> 524
       (define state-base 897)
       (replace! (lens 'circuit 'wrapper.soc.ram.ram (map (lambda (i) (+ i state-base)) (range 5)))
                 (join (list (spec-word 0) (spec-word 1) (spec-word 2) (spec-word 3) (spec-word 4)))
                 #:use-pc #t)
       ;; overapproximate caller-saved registers; no return value

       (overapproximate! (lens 'circuit (for/list ([i (list 5 6 7 10 11 12 13 14 15 16 17 28 29 30 31)])
                                          (format "wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[~a].rf_reg_q" i))))
       (overapproximate-pc! #t) ;; don't even need R at this point, we've loaded the state into RAM
       #;(printf "cpuregs: ~v~n" (lens-view (lens 'interpreter 'globals 'circuit 'wrapper.soc.cpu.cpuregs) (get-state)))
       (merge!)))]
   [maybe-split-write
    (tactic
     (define ckt (lens-view (lens 'interpreter 'globals 'circuit) (get-state)))
     ;; at the slli just after the snez
     (when (and (equal? (get-field ckt 'wrapper.soc.cpu.u_ibex_core.if_stage_i.pc_id_o) (bv #x2dc 32)))
       (let ([fram0 (lens-view (lens 'wrapper.soc.fram.fram 0) ckt)])
         (displayln "case split on active = 0 or active = 1")
         (case-split! (list (bvzero? fram0) (! (bvzero? fram0))))
         (concretize! (lens 'circuit '|wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[16].rf_reg_q|) #:use-pc #t))))]
   ;; merging the write isn't tricky because we don't do sophisticated
   ;; transformations to the spec state (only the output), so we can just replace the fram
   ;; state with the spec state again (and the replace! is fast)
   [maybe-merge-after-write
    (tactic
     (define ckt (lens-view (lens 'interpreter 'globals 'circuit) (get-state)))
     ;; add the addi just before ret
     (when (and (equal? (get-field ckt 'wrapper.soc.cpu.u_ibex_core.if_stage_i.pc_id_o) (bv #x318 32)))
       (displayln "merging after write")
       (spec-finish!)
       (define f2 ((parfait:spec-get-state spec) (lens-view (lens 'spec-machine) (get-state))))
       (define (spec-word i)
         (concat
          (list-ref f2 (+ (* i 4) 3))
          (list-ref f2 (+ (* i 4) 2))
          (list-ref f2 (+ (* i 4) 1))
          (list-ref f2 (+ (* i 4) 0))))
       (define fram1 (get-field c1 'wrapper.soc.fram.fram))
       ;; the following isn't necessary because our C code does
       ;; pmem->active0 = !pmem->active0, so it makes the same symbolic
       ;; expression in both branches (re-reads that word)
       #;(replace! (lens 'circuit 'wrapper.soc.fram.fram 0) (if active0 (bv 1 32) (bv 0 32)))
       (define active1 (! (bvzero? (lens-view (lens 'wrapper.soc.fram.fram 0) ckt))))
       (replace! (lens 'circuit 'wrapper.soc.fram.fram (list 2 3 4 5 6 7 8 9 10 11))
                 (join (list
                        (if active1 (vector-ref fram1 2) (spec-word 0))
                        (if active1 (vector-ref fram1 3) (spec-word 1))
                        (if active1 (vector-ref fram1 4) (spec-word 2))
                        (if active1 (vector-ref fram1 5) (spec-word 3))
                        (if active1 (vector-ref fram1 6) (spec-word 4))

                        (if active1 (spec-word 0) (vector-ref fram1 7))
                        (if active1 (spec-word 1) (vector-ref fram1 8))
                        (if active1 (spec-word 2) (vector-ref fram1 9))
                        (if active1 (spec-word 3) (vector-ref fram1 10))
                        (if active1 (spec-word 4) (vector-ref fram1 11))
                        ))
                 #:use-pc #t)
       ;; overapproximate caller-saved registers; no return value
       (overapproximate! (lens 'circuit (for/list ([i (list 5 6 7 10 11 12 13 14 15 16 17 28 29 30 31)])
                                          (format "wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[~a].rf_reg_q" i))))
       (overapproximate-pc! #t) ;; don't even need R at this point, we've loaded the state into RAM
       #;(printf "cpuregs: ~v~n" (lens-view (lens 'interpreter 'globals 'circuit 'wrapper.soc.cpu.cpuregs) (get-state)))
       (merge!)))]
   [maybe-concretize-cpu
    (tactic
     (define ckt (lens-view (lens 'interpreter 'globals 'circuit) (get-state)))
     (when (symbolic? (get-field ckt 'wrapper.soc.cpu.u_ibex_core.if_stage_i.pc_id_o))
       (concretize! (lens 'circuit (field-filter/and "soc.cpu." (field-filter/not "register_file"))))))]
   [overapproximate-uart (overapproximate! (lens 'circuit (field-filter/or "send_divcnt")))]
   [overapproximate-boot (overapproximate! (lens 'circuit (field-filter/or "count_cycle" "count_instr" "send_divcnt")))]
   [overapproximate-send-merge (overapproximate! (lens 'circuit (field-filter/or "count_cycle" "count_instr" "send_divcnt")))]
   [overapproximate-recv-merge (overapproximate! (lens 'circuit (field-filter/or "count_cycle" "count_instr")))]
   [debug (tactic
           (define ckt (lens-view (lens 'interpreter 'globals 'circuit) (get-state)))
           #;(parameterize ([print-filter "soc.cpu."])
             (println ckt))
           (printf "pc: ~v~n" (get-field ckt 'wrapper.soc.cpu.u_ibex_core.if_stage_i.pc_id_o)))]
   [sync
    (tactic
     ;; begin syncing, if necessary
     (define ckt (lens-view (lens 'interpreter 'globals 'circuit) (get-state)))
     (when (and (equal? (get-field ckt 'wrapper.soc.cpu.u_ibex_core.if_stage_i.pc_id_o) (bv #x618 32)))
       (displayln "begin syncing")
       (begin-sync! ibex-mapping))
     ;; call auto-sync
     (auto-sync!))]))
