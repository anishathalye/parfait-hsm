#lang knox/security

#:spec "../spec/spec.rkt"
#:circuit "circuit.rkt"
#:emulator "emulator.rkt"
#:R R
#:R* R*
;; #:skip-final-check #t

(define STATE-LENGTH 5) ; 32-bit words
(define COMMAND-LENGTH 33) ; bytes
(define RESPONSE-LENGTH 33) ; bytes
(define state-base 897)

(require
 "shared.rkt"
 rosette/safe
 rosutil
 parfait/sync
 (prefix-in racket/ racket/base)
 (only-in racket/list range))

(define (cases*! preds)
  (cases! (append preds (list (not (apply || preds))))))

(define (show-pcs)
  (define t (set-term (current)))
  (define c (lens-view (lens 'circuit 'wrapper.soc.cpu.u_ibex_core.if_stage_i.pc_id_o) t))
  (define s (lens-view (lens 'emulator 'auxiliary 'wrapper.soc.cpu.u_ibex_core.if_stage_i.pc_id_o) t))
  (printf "ckt: ~v emu: ~v\n" c s))

(define (step-n! n)
  (unless (zero? n)
    (step!)
    (printf "step ~a, " n)
    (show-pcs)
    (step-n! (sub1 n))))

(define (poweroff term)
  (racket/equal? (lens-view (lens 'circuit 'wrapper.pwrmgr_state) term) (bv #b01 2)))

(define ((pc-is pc) term)
  (racket/equal? (lens-view (lens 'circuit 'wrapper.soc.cpu.u_ibex_core.if_stage_i.pc_id_o) term) pc))

(define (symbolic-pc term)
  (symbolic? (lens-view (lens 'circuit 'wrapper.soc.cpu.u_ibex_core.if_stage_i.pc_id_o) term)))

;; proceed to where we're about to read from UART
(define (step-until! circuit-pred [sync-recv #t])
  (let loop ([i 0])
    (unless (circuit-pred (set-term (current)))
      (step!)
      (when sync-recv
        (sync-overapprox-uart-recv!))
      (printf "step ~a, " i)
      (show-pcs)
      (loop (add1 i)))))

;; insight: we actually don't care what's going on inside the UART,
;; just that the value read by the circuit and the emulated circuit in
;; uart_read is the same

(define (match-abstract! l [name #f])
  (define t (remember+! (list (lens 'circuit l) (lens 'emulator 'auxiliary l)) name))
  (clear! t)
  t)

;; the kind of annoying thing is that once we overapproximate what's
;; going on in the recieve side of the uart, it needs to stay
;; overapproximated forever, it never becomes quiescent again
(define (sync-overapprox-uart-recv!)
  (for ([field (list 'wrapper.soc.uart.simpleuart.recv_buf_valid
                     'wrapper.soc.uart.simpleuart.recv_buf_data
                     'wrapper.soc.uart.simpleuart.recv_divcnt
                     'wrapper.soc.uart.simpleuart.recv_pattern
                     'wrapper.soc.uart.simpleuart.recv_state)])
    (match-abstract! field field)))

(define (concretize-branch!)
  (define branch-related (list
                          "branch_set_raw_q"
                          "id_fsm_q"
                          "instr_addr_q"
                          "prefetch_buffer_i.fifo_i.rdata_q"
                          "prefetch_buffer_i.fifo_i.valid_q"
                          "_id_o"))
  (concretize! (lens (list (lens 'circuit branch-related)
                                   (lens 'emulator 'auxiliary branch-related)))))

;; proceed to the UART read; returns var
(define (step-past-uart-read! [read-name #f])
  (define (overapproximate-uart-read!)
    (overapproximate!
     (lens (list (lens 'circuit (list 'wrapper.soc.uart.simpleuart.send_divcnt
                                      'wrapper.soc.cpu.u_ibex_core.cs_registers_i.mcycle_counter_i.counter_q
                                      'wrapper.soc.cpu.u_ibex_core.cs_registers_i.minstret_counter_i.counter_q
                                      '|wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[5].rf_reg_q|
                                      '|wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[31].rf_reg_q|))
                 (lens 'emulator 'auxiliary (list 'wrapper.soc.uart.simpleuart.send_divcnt
                                                  'wrapper.soc.cpu.u_ibex_core.cs_registers_i.mcycle_counter_i.counter_q
                                                  'wrapper.soc.cpu.u_ibex_core.cs_registers_i.minstret_counter_i.counter_q
                                                  '|wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[5].rf_reg_q|
                                                  '|wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[31].rf_reg_q|))))))

  (step-until! (pc-is (bv #x00000130 32)) #t) ; li t6, -1
  (define ready1 (match-abstract! (lens '|wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[5].rf_reg_q|) #f))
  (define old-pred (set-predicate (current)))
  (cases*! (list (equal? ready1 (bv -1 32))))
  (step-until! symbolic-pc)
  (concretize-branch!)
  (step-until! (pc-is (bv #x0000012c 32)) #t) ; lw t0, ...
  (step-n! 1)
  ;; subsumption point, after one loop iteration
  (overapproximate-uart-read!)
  (sync-overapprox-uart-recv!)
  (history! #t)
  (define pre-read (length (visited)))
  (step-until! (pc-is (bv #x00000130 32)) #t) ; li t6, -1
  (define ready2 (match-abstract! (lens '|wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[5].rf_reg_q|) #f))
  (cases*! (list (equal? ready2 (bv -1 32))))
  (step-until! symbolic-pc)
  (concretize-branch!)
  (step-until! (pc-is (bv #x0000012c 32)) #t) ; lw t0, ...
  (step-n! 1)
  (sync-overapprox-uart-recv!)
  (subsumed! pre-read)
  ;; now, sync two branches that both did the read
  (step-until! symbolic-pc)
  (concretize-branch!)
  (step-until! (pc-is (bv #x144 32))) ; ret
  (overapproximate-uart-read!)
  (sync-overapprox-uart-recv!)
  (overapproximate-predicate! old-pred)
  (define post-read (length (visited)))
  (step-n! 1)
  (switch-goal! 1)
  (step-until! symbolic-pc)
  (concretize-branch!)
  (step-until! (pc-is (bv #x144 32))) ; ret
  (sync-overapprox-uart-recv!)
  (overapproximate-predicate! old-pred)
  (subsumed! post-read)
  (history! #f))

(define (step-past-uart-write!)
  (define (overapproximate-uart-write!)
    (overapproximate!
     (lens (list (lens 'circuit (list
                                 'wrapper.soc.cpu.u_ibex_core.cs_registers_i.mcycle_counter_i.counter_q
                                 'wrapper.soc.cpu.u_ibex_core.cs_registers_i.minstret_counter_i.counter_q))
                 (lens 'emulator 'auxiliary (list
                                             'wrapper.soc.cpu.u_ibex_core.cs_registers_i.mcycle_counter_i.counter_q
                                             'wrapper.soc.cpu.u_ibex_core.cs_registers_i.minstret_counter_i.counter_q))))))
  (step-until! (pc-is (bv #x158 32))) ; lw t1, ...
  (step-n! 2)

  (define cts-read1 (match-abstract! (lens '|wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[6].rf_reg_q|) 'cts-read))
  (define old-pred (set-predicate (current)))
  (cases*! (list (not (bvzero? cts-read1))))
  ;; no cts case, should be able to get back to start of loop
  (step-until! symbolic-pc)
  (concretize-branch!)
  (step-until! (pc-is (bv #x158 32))) ; lw t1, ...
  ;; subsumption point, after one loop iteration
  (overapproximate-uart-write!)
  (sync-overapprox-uart-recv!)
  (history! #t)
  (define pre-write (length (visited)))
  (step-until! (pc-is (bv #x15c 32))) ; bnez ...
  (define cts-read2 (match-abstract! (lens '|wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[6].rf_reg_q|) 'cts-read))
  (cases*! (list (not (bvzero? cts-read2))))
  (step-until! symbolic-pc)
  (concretize-branch!)
  (step-until! (pc-is (bv #x158 32))) ; lw t1, ...
  (subsumed! pre-write)
  ;; now, sync two branches that both got past the cts
  (step-until! symbolic-pc)
  (concretize-branch!)
  (step-until! (pc-is (bv #x164 32))) ; lw a1, ...
  (overapproximate-uart-write!)
  (sync-overapprox-uart-recv!)
  (overapproximate-predicate! old-pred)
  (define post-write (length (visited)))
  (step-n! 1)
  (switch-goal! 1)
  (step-until! symbolic-pc)
  (concretize-branch!)
  (step-until! (pc-is (bv #x164 32))) ; lw a1, ...
  (sync-overapprox-uart-recv!)
  (overapproximate-predicate! old-pred)
  (subsumed! post-write)
  (step-until! (pc-is (bv #x178 32))) ; ret
  (overapproximate!
   (lens (list (lens 'circuit 'wrapper.soc.uart.simpleuart.send_divcnt)
               (lens 'emulator 'auxiliary 'wrapper.soc.uart.simpleuart.send_divcnt))))
  (history! #f))

(define (step-to-start-of-main!)
  (concretize!
        (lens 'circuit (list 'wrapper.soc.rom.rom
                             'wrapper.pwrmgr_state
                             'resetn
                             "$auto$proc_rom")))

  ;; we want to get rid of the predicate, to simplify subsumption checks
  ;; so we make use of replace and overapproximate-predicate
  ;;
  ;; compute spec state based on circuit state
  (replace! (lens 'emulator 'oracle) (AbsF (lens-view (lens 'term 'circuit) (current))))
  (overapproximate-predicate! #t)

  ;; if CTS was not asserted, then the circuit is still in the "embryo"
  ;; state
  (prepare!) ; prepare first, so we can case-split on inputs _before_ stepping

  #;(step!)
  (cases*! (list (lens-view (lens 'term 'circuit 'cts) (current))))
  (concretize! (lens (list (lens 'circuit (list 'cts))
                                   (lens 'emulator 'auxiliary (list 'cts)))))
  ;; we case-split and concretize first before stepping so that we don't
  ;; get terms like (if cts a b), where the two branches are symbolic
  ;; variables, but this can't be optimized by concretize (we'd need a "simplify" tactic)

  (define cpu-free-running-regs
    (field-filter/or
     "cpu.alu_out_q"
     "cpu.decoded_imm"
     "cpu.instr_"
     "cpu.is_jalr"
     "cpu.is_lbu"
     "cpu.is_lui"
     "cpu.is_sll"
     "cpu.is_slti"
     "cpu.mem_rdata_q"))

  (step!)
  (history! #f)

  (overapproximate!
        (lens (list (lens 'circuit cpu-free-running-regs)
                    (lens 'emulator 'auxiliary cpu-free-running-regs))))
  (subsumed! 0)

  ;; "main thread", where CPU has just been reset. we need to concretize
  ;; CTS first so things don't blow up
  (concretize! (lens (list (lens 'circuit (list 'cts))
                                   (lens 'emulator 'auxiliary (list 'cts)))))
  (overapproximate-predicate! #t) ; don't need to remember cts anymore

  ;; proceed to uart init
  (step-until! (pc-is (bv #x0000010c 32)) #f) ; sw a1, ...

  ;; proceed to right before reading the command
  (step-until! (pc-is (bv #x204 32)))) ; jal uart_read

(define (do-read-command!)
  (for ([i (range COMMAND-LENGTH)])
    (step-past-uart-read!)))

(define (do-write-response!)
  (for ([i (range RESPONSE-LENGTH)])
    (step-past-uart-write!)))

(define (do-read-state!)
  ;; going to do case analysis on which region is active, step just past the snez
  (step-until! (pc-is (bv #x258 32))) ; sll a1, ...
  (define state (lens-view (lens 'emulator 'oracle) (set-term (current))))
  (define fram (lens-view (lens 'circuit 'wrapper.soc.fram.fram) (set-term (current))))
  (define fram0 (vector-ref fram 0))
  (define active0 (bvzero? (lens-view (lens 'circuit 'wrapper.soc.fram.fram 0) (set-term (current)))))
  (cases! (list active0 (! active0)))

  (define (align-case!)
    (concretize! (lens 'circuit '|wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[6].rf_reg_q|))
    (step-until! (pc-is (bv #x280 32))) ; ret
    (for ([i (range STATE-LENGTH)])
      (replace! (lens 'circuit 'wrapper.soc.ram.ram (+ state-base i))
                (if active0
                    (vector-ref fram (+ 2 i))
                    (vector-ref fram (+ 2 STATE-LENGTH i)))))
    (overapproximate! (lens 'circuit
                            (for/list ([i (list 5 6 7 10 11 12 13 14 15 16 17 28 29 30 31)])
                              (string->symbol (format "wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[~a].rf_reg_q" i)))))
    (overapproximate-predicate! #t))

  (align-case!)
  (history! #t)
  (define ref (length (visited)))
  (step!)
  ;; eliminate other branch
  (switch-goal! 1)
  (align-case!)
  (subsumed! ref)
  (history! #f))

(define (do-handle!)
  (step-until! (pc-is (bv #x618 32))) ;; start of impl_main
  (begin-sync! ibex-mapping)
  ;; get past all the symbolic branches, and then enable abstraction
  (define (ready? t)
    (define emu-ckt (lens-view (lens 'emulator 'auxiliary) (set-term t)))
    (and (not ((mapping-symbolic-branch? ibex-mapping) emu-ckt))
         (bvuge (get-field (pairing-circuit (set-term t)) 'wrapper.soc.cpu.u_ibex_core.if_stage_i.pc_id_o) (bv #x63c 32))))
  (define (all-ready?)
    (for/and ([t (next)]) (ready? t)))
  (define (maybe-concretize!)
    (define emu-ckt (lens-view (lens 'emulator 'auxiliary) (set-term (current))))
    (when ((mapping-symbolic-branch? ibex-mapping) emu-ckt)
      (concretize! (lens 'emulator 'auxiliary (mapping-cpu-lens ibex-mapping))
                   #:piecewise #t)
      (overapproximate-predicate! #t)))
  (let loop ()
    (unless (all-ready?)
      (let loop-until-done ([i 0])
        (maybe-concretize!)
        (sync-overapprox-uart-recv!)
        (printf "step ~a, " i)
        (show-pcs)
        (unless (ready? (current))
          (step!)
          (loop-until-done (add1 i)))
        ;; current is ready, move it
        (switch-goal! (sub1 (length (next)))))
      (loop)))
  (sync-abstract! #t))

(define (do-write-state!)
  (step-until! (pc-is (bv #x2dc 32))) ; li a5, 1
  (define state (lens-view (lens 'emulator 'oracle) (set-term (current))))
  ;; load fram before the commit point
  (define fram (lens-view (lens 'circuit 'wrapper.soc.fram.fram) (set-term (current))))
  (define fram0 (vector-ref fram 0))
  (define ram (lens-view (lens 'circuit 'wrapper.soc.ram.ram) (set-term (current))))
  (define active0 (bvzero? (lens-view (lens 'circuit 'wrapper.soc.fram.fram 0) (set-term (current)))))
  (cases! (list active0 (! active0)))

  (define (align-case!)
    (concretize! (lens 'circuit '|wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[16].rf_reg_q|))
    (step-until! (pc-is (bv #x320 32))) ; ret
    ;; do alignment
    (for ([i (range STATE-LENGTH)])
      (replace! (lens 'circuit 'wrapper.soc.fram.fram (+ 2 i))
                (if active0 (vector-ref fram (+ 2 i)) (vector-ref ram (+ state-base i)))))
    (for ([i (range STATE-LENGTH)])
      (replace! (lens 'circuit 'wrapper.soc.fram.fram (+ 2 STATE-LENGTH i))
                (if active0 (vector-ref ram (+ state-base i)) (vector-ref fram (+ 2 STATE-LENGTH i)))))
    (overapproximate! (lens 'circuit
                            (for/list ([i (list 5 6 7 10 11 12 13 14 15 16 17 28 29 30 31)])
                              (string->symbol (format "wrapper.soc.cpu.gen_regfile_ff.register_file_i.g_rf_flops[~a].rf_reg_q" i)))))
    (overapproximate-predicate! #t)
    (sync-overapprox-uart-recv!))

  (align-case!)
  (history! #t)
  (define ref (length (visited)))
  (step!)
  ;; eliminate other branch
  (switch-goal! 1)
  (align-case!)
  (subsumed! ref)
  (history! #f))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(step-to-start-of-main!)
(do-read-command!)
(do-read-state!)
(do-handle!)
;; finish all branches
(let loop ()
  (unless (empty? (next))
    (do-write-state!)
    (do-write-response!)
    (step-until! poweroff)
    (r-holds!)
    (loop)))
