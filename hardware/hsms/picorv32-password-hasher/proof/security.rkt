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
  (define c (lens-view (lens 'circuit 'wrapper.soc.cpu.reg_pc) t))
  (define cs (lens-view (lens 'circuit 'wrapper.soc.cpu.cpu_state) t))
  (define s (lens-view (lens 'emulator 'auxiliary 'wrapper.soc.cpu.reg_pc) t))
  (define ss (lens-view (lens 'emulator 'auxiliary 'wrapper.soc.cpu.cpu_state) t))
  (printf "ckt: ~v ~v emu: ~v ~v\n" c cs s ss))

(define (step-n! n)
  (unless (zero? n)
    (step!)
    (printf "step ~a, " n)
    (show-pcs)
    (step-n! (sub1 n))))

(define (poweroff term)
  (racket/equal? (lens-view (lens 'circuit 'wrapper.pwrmgr_state) term) (bv #b01 2)))

(define ((pc-is pc) term)
  (racket/equal? (lens-view (lens 'circuit 'wrapper.soc.cpu.reg_pc) term) pc))

(define ((state-is state) term)
  (racket/equal? (lens-view (lens 'circuit 'wrapper.soc.cpu.cpu_state) term) state))

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
                          'wrapper.soc.cpu.reg_pc
                          'wrapper.soc.cpu.decoder_trigger
                          'wrapper.soc.cpu.latched_branch
                          'wrapper.soc.cpu.latched_store
                          'wrapper.soc.cpu.mem_do_rinst))
  (concretize! (lens (list (lens 'circuit branch-related)
                                   (lens 'emulator 'auxiliary branch-related)))))

;; proceed to the UART read; returns var
(define (step-past-uart-read! [read-name #f])
  (step-until! (pc-is (bv #x0000012c 32)) #t)

  ;; now, we overapproximate some stuff, so we can loop back later
  (overapproximate!
   (lens (list (lens 'circuit (list 'wrapper.soc.cpu.alu_out_q
                                    'wrapper.soc.cpu.reg_op1
                                    'wrapper.soc.uart.simpleuart.send_divcnt
                                    'wrapper.soc.cpu.count_cycle
                                    'wrapper.soc.cpu.count_instr
                                    'wrapper.soc.cpu.is_lbu_lhu_lw
                                    'wrapper.soc.cpu.mem_addr
                                    'wrapper.soc.cpu.mem_rdata_q
                                    'wrapper.soc.cpu.mem_wstrb
                                    'wrapper.soc.cpu.reg_op2
                                    (lens 'wrapper.soc.cpu.cpuregs (list 5 31))))
               (lens 'emulator 'auxiliary (list 'wrapper.soc.cpu.alu_out_q
                                                'wrapper.soc.cpu.reg_op1
                                                'wrapper.soc.uart.simpleuart.send_divcnt
                                                'wrapper.soc.cpu.count_cycle
                                                'wrapper.soc.cpu.count_instr
                                                'wrapper.soc.cpu.is_lbu_lhu_lw
                                                'wrapper.soc.cpu.mem_addr
                                                'wrapper.soc.cpu.mem_rdata_q
                                                'wrapper.soc.cpu.mem_wstrb
                                                'wrapper.soc.cpu.reg_op2
                                                (lens 'wrapper.soc.cpu.cpuregs (list 5 31)))))))
  (history! #t)
  (define pre-read (length (visited)))
  ;; on the branch now
  (step-until! (pc-is (bv #x00000134 32)) #t)
  ;; read is done now, in register x15 (a5), abstract it and then case analyze on whether it returned -1 or not
  (define var (match-abstract! (lens 'wrapper.soc.cpu.cpuregs 5) read-name))
  (define old-pred (set-predicate (current)))
  (cases*! (list (equal? var (bv -1 32))))
  ;; currently in the "no data" case, should be able to get back to start of loop at 0x88
  (step-until! (state-is (bv #x40 8)) #t)
  (concretize-branch!)
  (step-until! (pc-is (bv #x0000012c 32)) #t)
  (step-n! 2)
  (subsumed! pre-read)
  (history! #f)
  ;; UART read finished
  (step-until! (state-is (bv #x40 8)) #t)
  (concretize-branch!)
  (overapproximate-predicate! old-pred)
  (step-until! (pc-is (bv #x144 32)))
  var)

(define (step-past-uart-write!)
  (step-until! (pc-is (bv #x15c 32)))
  (overapproximate!
   (lens (list (lens 'circuit (list
                               'wrapper.soc.cpu.alu_out_q
                               'wrapper.soc.cpu.mem_rdata_q
                               'wrapper.soc.uart.simpleuart.send_divcnt
                               'wrapper.soc.cpu.count_cycle
                               'wrapper.soc.cpu.count_instr
                               'wrapper.soc.cpu.pcpi_insn
                               #;(lens 'wrapper.soc.cpu.cpuregs 6)))
               (lens 'emulator 'auxiliary (list
                                           'wrapper.soc.cpu.alu_out_q
                                           'wrapper.soc.cpu.mem_rdata_q
                                           'wrapper.soc.uart.simpleuart.send_divcnt
                                           'wrapper.soc.cpu.count_cycle
                                           'wrapper.soc.cpu.count_instr
                                           'wrapper.soc.cpu.pcpi_insn
                                           #;(lens 'wrapper.soc.cpu.cpuregs 6))))))
  (define cts-read (match-abstract! (lens 'wrapper.soc.cpu.cpuregs 6) 'cts-read))
  (define pre-write (length (visited)))
  (history! #t)
  (step-until! (state-is (bv #x40 8)))
  (define old-pred (set-predicate (current)))
  (cases*! (list (not (bvzero? cts-read))))
  ;; no cts case, should be able to get back to start of loop
  (concretize-branch!)
  ;; go past the loop, and then back to where we were
  (step-until! (pc-is (bv #x158 32)))
  (step-until! (pc-is (bv #x15c 32)))
  (subsumed! pre-write)
  (history! #f)
  ;; main thread
  (concretize-branch!)
  (overapproximate-predicate! old-pred)
  (step-until! (pc-is (bv #x178 32))))

(define (step-to-start-of-main!)
  (concretize!
        (lens 'circuit (list 'wrapper.soc.rom.rom
                             'wrapper.pwrmgr_state
                             'resetn)))

  ;; we want to get rid of the predicate, to simplify subsumption checks
  ;; so we make use of replace and overapproximate-predicate
  ;;
  ;; compute spec state based on circuit state
  (replace! (lens 'emulator 'oracle) (AbsF (lens-view (lens 'term 'circuit) (current))))
  (overapproximate-predicate! #t)

  (overapproximate!
        (lens 'emulator 'auxiliary
              (list (field-filter/not (field-filter/or 'resetn 'wrapper.pwrmgr_state
                                                       'wrapper.soc.cpu.cpuregs 'wrapper.soc.ram.ram 'wrapper.soc.fram.fram 'wrapper.soc.rom.rom))
                    ;; note: we purposefully don't overapproximate the FRAM: we make sure it's zeroed out at the start and end
                    (lens 'wrapper.soc.ram.ram vector-all-elements-lens)
                    (lens 'wrapper.soc.cpu.cpuregs vector-all-elements-lens))))

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
  (step-until! (pc-is (bv #x0000010c 32)) #f)

  ;; proceed to right before reading the command
  (step-until! (pc-is (bv #x204 32))))

(define (do-read-command!)
  (for ([i (range COMMAND-LENGTH)])
    (step-past-uart-read!)))

(define (do-write-response!)
  (for ([i (range RESPONSE-LENGTH)])
    (step-past-uart-write!)))

(define (do-read-state!)
  ;; going to do case analysis on which region is active, step just past the snez
  (step-until! (pc-is (bv #x258 32)))
  (define state (lens-view (lens 'emulator 'oracle) (set-term (current))))
  (define fram (lens-view (lens 'circuit 'wrapper.soc.fram.fram) (set-term (current))))
  (define fram0 (vector-ref fram 0))
  (define active0 (bvzero? (lens-view (lens 'circuit 'wrapper.soc.fram.fram 0) (set-term (current)))))
  (cases! (list active0 (! active0)))

  (define (align-case!)
    (concretize! (lens 'circuit 'wrapper.soc.cpu.cpuregs 6))
    (step-until! (pc-is (bv #x280 32)))
    (for ([i (range STATE-LENGTH)])
      (replace! (lens 'circuit 'wrapper.soc.ram.ram (+ state-base i))
                (if active0
                    (vector-ref fram (+ 2 i))
                    (vector-ref fram (+ 2 STATE-LENGTH i)))))
    (overapproximate! (lens 'circuit 'wrapper.soc.cpu.cpuregs (list 5 6 7 10 11 12 13 14 15 16 17 28 29 30 31)))
    (overapproximate! (lens 'circuit 'wrapper.soc.cpu.mem_wdata))
    (overapproximate-predicate! #t)) ;; don't even need R at this point, we've loaded the state into RAM

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
  (begin-sync! picorv32-mapping)
  ;; get past all the symbolic branches, and then enable abstraction
  (define (ready? t)
    (define emu-ckt (lens-view (lens 'emulator 'auxiliary) (set-term t)))
    (and (not ((mapping-symbolic-branch? picorv32-mapping) emu-ckt))
         (bvuge (get-field (pairing-circuit (set-term t)) 'wrapper.soc.cpu.reg_pc) (bv #x63c 32))))
  (define (all-ready?)
    (for/and ([t (next)]) (ready? t)))
  (define (maybe-concretize!)
    (define emu-ckt (lens-view (lens 'emulator 'auxiliary) (set-term (current))))
    (when ((mapping-symbolic-branch? picorv32-mapping) emu-ckt)
      (concretize! (lens 'emulator 'auxiliary (mapping-cpu-lens picorv32-mapping))
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
  (step-until! (pc-is (bv #x2dc 32)))
  (define state (lens-view (lens 'emulator 'oracle) (set-term (current))))
  ;; load fram before the commit point
  (define fram (lens-view (lens 'circuit 'wrapper.soc.fram.fram) (set-term (current))))
  (define fram0 (vector-ref fram 0))
  (define ram (lens-view (lens 'circuit 'wrapper.soc.ram.ram) (set-term (current))))
  (define active0 (bvzero? (lens-view (lens 'circuit 'wrapper.soc.fram.fram 0) (set-term (current)))))
  (cases! (list active0 (! active0)))

  (define (align-case!)
    (concretize! (lens 'circuit 'wrapper.soc.cpu.cpuregs 16))
    (step-until! (pc-is (bv #x314 32)))
    (step-n! 5)
    ;; do alignment
    (for ([i (range STATE-LENGTH)])
      (replace! (lens 'circuit 'wrapper.soc.fram.fram (+ 2 i))
                (if active0 (vector-ref fram (+ 2 i)) (vector-ref ram (+ state-base i)))))
    (for ([i (range STATE-LENGTH)])
      (replace! (lens 'circuit 'wrapper.soc.fram.fram (+ 2 STATE-LENGTH i))
                (if active0 (vector-ref ram (+ state-base i)) (vector-ref fram (+ 2 STATE-LENGTH i)))))
    (overapproximate! (lens 'circuit 'wrapper.soc.cpu.cpuregs (list 5 6 7 10 11 12 13 14 15 16 17 28 29 30 31)))
    (overapproximate! (lens 'circuit 'wrapper.soc.cpu.mem_wdata))
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
