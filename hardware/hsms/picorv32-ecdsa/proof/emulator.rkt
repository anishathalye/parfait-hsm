#lang knox/emulator

(define (initial-circuit)
  (circuit-with-input
   (circuit-step
    (circuit-with-input
     (circuit-new)
     (input* 'resetn #f 'cts #t 'rx #t)))
   (input* 'resetn #t 'cts #t 'rx #t)))

(define (init)
  (set! (initial-circuit)))

(define (with-input i)
  (set! (circuit-with-input (get) i)))

(define (get-output)
  (circuit-get-output (get)))

(define (repeat v n)
  (if (= n 0) '() (cons v (repeat v (sub1 n)))))

(define (load4 v i)
  (let ([b (vector-ref v i)])
    (list
     (extract 7 0 b)
     (extract 15 8 b)
     (extract 23 16 b)
     (extract 31 24 b))))

(define (load-bytes v ofs-words nbytes)
  (if (>= nbytes 4)
      (append (load4 v ofs-words) (load-bytes v (add1 ofs-words) (- nbytes 4)))
      (take (load4 v ofs-words) nbytes)))

(define (store-bytes vec ofs-words val)
  (if (>= (length val) 4)
      (let ([nv (concat (list-ref val 3) (list-ref val 2) (list-ref val 1) (list-ref val 0))])
        (let ([upd (vector-set vec ofs-words nv)])
          (if (> (length val) 4)
              (store-bytes upd (add1 ofs-words) (drop val 4))
              upd)))
      (let ([prev (vector-ref vec ofs-words)]
            [l (length val)])
        (vector-set
         vec
         ofs-words
         (concat
          (if (> l 3) (list-ref val 3) (extract 31 24 prev))
          (if (> l 2) (list-ref val 2) (extract 23 16 prev))
          (if (> l 1) (list-ref val 1) (extract 15 8 prev))
          (if (> l 0) (list-ref val 0) (extract 7 0 prev)))))))

(define (step)
  ;; invoke call of spec
  (let ([c (get)])
    (if (and
         (equal? (get-field c 'wrapper.pwrmgr_state) (bv #b10 2))
         (equal? (get-field c 'wrapper.soc.cpu.reg_pc) (bv #xbc8 32))
         (equal? (get-field c 'wrapper.soc.cpu.cpu_state) (bv #x20 8)))
        (let ([ram (get-field c 'wrapper.soc.ram.ram)])
          (let ([cmd (load-bytes ram 930 49)])
            (displayln "emulator: invoking call()")
            (call cmd)))
        (void)))
  ;; zero out state/cmd, because emulator doesn't need it anymore (after reading command tag)
  (let ([c (get)])
    (if (and
         (equal? (get-field c 'wrapper.pwrmgr_state) (bv #b10 2))
         (equal? (get-field c 'wrapper.soc.cpu.reg_pc) (bv #xbe0 32))
         (equal? (get-field c 'wrapper.soc.cpu.cpu_state) (bv #x20 8)))
        (let ([ram (get-field c 'wrapper.soc.ram.ram)])
          (displayln "emulator: clearing state/command")
          (set! (update-field c 'wrapper.soc.ram.ram
                              (store-bytes
                               ;; state
                               (store-bytes ram 899 (repeat (bv 0 8) 56))
                               ;; command
                               930 (repeat (bv 0 8) 49)))))
        (void)))
  ;; zero out fram at poweroff
  (let ([c (get)])
    (if (and
         (equal? (get-field c 'wrapper.pwrmgr_state) (bv #b10 2))
         (equal? (get-field c 'wrapper.soc.cpu.reg_pc) (bv #xb80 32)))
        (let ()
          (displayln "emulator: poweroff")
          (set! (update-field c 'wrapper.soc.fram.fram (get-field (circuit-zeroed) 'wrapper.soc.fram.fram))))
        (void)))

  (let ([pre-commit (bvzero? (vector-ref (get-field (get) 'wrapper.soc.fram.fram) 0))])
    (set! (circuit-step (get)))
    ;; invoke return at commit point; this has to come after the step
    (let ([c (get)])
      (if (and
           (equal? (get-field c 'wrapper.pwrmgr_state) (bv #b10 2))
           pre-commit
           (not (bvzero? (vector-ref (get-field c 'wrapper.soc.fram.fram) 0)))) ; at commit point
          (let ([ram (get-field c 'wrapper.soc.ram.ram)])
            (let ([v (return)])
              (displayln "emulator: invoking return()")
              (set! (update-field c 'wrapper.soc.ram.ram
                                  (store-bytes ram 913 v)))))
          (void)))))
