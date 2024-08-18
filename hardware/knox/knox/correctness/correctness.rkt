#lang racket/base

(require
 yosys/meta
 (prefix-in crv32: crv32)
 parfait/spec
 "../driver.rkt"
 "../circuit.rkt"
 "../result.rkt"
 "../driver/interpreter.rkt"
 "checker.rkt"
 "hint.rkt"
 (only-in racket/class new send)
 (prefix-in @ (combine-in rosette/safe rosutil/addressable-struct rosutil/convenience)))

(provide verify-correctness)

(define (verify-correctness
         spec
         circuit
         driver
         #:R R
         #:hints [hints (lambda (method c1 f1) (make-hintdb))]
         #:only [only-method #f] ; method name or 'init or 'idle
         #:override-args [override-args #f]
         #:override-f1 [override-f1 #f]
         #:override-c1 [override-c1 #f]
         #:without-yield [without-yield #f]
         #:verbose [verbose #f])
  (@gc-terms!)
  (define crash+por (crash+power-on-reset circuit)) ; so we can re-use it
  (when (or (not only-method) (equal? only-method 'invariant))
    (when verbose (printf "verifying invariant...\n"))
    (verify-invariant circuit verbose)
    (when verbose (printf "  done!\n")))
  (when (or (not only-method) (equal? only-method 'init))
    (when verbose (printf "verifying init...\n"))
    (verify-init spec circuit crash+por R verbose)
    (when verbose (printf "  done!\n")))
  (when (or (not only-method) (equal? only-method 'idle))
    (when verbose (printf "verifying idle...\n"))
    (verify-idle spec circuit driver R verbose)
    (when verbose (printf "  done!\n")))
  (when (or (not only-method) (equal? only-method 'handle))
    (when verbose (printf "verifying handle...\n"))
    (verify-handle spec circuit driver R override-args override-f1 override-c1 without-yield hints verbose)
    (when verbose (printf "  done!\n"))))

;; yosys uses the {module}_i to denote an initializer, not an invariant,
;; but we only use the initializer to initialize ROMs, and so it's an invariant
;;
;; still, here, we double-check that it's indeed an invariant, and that the
;; user didn't accidentally have other mutable fields be initialized
(define (verify-invariant circuit verbose)
  (define m (circuit-meta circuit))
  (define c1 ((meta-new-symbolic m)))
  (define c2 ((meta-step m) c1))
  (define inv (meta-invariant m))
  (define res
    (@verify
     (@begin
      (@assume (inv c1))
      (@assert (inv c2)))))
  (cond
    [(@unsat? res) (void)] ; verified
    [(@unknown? res) (error 'verify-invariant "solver timeout")]
    [else (error 'verify-invariant "failed to prove invariant: misuse of 'initial' in Verilog?")]))

(define (verify-init spec circuit crash+por R verbose)
  (define f0 (spec-init-state spec))
  (define m (circuit-meta circuit))
  (define c0
    (@update-fields
     ((meta-new-symbolic m))
     (let ([c-zeroed ((meta-new-zeroed m))])
       (for/list ([field-name (circuit-init-zeroed-fields circuit)])
         (cons field-name (@get-field c-zeroed field-name))))))
  (define c-init (crash+por c0))
  (define inv (meta-invariant m))
  (define res
    (@verify
     (@begin
      (@assume (inv c0))
      (@assert (R f0 c-init)))))
  (cond
    [(@unsat? res) (void)] ; verified
    [(@unknown? res) (error 'verify-init "solver timeout")]
    [verbose
     (define sol (@complete-solution res (@symbolics (@list f0 c-init))))
     (printf "failed to prove init\n")
     (printf "c-init = ~v\n" (@evaluate c-init sol))
     (printf "f0 = ~v\n" (@evaluate f0 sol))
     (printf "(R f0 c-init) = ~v\n" (@evaluate (R f0 c-init) sol))
     ;; finally, raise an error
     (error 'verify-init "failed to prove init")]
    [else (error 'verify-init "failed to prove init")]))

(define (verify-idle spec circuit driver R verbose)
  (define f1 ((spec-new-symbolic-state spec)))
  (define m (circuit-meta circuit))
  (define idle-input
    (@update-field
     (@update-fields ((meta-new-symbolic-input (circuit-meta circuit)))
                     (driver-idle driver))
     (circuit-reset-input-name circuit)
     (not (circuit-reset-input-signal circuit))))
  (define c1 ((meta-new-symbolic m)))
  (define c2 ((meta-step m) ((meta-with-input m) c1 idle-input)))
  (define inv (meta-invariant m))
  (define res
    (@verify
     (@begin
      (@assume (R f1 c1))
      (@assume (inv c1))
      (@assert (R f1 c2)))))
  (cond
    [(@unsat? res) (void)] ; verified
    [(@unknown? res) (error 'verify-idle "solver timeout")]
    [verbose
     (define sol (@complete-solution res (@symbolics (@list f1 idle-input c1 c2))))
     (printf "failed to prove idle\n")
     (printf "c1 = ~v\n" (@evaluate c1 sol))
     (printf "f1 = ~v\n" (@evaluate f1 sol))
     (printf "(R f1 c1) = ~v\n" (@evaluate (R f1 c1) sol))
     (printf "input = ~v\n" (@evaluate idle-input sol))
     (printf "c2 = ~v\n" (@evaluate c2 sol))
     (printf "(R f1 c2) = ~v\n" (@evaluate (R f1 c2) sol))
     (error 'verify-idle "failed to prove idle")]
    [else (error 'verify-idle "failed to prove idle")]))

(define (verify-handle spec circuit driver R override-args override-f1 override-c1 without-yield hints verbose)
  ;; set up method and arguments
  (define args (or override-args ((spec-new-symbolic-command spec))))
  ;; spec
  (define f1 (or override-f1 ((spec-new-symbolic-state spec))))
  (define m1 ((spec-handle spec) f1 args))
  ;; circuit
  (define m (circuit-meta circuit))
  (define c1 (@update-fields (or override-c1 ((meta-new-symbolic m)))
                             (cons
                              ;; reset is de-asserted
                              (cons (circuit-reset-input-name circuit)
                                    (not (circuit-reset-input-signal circuit)))
                              ;; other inputs are idle
                              (driver-idle driver))))
  ;; make sure reset line is de-asserted
  (define driver-expr (list 'handle (list 'quote args)))
  (define initial-interpreter-state
    (make-interpreter driver-expr (driver-bindings driver) c1 m))
  (define local-hints (hints (cons 'handle args) c1 f1))
  (define inv (meta-invariant m))
  (define precondition (@check-no-asserts (@&& (R f1 c1) (inv c1))))
  (define exc (new checker%
                   [spec spec]
                   [initial-state initial-interpreter-state]
                   [initial-spec-machine m1]
                   [hint-db local-hints]
                   [precondition precondition]
                   [without-yield without-yield]))
  (when verbose (send exc debug!))
  ;; run
  (define finished (send exc run!))
  (for ([f finished])
    (define pc (checker-state-pc f))
    (define c-result (checker-state-interpreter f))
    (define c-out (finished-value c-result))
    (define c2 (finished-circuit c-result))
    (define f-out ((spec-get-response spec) (checker-state-spec-machine f)))
    (define f2 ((spec-get-state spec) (checker-state-spec-machine f)))
    (define res
      (@verify
       (@begin
        (@assume precondition) ; R and hardware invariant
        (@assume pc)
        (@assert (@equal? f-out c-out))
        (@assert (R f2 c2)))))
    (cond
      [(@unsat? res) (void)] ; verified
      [(@unknown? res) (error 'verify-handle "solver timeout")]
      [verbose
       (define sol (@complete-solution res (@symbolics (@list args f1 f-out f2 c1 c-out c2))))
       (printf "failed to verify\n")
       (printf "c1 = ~v\n" (@evaluate c1 sol))
       (printf "f1 = ~v\n" (@evaluate f1 sol))
       (printf "args = ~v\n" (@evaluate args sol))
       (printf "f2 = ~v\n" (@evaluate f2 sol))
       (printf "f-out = ~v\n" (@evaluate f-out sol))
       (printf "c-out = ~v\n" (@evaluate c-out sol))
       (printf "(R f2 c2) = ~v\n" (@evaluate (R f2 c2) sol))
       (printf "c2 = ~v\n" (@evaluate c2 sol))
       ;; finally, raise an error
       (error 'verify-handle "failed to verify")]
      [else (error 'verify-handle "failed to verify")])))
