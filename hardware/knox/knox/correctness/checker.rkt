#lang racket/base

(require
 (prefix-in interp: "../driver/interpreter.rkt")
 "hint.rkt"
 racket/class racket/set racket/match racket/list racket/function
 (prefix-in yosys: yosys)
 (prefix-in @ (combine-in rosutil rosette/safe))
 (prefix-in crv32: (only-in crv32 step run))
 (prefix-in parfait: (combine-in parfait/sync parfait/spec))
 syntax/parse/define)

(provide checker%
         (prefix-out checker- (struct-out state)))

(@addressable-struct state
  (interpreter
   pc
   equalities
   spec-machine))

(struct execution
  (state
   next-hint
   sync-state)
  #:transparent)

(define (protected-evaluate-to-next-hint k [arg (void)])
  (if k
      (@check-no-asserts (evaluate-to-next-hint k arg))
      #f))

(define (finished? st)
  (not (interp:state? (state-interpreter st))))

(define (weak-seteq->seteq s)
  (for/seteq ([e (in-weak-set s)]) e))

(define top-view
  (@virtual-lens
   (list
    (cons 'circuit (@lens 'globals 'circuit))
    (cons 'interpreter (@virtual-lens
                        (list
                         (cons 'control (@lens 'control))
                         (cons 'environment (@lens 'environment))
                         (cons 'continuation (@lens 'continuation))))))))

(define checker%
  (class object%
    (super-new)
    (init initial-state)
    (init initial-spec-machine)
    (init-field hint-db)
    (init [precondition #t])
    (init-field [spec #f])
    (init-field [without-yield #f])
    (define free-variables (weak-seteq))
    (define completed '()) ; list of state
    (define working (list (execution (state initial-state precondition (hasheq) initial-spec-machine) #f #f))) ; list of execution
    (define waiting '()) ; list of state (not execution, because we already have the hint saved in merge-hint)
    (define debug*-hint #f)
    (define merge-hint #f)
    (define debug #f)

    (define/public (debug!)
      (set! debug #t))

    (define (dprintf . args)
      (when debug (apply printf args)))

    (define (run-single! exc)
      (match-define (execution st hint sync-state) exc)
      (cond
        ;; are there any pending hints? if so run them
        [hint (run-hint! st hint sync-state)]
        ;; no pending hints; run to next hypercall, handle it
        [else
         (define st* (run-to-next-hypercall st sync-state))
         (cond
           [(finished? st*)
            ;; value
            (set! completed (cons st* completed))]
           [else
            ;; hypercall
            (handle-hypercall! st* sync-state)])]))

    (define (handle-hypercall! st sync-state)
      (match-define (state (and ist (interp:state control environment globals continuation)) pc equalities spec-machine) st)
      (unless (list? control)
        (error 'handle-hypercall! "hypercall must be a concrete list, not a term (~v), try concretizing more?" control))
      (match-define (list fun hint-name) control)
      (define hint (hash-ref hint-db hint-name))
      (case fun
        [(yield)
         (cond
           [without-yield
            ;; step past
            (define st1 (@check-no-asserts (interp:step ist) #:assumes pc))
            (set! working (cons (execution (state st1 pc equalities spec-machine) #f sync-state) working))]
           [else
            (unless (fixpoint? hint)
              (error 'handle-hypercall! "argument to yield must be a fixpoint hint"))
            (define ckt (interp:globals-circuit globals))
            (define metadata (interp:globals-meta globals))
            (define ckt-step (yosys:meta-step metadata))
            (match-define (fixpoint setup auto len step-concretize-lens use-pc piecewise step-overapproximate-lens k) hint)
            (define fp
              (compute-fixpoint
               pc
               (@&& pc (equalities->bool equalities))
               ckt-step
               ckt
               setup
               auto
               len
               step-concretize-lens
               use-pc
               piecewise
               step-overapproximate-lens))
            ;; step (interpreter) once more to advance past the call
            (define st1 (@check-no-asserts (interp:step ist) #:assumes pc))
            ;; make one state for every point in fp, put back on working list
            (set! working
                  (append
                   (for/list ([ckt fp])
                     (let ([st* (state (update-state-circuit st1 ckt) pc equalities spec-machine)])
                       (execution st* (protected-evaluate-to-next-hint k) sync-state)))
                   working))
            (dprintf "info: yielded, now have ~a threads, ~a waiting~n" (length working) (length waiting))])]
        [(hint)
         ;; don't actually do anything here, just remember that we need to apply the hint next, and
         ;; step once more to advance past the call
         (define st1 (@check-no-asserts (interp:step ist) #:assumes pc))
         (set! working (cons (execution (state st1 pc equalities spec-machine) hint sync-state) working))]))

    (define (run-hint! st hint sync-state)
      (match-define (state ist pc equalities spec-machine) st)
      (match hint
        [(? done?) (set! working (cons (execution st #f sync-state) working))]
        [(tactic k)
         (set! working (cons (execution st (protected-evaluate-to-next-hint k) sync-state) working))]
        [(get-state k)
         (set! working (cons (execution st (protected-evaluate-to-next-hint k st) sync-state) working))]
        [(concretize! lens use-pc use-equalities piecewise k)
         (define full-lens (@lens-thrush top-view lens))
         (define effective-pc (@&&
                               (if use-pc pc #t)
                               (if use-equalities (equalities->bool equalities) #t)))
         (define ist* (@lens-transform full-lens ist
                                       (lambda (view) (@concretize view effective-pc #:piecewise piecewise))))
         (define st* (state ist* pc equalities spec-machine))
         (set! working (cons (execution st* (protected-evaluate-to-next-hint k) sync-state) working))]
        [(overapproximate! lens k)
         (define full-lens (@lens-thrush top-view lens))
         (define view (@lens-view full-lens ist))
         (define overapprox-view (@overapproximate view))
         (for ([var (in-list (@symbolics overapprox-view))])
           (set-add! free-variables var))
         (define ist* (@lens-set full-lens ist overapprox-view))
         (define st* (state ist* pc equalities spec-machine))
         (set! working (cons (execution st* (protected-evaluate-to-next-hint k overapprox-view) sync-state) working))]
        [(overapproximate-pc! new-pc use-equalities k)
          (define effective-pc (if use-equalities
                                   (@&& pc (equalities->bool equalities))
                                   pc))
          (unless (@unsat? (@verify (@assert (@implies effective-pc new-pc))))
            (error 'run-hint! "hint overapproximate-pc: not an overapproximation"))
          (define st* (state ist new-pc equalities spec-machine))
          (set! working (cons (execution st* (protected-evaluate-to-next-hint k) sync-state) working))]
        [(replace! lens view use-pc use-equalities k)
         (define full-lens (@lens-thrush top-view lens))
         (define current-view (@lens-view full-lens ist))
         (define effective-pc (@&&
                               (if use-pc pc #t)
                               (if use-equalities (equalities->bool equalities) #t)))
         (unless (@unsat? (@verify (@begin (@assume effective-pc) (@assert (@equal? current-view view)))))
           (error 'run-hint! "hint replace: failed to prove equality"))
         (define ist* (@lens-set full-lens ist view))
         (define st* (state ist* pc equalities spec-machine))
         (set! working (cons (execution st* (protected-evaluate-to-next-hint k) sync-state) working))]
        [(remember! lens name k)
         (define full-lens (@lens-thrush top-view lens))
         (define current-view (@lens-view full-lens ist))
         (define current-type (@type-of current-view))
         (when (not (@solvable? current-type))
           (error 'run-hint! "hint remember: not a solvable type"))
         (define new-var (@fresh-symbolic (or name '||) current-type))
         (define ist* (@lens-set full-lens ist new-var))
         (define st* (state ist* pc (hash-set equalities new-var current-view) spec-machine))
         ;; pass new variable to callback...
         (set! working (cons (execution st* (protected-evaluate-to-next-hint k new-var) sync-state) working))]
        [(subst! lens var k)
         (define full-lens (@lens-thrush top-view lens))
         (define ist* (@lens-transform full-lens ist (lambda (view)
                                                       (if var
                                                           (@substitute view var (hash-ref equalities var))
                                                           (@substitute-terms view equalities)))))
         (define st* (state ist* pc equalities spec-machine))
         (set! working (cons (execution st* (protected-evaluate-to-next-hint k) sync-state) working))]
        [(clear! var k)
         (define equalities* (if var
                                 (if (list? var)
                                     (for/fold ([equalities equalities])
                                               ([v var])
                                       (hash-remove equalities var))
                                     (hash-remove equalities var))
                                 (hasheq)))
         (define st* (state ist pc equalities* spec-machine))
         (set! working (cons (execution st* (protected-evaluate-to-next-hint k) sync-state) working))]
        [(spec-finish! k)
         (define spec-machine* (crv32:run spec-machine (parfait:spec-environment spec)))
         (define st* (state ist pc equalities spec-machine*))
         ;; sync-state gets cleared out
         (set! working (cons (execution st* (protected-evaluate-to-next-hint k) #f) working))]
        [(begin-sync! mapping k)
         (set! working (cons (execution st (protected-evaluate-to-next-hint k) (parfait:new-sync-state mapping)) working))]
        [(auto-sync! k)
         (set!
          working
          (append
           (if sync-state
               (let ([ckt (interp:globals-circuit (interp:state-globals ist))])
                 (for/list ([res (parfait:sync ckt spec-machine sync-state spec #:verbose debug)])
                   (match-define (list c* s* sync-state* pred*) res)
                   ;; just ignoring pred for now
                   (define ist* (@lens-set (@lens 'globals 'circuit) ist c*))
                   (define st* (state ist* pc equalities s*))
                   (execution st* (protected-evaluate-to-next-hint k) sync-state*)))
               (list (execution st (protected-evaluate-to-next-hint k) #f)))
           working))]
        [(case-split! splits* use-equalities k)
         (define splits (do-case-split st use-equalities splits*))
         (set! working (append (map (lambda (st) (execution st (protected-evaluate-to-next-hint k) sync-state)) splits) working))]
        [(? merge!?)
         ;; auto-syncing not supported through merge, we don't need it
         (when sync-state
           (error 'run-hint! "auto-syncing through merge not supported"))
         ;; put on waiting list
         (set! waiting (cons st waiting))
         (set! debug*-hint #f)
         (unless merge-hint
           (set! merge-hint hint))]
        [(? debug*?)
         ;; auto-syncing not supported through debug*, we don't need it
         (when sync-state
           (error 'run-hint! "auto-syncing through debug* not supported"))
         (set! waiting (cons st waiting))
         (unless debug*-hint
           (set! debug*-hint hint))]
        [else (error 'run-hint! "unimplemented hint: ~a" hint)]))

    (define (do-debug*!)
      ((debug*-callback debug*-hint) waiting)
      (set! working (map (lambda (st) (execution st #f #f)) waiting))
      (set! waiting '())
      (set! debug*-hint #f))

    (define (do-case-split st use-equalities splits)
      ;; split interpreter N ways, augmenting path condition with splits
      ;;
      ;; check that the split is indeed an exhaustive split (given current pc)
      ;;
      ;; doesn't make use of extra info in equalities, but that's okay
      (define pc (state-pc st))
      (define effective-pc (if use-equalities
                               (@&& pc (equalities->bool (state-equalities st)))
                               pc))
      ;; prune unsat splits
      (define pruned-splits
        (filter (lambda (p) (not (@unsat? (@solve (@assert (@&& effective-pc p)))))) splits))
      ;; verify that the current pc implies that at least one of the splits must hold
      ;;
      ;; if we have splits p1, p2, ..., pn, we prove _here_ that
      ;; pc => (p1 \/ p2 \/ ... \/ pn), and we create n threads
      ;; with pcs (pc /\ p1), (pc /\ p2), ..., (pc /\ pn)
      (define any-split (apply @|| pruned-splits))
      (when (not (@unsat? (@verify (@assert (@implies effective-pc any-split)))))
        (error 'do-case-split "failed to prove exhaustiveness"))
      (dprintf "info: case split ~a ways~n" (length pruned-splits))
      (for/list ([p pruned-splits])
        (state (state-interpreter st) (@&& pc p) (state-equalities st) (state-spec-machine st))))

    (define (merge-states!)
      ;; first, partition by path condition (we never merge across different PCs) as well as machine state
      ;; (we don't merge across different spec machines either)
      (define by-pc-eq-m (group-by (lambda (st) (list (state-pc st) (state-equalities st) (state-spec-machine st))) waiting))
      (define free-vars-seteq (weak-seteq->seteq free-variables))
      (define merged (apply append (map (lambda (st) (merge-states-for-pc-eq st free-vars-seteq)) by-pc-eq-m)))
      (define k (merge!-k merge-hint))
      (set! working (map (lambda (st) (execution st (protected-evaluate-to-next-hint k) #f)) merged))
      (dprintf "info: merged, reduced from ~v states to ~v states~n" (length waiting) (length working))
      (set! waiting '())
      (set! merge-hint #f))

    (define (merge-states-for-pc-eq sts free-vars-seteq)
      ;; right now, we only handle the case where the rest of the
      ;; interpreter state is identical between all forks; in the future, we
      ;; could partition by interpreter state and support multiple, but I don't
      ;; think this is necessary right now
      (define template-state (first sts))
      (define template-interpreter (state-interpreter template-state))
      (for ([st (rest sts)])
        (define ist (state-interpreter st))
        ;; note: we don't check globals, because we're expecting the
        ;; circuit to differ, and we're not expecting the environment or meta
        ;; to differ (it never changes)
        (unless (or (and (interp:finished? ist) (interp:finished? template-interpreter))
                    (and (equal? (interp:state-control ist) (interp:state-control template-interpreter))
                         (equal? (interp:state-environment ist) (interp:state-environment template-interpreter))
                         (equal? (interp:state-continuation ist) (interp:state-continuation template-interpreter))))
          (error 'merge-states! "interp:states differ in aspects other than circuit")))
      (define effective-pc
        (let* ([st1 (first sts)]
               [pc (state-pc st1)]
               [eq (state-equalities st1)])
          (@&& pc (equalities->bool eq))))
      (define ckts
        (shrink-by-key
         (map
          (lambda (st)
            (define s (state-interpreter st))
            (if (interp:finished? s) (interp:finished-circuit s) (interp:globals-circuit (interp:state-globals s))))
          sts)
         (merge!-key merge-hint)
         effective-pc
         free-vars-seteq))
      (for/list ([ckt ckts])
        (state (update-state-circuit template-interpreter ckt) (state-pc template-state) (state-equalities template-state) (state-spec-machine template-state))))

    (define (compute-fixpoint pc effective-pc step s0 setup-cycles auto cycle-length step-concretize-lens use-pc piecewise step-overapproximate-lens)
      (define (step* ckt)
        ;; step, but applying concretization/overapproximatino if required at every step
        (let* ([ckt (step ckt)]
               [ckt (if step-concretize-lens
                        (@lens-transform step-concretize-lens ckt (lambda (view) (@concretize view (if use-pc pc #t) #:piecewise piecewise)))
                        ckt)]
               [ckt (if step-overapproximate-lens
                        (let ([overapprox-view (@overapproximate (@lens-view step-overapproximate-lens ckt))])
                          (for ([var (in-list (@symbolics overapprox-view))])
                            (set-add! free-variables var))
                          (@lens-set step-overapproximate-lens ckt overapprox-view))
                        ckt)])
          ckt))
      (let loop ([rev-steps (rev-step-n step* s0 (+ cycle-length (or setup-cycles 0)))]) ; going to need a minimum of this many steps
        (dprintf "info: auto fixpoint finding at ~a cycles of setup~n" (- (length rev-steps) cycle-length 1))
        ;; next step
        (define next-step (step* (first rev-steps)))
        (define earlier (list-ref rev-steps cycle-length))
        ;; if subsumption check passes, we're done, otherwise append it to the list of steps and continue
        (define fv (weak-seteq->seteq free-variables))
        (cond
          [(@subsumed? fv next-step effective-pc earlier effective-pc #:skip-empty-check #t)
           (dprintf "info: fixpoint found with ~a cycle setup (and ~a cycle length)~n"
                    (- (length rev-steps) cycle-length 1) cycle-length)
           (reverse rev-steps)]
          [else
           (if auto
               (loop (cons next-step rev-steps))
               (begin
                 (dprintf "next step: ~v~n does not loop back to~nearlier: ~v~ndiff: ~a~n" next-step earlier (@show-diff next-step earlier))
                 (error 'compute-fixpoint "Did not find a fixpoint")))])))

    (define (shrink-by-key s key path-condition free-vars-seteq)
      (define groups (group-by key s))
      (dprintf "info: merging, have ~a states grouped into ~a partitions~n" (length s) (length groups))
      ;; note: we pass in the free-variables converted to a seteq to minimize allocations
      (apply append (map (curry shrink-set free-vars-seteq path-condition) groups)))

    ;; aims to be sound, can't be "complete" (what is complete?)
    (define (shrink-set free-vars-seteq path-condition s)
      (dprintf "info: merging ~a states~n" (length s))
      (let loop ([pending (reverse s)]
                 [keep '()])
        (if (empty? pending)
            (begin
              (dprintf "info: merged into ~a states~n" (length keep))
              keep)
            (let ()
              (define p (first pending))
              (define pp (rest pending))
              (define represented
                (for/or ([k keep])
                  (@subsumed? free-vars-seteq p path-condition k path-condition #:skip-empty-check #t)))
              (if represented
                  (loop pp keep)
                  ;; need to add
                  (loop pp (cons p keep)))))))

    (define (run-to-next-hypercall st sync-state)
      (if (not (finished? st))
          (if (in-hypercall? (state-interpreter st))
              st ; return as-is
              (let ()
                (define st1 (@check-no-asserts (interp:step (state-interpreter st)) #:assumes (state-pc st)))
                (run-to-next-hypercall (state st1 (state-pc st) (state-equalities st) (state-spec-machine st)) sync-state)))
          ;; value
          st))

    (define (in-hypercall? st)
      (interp:uninterpreted? (interp:state-control st)))

    (define/public (run!)
      (cond
        [(and (empty? working) (empty? waiting))
         ;; if spec machines aren't finished, finish those up, and then return values
         (for/list ([st completed])
           (match-define (state interpreter pc equalities spec-machine) st)
           (define spec-machine-final (crv32:run spec-machine (parfait:spec-environment spec)))
           (state interpreter pc equalities spec-machine-final))]
        [(not (empty? working))
         ;; more "single threads" to execute
         (match-define (cons h t) working)
         (set! working t)
         (run-single! h)
         (run!)]
        [else
         ;; merge
         (if debug*-hint
             (do-debug*!)
             (merge-states!))
         (run!)]))))

(define (rev-step-n step s0 n)
  (let loop ([s s0]
             [n n])
    (if (zero? n)
        (list s)
        (let* ([ss (loop s (sub1 n))]
               [sn-1 (first ss)])
          (cons (step sn-1) ss)))))

(define (update-state-circuit st ckt)
  (if (interp:state? st)
      (interp:state
       (interp:state-control st)
       (interp:state-environment st)
       (interp:update-circuit (interp:state-globals st) ckt)
       (interp:state-continuation st))
      (interp:finished (interp:finished-value st) ckt)))

(define (equalities->bool eqt)
  (apply @&& (for/list ([(k v) (in-hash eqt)]) (@equal? k v))))
