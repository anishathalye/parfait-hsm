#lang racket/base

(require
 (prefix-in emulator: "../emulator/interpreter.rkt")
 "../result.rkt"
 (prefix-in @ (combine-in rosette/safe rosutil))
 yosys/meta
 "../circuit.rkt"
 (prefix-in parfait: (combine-in parfait/spec parfait/sync))
 "../emulator.rkt"
 racket/list racket/class racket/match)

(provide checker%
         (struct-out pairing)
         (struct-out set))

(@addressable-struct
 pairing
 (circuit
  emulator))

(@addressable-struct
 set
 (term
  predicate
  equalities
  ready-to-step
  sync-state))

(define checker%
  (class object%
    (super-new)

    (init-field spec)
    (init-field circuit)
    (init-field emulator)
    (init-field R)
    (init-field R*)
    (init-field [history #t])
    (init-field [sync-abstract #f])

    (define meta (circuit-meta circuit))

    (define (new-symbolic-input)
      (@update-field
       ((meta-new-symbolic-input (circuit-meta circuit)))
       (circuit-reset-input-name circuit)
       (not (circuit-reset-input-signal circuit))))

    (define circuit-crash+power-on-reset
      (crash+power-on-reset circuit))

    (define emulator-interpret
      (let* ([global-env (emulator:create-environment
                          spec
                          (circuit-meta circuit)
                          (emulator-bindings emulator))])
        (lambda (expr st pred) (@check-no-asserts (emulator:interpret expr st global-env)
                                             #:assumes pred
                                             #:discharge-asserts #t))))

    (define visited '())
    (define next
      (let* ([c ((meta-new-symbolic meta))]
             [f ((parfait:spec-new-symbolic-state spec))]
             [p (@&& ((meta-invariant meta) c) (@check-no-asserts (R f c)))]
             [emu (result-state (emulator-interpret '(init) (emulator:state #f f) p))])
        (list (set (pairing c emu) p (hasheq) #f #f))))

    (define checks-disabled #f)
    (define checks-ever-disabled #f)

    (define/public (disable-checks!)
      (set! checks-disabled #t)
      (set! checks-ever-disabled #t))

    (define/public (enable-checks!)
      (set! checks-disabled #f))

    (define/public (finished?)
      (and (empty? next) (not checks-ever-disabled)))

    (define/public (focused)
      (first next))

    (define/public (count-remaining)
      (length next))

    (define/public (get-next)
      next)
    (define/public (get-visited)
      visited)

    (define/public (switch-goal! num)
      (unless (< num 0)
        (define-values (h t) (split-at next num))
        (set! next (cons (car t) (append h (cdr t))))))

    (define (equalities->bool eqt)
      (apply @&& (for/list ([(k v) (in-hash eqt)]) (@equal? k v))))

    (define/public (concretize! lens #:use-equalities [use-equalities #f] #:piecewise [piecewise #f])
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      (define effective-pred (if use-equalities
                                 (@&& focus-pred (equalities->bool focus-eq))
                                 focus-pred))
      (define focus-term*
        (@lens-transform lens focus-term (lambda (view) (@concretize view effective-pred #:piecewise piecewise))))
      (set! next (cons (set focus-term* focus-pred focus-eq focus-ready sync-state) (rest next))))

    (define/public (overapproximate! lens)
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      (define focus-term*
        (@lens-transform lens focus-term (lambda (view) (@overapproximate view))))
      (set! next (cons (set focus-term* focus-pred focus-eq focus-ready sync-state) (rest next))))

    ;; lets the caller specify what to replace terms with, but we do a subsumption check
    (define/public (overapproximate*! lens view)
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      (define focus-term* (@lens-set lens focus-term view))
      (define effective-pred (@&& focus-pred (equalities->bool focus-eq)))
      (unless (or checks-disabled (@subsumed? #f focus-term effective-pred focus-term* effective-pred))
        (error 'overapproximate*! "subsumption check failed"))
      (set! next (cons (set focus-term* focus-pred focus-eq focus-ready sync-state) (rest next))))

    (define/public (overapproximate-predicate! p #:use-equalities [use-equalities #f])
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      (define effective-pred (if use-equalities
                                 (@&& focus-pred (equalities->bool focus-eq))
                                 focus-pred))
      (unless (or checks-disabled (@unsat? (@verify (@assert (@implies effective-pred p)))))
        (error 'overapproximate-predicate! "failed to prove implication of new predicate"))
      (set! next (cons (set focus-term p focus-eq focus-ready sync-state) (rest next))))

    ;; proof by subsumption
    (define/public (overapproximate-predicate*! p)
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      (define effective-pred (@&& focus-pred (equalities->bool focus-eq)))
      (define effective-new-pred (@&& p (equalities->bool focus-eq)))
      (unless (or checks-disabled (@subsumed? #f focus-term effective-pred focus-term effective-new-pred))
        (error 'overapproximate-predicate*! "subsumption check failed"))
      (set! next (cons (set focus-term p focus-eq focus-ready sync-state) (rest next))))

    (define/public (replace! lens view #:use-equalities [use-equalities #f])
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      (define current-view (@lens-view lens focus-term))
      (define effective-pred (if use-equalities
                                 (@&& focus-pred (equalities->bool focus-eq))
                                 focus-pred))
      (unless (or checks-disabled (@unsat? (@verify (@begin (@assume effective-pred) (@assert (@equal? current-view view))))))
        (error 'replace! "failed to prove equality"))
      (define focus-term* (@lens-set lens focus-term view))
      (set! next (cons (set focus-term* focus-pred focus-eq focus-ready sync-state) (rest next))))

    ;; gives circuit/emu new inputs
    (define/public (prepare!)
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      (define input (new-symbolic-input))
      (define c-with-input ((meta-with-input meta) (pairing-circuit focus-term) input))
      (define emulator-with-input (result-state (emulator-interpret `(with-input ',input) (pairing-emulator focus-term) focus-pred)))
      (set! next (cons (set (pairing c-with-input emulator-with-input) focus-pred focus-eq #t sync-state) (rest next))))

    (define/public (history! on)
      (set! history on))

    (define/public (step!)
      (unless (set-ready-to-step (first next))
        (prepare!))
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      ;; check that outputs match
      (match-define (pairing c-with-input emulator-with-input) focus-term)
      ;; not making use of focus-eq in assumption
      (unless checks-disabled
        (define c-out ((meta-get-output meta) c-with-input))
        (match-define (result emulator-out emulator-after-out) (emulator-interpret '(get-output) emulator-with-input focus-pred))
        (set! emulator-with-input emulator-after-out) ; in case the emulator updates state / calls the oracle as part of get-output
        (define outputs-equal (@equal? c-out emulator-out))
        (unless (or (eqv? outputs-equal #t) ; avoid solver query when possible
                    (@unsat? (@verify (@begin
                                       (@assume focus-pred)
                                       (@assert outputs-equal)))))
          (error 'step! "output mismatch between circuit and emulator")))
      ;; check crash/reset/recovery
      (unless checks-disabled
        #;(define c-reset (circuit-crash+power-on-reset (pairing-circuit focus-term)))
        (define c (pairing-circuit focus-term))
        (define o (emulator:state-oracle (pairing-emulator focus-term)))
        (define f (if (emulator:executing? o) (emulator:executing-persistent o) o))
        (define R-post-crash (@check-no-asserts (R* f c)))
        (define crash-model (if
                             (eqv? R-post-crash #t)
                             (@unsat) ; avoid solver query when possible
                             (@verify (@begin
                                       (@assume focus-pred)
                                       (@assert R-post-crash)))))
        (unless (@unsat? crash-model)
          (println (@evaluate f crash-model))
          (println (@evaluate c crash-model))
          (error 'step! "recovery condition does not hold")))
      (define c1 ((meta-step meta) c-with-input))
      (define emu1 (result-state (emulator-interpret '(step) emulator-with-input focus-pred)))
      (define o1 (emulator:state-oracle emu1))
      ;; oracles
      (define stepped
        (if (and sync-state (emulator:executing? o1))
            ;; need to sync
            (for/list ([res (parfait:sync c1 (emulator:executing-machine o1) sync-state spec #:verbose #t #:abstract sync-abstract)])
              (match-define (list c* s* sync-state* pred*) res)
              (set
               (pairing
                c*
                (emulator:state
                 (emulator:state-auxiliary emu1)
                 (emulator:executing (emulator:executing-persistent o1) s*)))
               (@&& focus-pred pred*)
               focus-eq
               #f
               sync-state*))
            ;; no sync
            (list
             (set
              (pairing c1 emu1)
              focus-pred
              focus-eq
              #f
              sync-state))))
      (prepare!) ; what's about to go in visited, make inputs symbolic
      (when history
        (set! visited (cons (first next) visited)))
      (set! next (append stepped (rest next))))

    (define/public (cases! preds #:use-equalities [use-equalities #f])
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      (define preds* (map (lambda (p) (@&& focus-pred p)) preds))
      (define any-split (apply @|| preds*))
      (define effective-pred (if use-equalities
                                 (@&& focus-pred (equalities->bool focus-eq))
                                 focus-pred))
      (unless (or checks-disabled (@unsat? (@verify (@assert (@implies effective-pred any-split)))))
        (error 'cases! "failed to prove exhaustiveness"))
      (define new (map (lambda (p) (set focus-term p focus-eq focus-ready sync-state)) preds*))
      (set! next (append new (rest next))))

    (define/public (admit!)
      (set! checks-ever-disabled #t)
      (set! next (rest next)))

    (define/public (begin-sync! mapping)
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      (when sync-state
        (error 'begin-sync! "already syncing"))
      (define new (set focus-term focus-pred focus-eq focus-ready (parfait:new-sync-state mapping)))
      (set! next (cons new (rest next))))

    (define/public (sync-abstract! abstract)
      (set! sync-abstract abstract))

    (define/public (syncing?)
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      sync-state)

    ;; pos is relative to end
    (define/public (subsumed! pos)
      (when (set-ready-to-step (first next))
        (error 'subsumed! "cannot do subsumption check without stepping a prepared state"))
      ;; we call prepare here because (step!) doesn't replace the inputs with new ones
      ;; and our circuit rep includes the inputs (which shouldn't really be compared)
      (prepare!)
      (match-define (set focus-term focus-pred focus-eq focus-ready focus-sync-state) (first next))
      (define focus-effective-pred (@&& focus-pred (equalities->bool focus-eq)))
      (define idx (- (length visited) pos 1))
      (match-define (set ref-term ref-pred ref-eq ref-ready ref-sync-state) (list-ref visited idx))
      (define ref-effective-pred (@&& ref-pred (equalities->bool ref-eq)))
      (unless (or checks-disabled (@subsumed? #f focus-term focus-effective-pred ref-term ref-effective-pred))
        (error 'subsumed! "subsumption check failed"))
      ;; now, we can just discard the currently focused term
      (set! next (rest next)))

    ;; another way to tie the knot
    (define/public (r-holds!)
      ;; like the crash check, except we don't crash and restart
      ;; XXX need to ensure that this isn't a zero-length loop
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      (define c (pairing-circuit focus-term))
      (define o (emulator:state-oracle (pairing-emulator focus-term)))
      (define f (if (emulator:executing? o) (emulator:executing-persistent o) o))
      (define R-v (@check-no-asserts (R f c)))
      (define crash-model (if
                           (eqv? R-v #t)
                           (@unsat) ; avoid solver query when possible
                           (@verify (@begin
                                     (@assume focus-pred)
                                     (@assert R-v)))))
      (unless (@unsat? crash-model)
        (println (@evaluate f crash-model))
        (println (@evaluate c crash-model))
        (error 'r-holds! "R does not hold"))
      (set! next (rest next)))

    (define/public (remember! lens [name #f])
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      (define current-view (@lens-view lens focus-term))
      (define current-type (@type-of current-view))
      (when (not (@solvable? current-type))
        (error 'remember! "not a solvable type"))
      (define new-var (@fresh-symbolic (or name '||) current-type))
      (define focus-term* (@lens-set lens focus-term new-var))
      (define focus-eq* (hash-set focus-eq new-var current-view))
      (set! next (cons (set focus-term* focus-pred focus-eq* focus-ready sync-state) (rest next)))
      new-var)

    (define/public (remember+! lenses [name #f])
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      (define current-view (@lens-view (first lenses) focus-term))
      (define current-type (@type-of current-view))
      (when (not (@solvable? current-type))
        (error 'remember+! "not a solvable type"))
      (for ([l (rest lenses)])
        (define same (@equal? (@lens-view l focus-term) current-view))
        ;; doesn't use pred etc, this is for terms that are equal?
        (unless (or checks-disabled (eqv? same #t) (@unsat? (@verify (@assert same))))
          (error 'remember+ "unequal terms")))
      (define new-var (@fresh-symbolic (or name '||) current-type))
      (define focus-term*
        (for/fold ([t focus-term])
                  ([l lenses])
          (@lens-set l t new-var)))
      (define focus-eq* (hash-set focus-eq new-var current-view))
      (set! next (cons (set focus-term* focus-pred focus-eq* focus-ready sync-state) (rest next)))
      new-var)

    ;; if var is not given, clears everything
    (define/public (clear! [var #f])
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      (define focus-eq* (if var
                            (hash-remove focus-eq var)
                            (hasheq)))
      (set! next (cons (set focus-term focus-pred focus-eq* focus-ready sync-state) (rest next))))

    ;; this only substitutes into the term, not into existing
    ;; equalities (though we could add another tactic for that if it's
    ;; needed)
    ;;
    ;; when var is not given, substitutes all equalities
    ;; when lens is not given, substitutes in entire term (but not predicate or equalities)
    (define/public (subst! [lens @identity-lens] #:var [var #f])
      (match-define (set focus-term focus-pred focus-eq focus-ready sync-state) (first next))
      (define focus-term*
        (@lens-transform lens focus-term (lambda (view)
                                           (if var
                                               (@substitute view var (hash-ref focus-eq var))
                                               (@substitute-terms view focus-eq)))))
      (set! next (cons (set focus-term* focus-pred focus-eq focus-ready sync-state) (rest next))))))
