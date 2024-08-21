#lang racket/base

(require
 "checker.rkt"
 (only-in racket/class new send)
 (prefix-in @ (combine-in rosette/safe rosutil))
 (for-syntax racket/base racket/syntax syntax/parse))

(provide
 (except-out
  (all-from-out racket/base)
  #%module-begin)
 (rename-out [$#%module-begin #%module-begin])
 (struct-out pairing)
 (struct-out set))

(define-syntax ($#%module-begin stx)
  (syntax-parse stx
    [(_
      #:spec spec-module
      #:circuit circuit-module
      #:emulator emulator-module
      #:R R:expr
      #:R* R*:expr
      (~optional (~seq #:skip-final-check skip-final-check:boolean) #:defaults ([skip-final-check #'#f]))
      (~seq k:keyword v:expr) ... ;; these are ignored for now
      body ...)
     #:with spec (format-id stx "spec")
     #:with circuit (format-id stx "circuit")
     #:with emulator (format-id stx "emulator")
     #:with R_ (format-id stx "R")
     #:with R*_ (format-id stx "R*")
     #:with /... (quote-syntax ...)
     (define (wrap proof name [method-name #f])
       #`(define-syntax #,name
           (syntax-parser
             [(_ arg /...)
              #'(send #,proof #,(or method-name name) arg /...)])))
     #`(#%module-begin
        (require
         (only-in spec-module spec)
         (only-in circuit-module circuit)
         (only-in emulator-module emulator))
        (@gc-terms!)
        (define proof (new checker%
                           [spec spec]
                           [circuit circuit]
                           [emulator emulator]
                           [R_ R]
                           [R*_ R*]))
        #,@(for/list ([elem
                       ;; all proof methods exposed here
                       (list
                        'disable-checks!
                        'enable-checks!
                        'admit!
                        'finished?
                        (cons 'current 'focused)
                        (cons 'next 'get-next)
                        (cons 'visited 'get-visited)
                        (cons 'count 'count-remaining)
                        'switch-goal!
                        'concretize!
                        'overapproximate!
                        'overapproximate*!
                        'overapproximate-predicate!
                        'overapproximate-predicate*!
                        'replace!
                        'prepare!
                        'step!
                        'cases!
                        'subsumed!
                        'r-holds!
                        'remember!
                        'remember+!
                        'clear!
                        'subst!
                        'history!
                        'begin-sync!
                        'sync-abstract!
                        'syncing?)])
             (if (pair? elem)
                 (wrap #'proof (format-id stx "~a" (car elem)) (format-id stx "~a" (cdr elem)))
                 (wrap #'proof (format-id stx "~a" elem) (format-id stx "~a" elem))))
        body ...
        (cond
          [skip-final-check (printf "debug mode: skipping final check\n")]
          [(not (send proof finished?)) (error 'verify-security "proof is not finished")]))]))
