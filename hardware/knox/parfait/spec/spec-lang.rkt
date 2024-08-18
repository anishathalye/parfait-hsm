#lang rosette/safe

(require
 "../spec.rkt"
 (only-in racket/runtime-path define-runtime-path-list)
 (for-syntax racket/base racket/syntax syntax/parse))

(provide
 (except-out (all-from-out rosette/safe) #%module-begin)
 (rename-out [$#%module-begin #%module-begin]))

(define-syntax ($#%module-begin stx)
  (syntax-parse stx
    [(_
      #:sources source:str ...+
      #:main main:str
      #:state-length state-length:number
      #:command-length command-length:number
      #:response-length response-length:number)
     #:with spec (format-id stx "spec")
     #`(#%module-begin
        ;; so it's resolved relative to the importer, not this macro
        #,(datum->syntax stx
                         (syntax-e #'(define-runtime-path-list sources (list source ...)))
                         stx)
        (define spec
          (make-spec sources main state-length command-length response-length))
        (provide spec))]))
