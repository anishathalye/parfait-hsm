#lang rosette/safe

(require rosutil)

(provide
 block? ident? label? int32? int64? ptrofs? (struct-out offset-low) offset?
 Ceq Ceq? Cne Cne? Clt Clt? Cle Cle? Cgt Cgt? Cge Cge?
 int32-min int32-mone)

(define block? integer?)

(define ident? integer?)

(define label? integer?)

(define int32? (bitvector 32))

(define int32-min (bv #x80000000 32))
(define int32-mone (bv -1 32))

(define int64? (bitvector 64))

(define ptrofs? (bitvector 32)) ; interpreted as unsigned

;; - id is an ident, a positive integer?
;; - ofs is a ptrofs?
(struct offset-low (id ofs) #:transparent)

(define (offset? v)
  (or
   (ptrofs? v)
   (offset-low? v)))

;; compcert.lib.Integers.comparison
(define-singleton Ceq)
(define-singleton Cne)
(define-singleton Clt)
(define-singleton Cle)
(define-singleton Cgt)
(define-singleton Cge)
