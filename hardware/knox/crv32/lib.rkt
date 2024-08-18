#lang rosette/safe

(require rosutil)

(provide
 repeat vector-set vector-set-bv list->immutable-vector vector-slice/list vector-set-range
 none none? (struct-out some))

;; allows specifying a bound, so that if n is a symbolic expression, symbolic evaluation
;; will not diverge
(define (repeat v n [acc '()] #:bound [bound #f])
  (if (and bound (<= bound 0))
      acc
      (if (zero? n) acc (repeat v (sub1 n) (cons v acc) #:bound (and bound (sub1 bound))))))

(define (vector-set vec pos val)
  (let ([vec-copy (list->vector (vector->list vec))])
    (vector-set! vec-copy pos val)
    (vector->immutable-vector vec-copy)))

(define (vector-set-bv vec pos val)
  (let ([vec-copy (list->vector (vector->list vec))])
    (vector-set!-bv vec-copy pos val)
    (vector->immutable-vector vec-copy)))

(define (list->immutable-vector l)
  (vector->immutable-vector (list->vector l)))

;; take n elements (or as many as possible), starting at pos
(define (vector-slice/list vec pos n [acc '()])
  (cond
    [(zero? n) acc]
    [(> (+ pos n) (vector-length vec)) (vector-slice/list vec pos (sub1 n) acc)] ; just ignore this out-of-bounds element
    [else
     (let ([elt (vector-ref vec (sub1 (+ pos n)))])
       (vector-slice/list vec pos (sub1 n) (cons elt acc)))]))

;; vals is a list of values
(define (vector-set-range vec pos vs)
  (let ([vec-copy (list->vector (vector->list vec))])
    (let rec ([pos pos]
              [vs vs])
      (unless (or (empty? vs) (>= pos (vector-length vec)))
        (vector-set! vec-copy pos (first vs))
        (rec (add1 pos) (rest vs))))
    (vector->immutable-vector vec-copy)))

;; for when we need an option type
;;
;; most of the time, we can just use a union type with #f,
;; though this none/some is especially useful for an option bool
(define-singleton none)
(addressable-struct some (value))
