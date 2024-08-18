#lang racket/base

(require
 racket/match
 (prefix-in @ (combine-in
               rosette/safe
               (only-in rosette/base/core/bitvector [bv? bv-constant?])
               (only-in rosette/base/core/type typed? get-type type-deconstruct))))

(provide equivalent-up-to-renaming)

(define (equivalent-up-to-renaming expr1 expr2 [renaming (make-hash)])
  (define (rec children1 children2)
    (and
     (equal? (length children1) (length children2))
     (for/and ([c1 children1]
               [c2 children2])
       (equivalent-up-to-renaming c1 c2 renaming))))
  (match expr1
    [(or (? boolean?) (? integer?) (? real?) (? string?) (? symbol?) (? @bv-constant?))
     (equal? expr1 expr2)]
    [(@constant id1 type1)
     (match expr2
       [(@constant id2 type2)
        (cond
          ;; have we already decided id1 -> id2 ?
          [(hash-has-key? renaming id1)
           (equal? (hash-ref renaming id1) id2)]
          ;; do the types match?
          [(equal? type1 type2)
           ;; note that we've mapped id1 -> id2
           (hash-set! renaming id1 id2)
           #t]
          [else #f])]
       [_ #f])]
    [(@expression op1 vs1 ...)
     (match expr2
       [(@expression op2 vs2 ...)
        (and (equal? op1 op2) (rec vs1 vs2))]
       [_ #f])]
    [(@union contents1)
     (match expr2
       [(@union contents2)
        (equivalent-up-to-renaming contents1 contents2 renaming)]
       [_ #f])]
    [(list vs1 ...)
     (match expr2
       [(list vs2 ...)
        (rec vs1 vs2)]
       [_ #f])]
    [(cons x1 y1)
     (match expr2
       [(cons x2 y2)
        (and
         (equivalent-up-to-renaming x1 x2 renaming)
         (equivalent-up-to-renaming y1 y2 renaming))]
       [_ #f])]
    [(vector vs1 ...)
     (match expr2
       [(vector vs2 ...)
        (and
         (equal? (immutable? expr1) (immutable? expr2))
         (rec vs1 vs2))]
       [_ #f])]
    [(box v1)
     (match expr2
       [(box v2)
        (equivalent-up-to-renaming v1 v2 renaming)]
       [_ #f])]
    ;; custom structs
    [(and (? @typed?) (app @get-type type1))
     (match expr2
       [(and (? @typed?) (app @get-type type2))
        (and (equal? type1 type2)
             (rec (@type-deconstruct type1 expr1) (@type-deconstruct type2 expr2)))]
       [_ #f])]
    [_ #f]))
