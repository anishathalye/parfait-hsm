#lang rosette/safe

(require
 crv32/lib
 rackunit)

(test-case "vector-slice/list"
    (check-equal? (vector-slice/list '#(a b c d e f) 2 3) '(c d e))
    (check-equal? (vector-slice/list '#(a b c d e f) 0 2) '(a b))
    (check-equal? (vector-slice/list '#(a b c d e f) 0 1) '(a))
    (check-equal? (vector-slice/list '#(a b c d e f) 3 0) '())
    (check-equal? (vector-slice/list '#(a b c d e f) 0 6) '(a b c d e f))
    (check-equal? (vector-slice/list '#(a b c d e f) 0 7) '(a b c d e f)))

(test-case "vector-set-range"
    (check-equal? (vector-set-range '#(a b c d e f) 0 '()) '#(a b c d e f))
    (check-equal? (vector-set-range '#(a b c d e f) 0 '(x y)) '#(x y c d e f))
    (check-equal? (vector-set-range '#(a b c d e f) 2 '(x y)) '#(a b x y e f))
    (check-equal? (vector-set-range '#(a b c d e f) 7 '(x y)) '#(a b c d e f))
    (check-equal? (vector-set-range '#(a b c d e f) 3 '(w x y z)) '#(a b c w x y)))
