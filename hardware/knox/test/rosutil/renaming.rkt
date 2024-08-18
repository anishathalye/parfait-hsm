#lang rosette/safe

(require rosutil
         rackunit)

(test-case "basic"
  (define-symbolic* x y (bitvector 32))
  (define-symbolic* z (bitvector 8))
  (define-symbolic* a b integer?)

  (check-true (equivalent-up-to-renaming x y))
  (check-false (equivalent-up-to-renaming x z))
  (check-true (equivalent-up-to-renaming
               (bvzero? x) (bvzero? y)))
  (check-false (equivalent-up-to-renaming
                (bvzero? x) (bvzero? z)))
  (check-true (equivalent-up-to-renaming
               (bvadd x y) (bvadd y x)))
  (check-false (equivalent-up-to-renaming
                (+ a 1) (+ a 2)))
  (check-true (equivalent-up-to-renaming
               (equal? a b) (equal? b a)))
  (check-true (equivalent-up-to-renaming
               (bvadd x (bvmul y y))
               (bvadd y (bvmul x x))))
  (check-false (equivalent-up-to-renaming
                (bvadd x (bvmul y x))
                (bvadd x (bvmul y y))))
  (check-false (equivalent-up-to-renaming
                (bvadd x y)
                (bvsub x y)))
  (check-true (equivalent-up-to-renaming 3 3))
  (check-true (equivalent-up-to-renaming (list 1 2 x) (list 1 2 y)))
  (check-false (equivalent-up-to-renaming x 7))
  (check-false (equivalent-up-to-renaming x (bv 3 32))))

(test-case "constant"
  (check-true (equivalent-up-to-renaming 1 1))
  (check-true (equivalent-up-to-renaming (bv 3 32) (bv 3 32)))
  (check-false (equivalent-up-to-renaming (bv 3 32) (bv 3 16)))
  (define-symbolic* x integer?)
  (check-false (equivalent-up-to-renaming 3 x))
  (check-false (equivalent-up-to-renaming x 2))
  (check-false (equivalent-up-to-renaming (bv 3 16) x)))

(test-case "expression"
  (define-symbolic* x y z integer?)
  (check-true (equivalent-up-to-renaming (+ x y) (+ y x)))
  (check-true (equivalent-up-to-renaming (+ x y z) (+ y z x)))
  (check-false (equivalent-up-to-renaming (+ x y) (+ x y z)))
  (check-true (equivalent-up-to-renaming (+ (* x y) (* x 3))
                                         (+ (* y z) (* y 3))))
  (check-false (equivalent-up-to-renaming (+ (* x y) (* x 3))
                                          (+ (* y z) (* z 3))))
  (check-false (equivalent-up-to-renaming (+ x y) (* x y))))

(test-case "union"
  (define-symbolic* p q boolean?)
  (define-symbolic* x y (bitvector 32))
  (define-symbolic* a b integer?)
  (check-true (equivalent-up-to-renaming (if p x a)
                                         (if q y b)))
  (check-false (equivalent-up-to-renaming (if p (bvzero? x) a)
                                          (if p (bvzero? (bvadd x (bv 1 32))) b))))

(test-case "list"
  (define-symbolic* a b integer?)
  (check-true (equivalent-up-to-renaming (list 1 2 a 3)
                                         (list 1 2 b 3)))
  (check-false (equivalent-up-to-renaming (list 1 2 a 3)
                                          (list 1 2 (+ a 1) 3)))
  (check-false (equivalent-up-to-renaming (list 1 2 a)
                                          (list 1 2 a b)))
  (check-false (equivalent-up-to-renaming (list 1 2 a b)
                                          (list 1 2 a))))

(test-case "cons"
  (define-symbolic* a b integer?)
  (check-true (equivalent-up-to-renaming (cons 1 a)
                                         (cons 1 b)))
  (check-true (equivalent-up-to-renaming (cons a b)
                                         (cons b a)))
  (check-false (equivalent-up-to-renaming (cons a b)
                                          (cons 1 b))))

(test-case "vector"
  (define-symbolic* a b integer?)
  (check-true (equivalent-up-to-renaming (vector 1 2 a 3)
                                         (vector 1 2 b 3)))
  (check-false (equivalent-up-to-renaming (vector 1 2 a 3)
                                          (list 1 2 b 3)))
  (check-false (equivalent-up-to-renaming (vector-immutable 1 2 a 3)
                                          (vector 1 2 b 3)))
  (check-false (equivalent-up-to-renaming (vector 1 2 a 3)
                                          (vector-immutable 1 2 b 3)))
  (check-true (equivalent-up-to-renaming (vector-immutable 1 2 a 3)
                                         (vector-immutable 1 2 b 3)))
  (check-false (equivalent-up-to-renaming (vector 1 2 a 3)
                                          (vector 1 2 (+ a 1) 3)))
  (check-false (equivalent-up-to-renaming (vector 1 2 a)
                                          (vector 1 2 a b)))
  (check-false (equivalent-up-to-renaming (vector 1 2 a b)
                                          (vector 1 2 a))))

(test-case "box"
  (define-symbolic* a b integer?)
  (check-true (equivalent-up-to-renaming (box a) (box b)))
  (check-true (equivalent-up-to-renaming (box (+ a 1)) (box (+ b 1))))
  (check-false (equivalent-up-to-renaming (box (+ a 1)) (box b)))
  (check-false (equivalent-up-to-renaming (box (+ a 1)) (cons 1 2))))

(test-case "struct"
  (define-symbolic* a b integer?)
  (struct s1 (f1 f2) #:transparent)
  (struct s2 (f3 f4) #:transparent)
  (check-true (equivalent-up-to-renaming (s1 a b) (s1 b a)))
  (check-true (equivalent-up-to-renaming (s1 a (+ b 1)) (s1 b (+ a 1))))
  (check-false (equivalent-up-to-renaming (s1 a (+ b 1)) (s1 b a)))
  (check-false (equivalent-up-to-renaming (s1 a b) (s2 b a)))
  (check-false (equivalent-up-to-renaming (s1 1 2) (s2 1 2))))
