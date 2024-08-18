#lang rosette/safe

(require
 crv32/memory crv32/value crv32/lib crv32/types
 rosutil
 rackunit)

(test-case "value-cmpu-bool"
  (let* ([mem (cdr (alloc (cdr (alloc empty-memory 4)) 8))]
         [valid-pointer? (valid-pointer?* mem)])
    ;; int32? int32?
    (check-equal? (value-cmpu-bool valid-pointer? Ceq (bv 3 32) (bv 5 32)) (some #f))
    (check-equal? (value-cmpu-bool valid-pointer? Clt (bv 3 32) (bv 5 32)) (some #t))
    (check-equal? (value-cmpu-bool valid-pointer? Clt (bv 5 32) (bv 3 32)) (some #f))
    ;; int32? pointer?
    (check-equal? (value-cmpu-bool valid-pointer? Clt (bv 7 32) (pointer 1 (bv 0 32))) none)
    (check-equal? (value-cmpu-bool valid-pointer? Cne (bv 7 32) (pointer 1 (bv 0 32))) none)
    (check-equal? (value-cmpu-bool valid-pointer? Clt (bv 0 32) (pointer 1 (bv 0 32))) none)
    (check-equal? (value-cmpu-bool valid-pointer? Ceq (bv 0 32) (pointer 1 (bv 0 32))) (some #f))
    (check-equal? (value-cmpu-bool valid-pointer? Cne (bv 0 32) (pointer 1 (bv 0 32))) (some #t))
    (check-equal? (value-cmpu-bool valid-pointer? Clt (bv 0 32) (pointer 1 (bv 0 32))) none)
    ;; pointer? int32?
    (check-equal? (value-cmpu-bool valid-pointer? Clt (pointer 2 (bv 0 32)) (bv 7 32)) none)
    (check-equal? (value-cmpu-bool valid-pointer? Cne (pointer 2 (bv 0 32)) (bv 7 32)) none)
    (check-equal? (value-cmpu-bool valid-pointer? Clt (pointer 2 (bv 0 32)) (bv 0 32)) none)
    (check-equal? (value-cmpu-bool valid-pointer? Ceq (pointer 2 (bv 0 32)) (bv 0 32)) (some #f))
    (check-equal? (value-cmpu-bool valid-pointer? Cne (pointer 2 (bv 0 32)) (bv 0 32)) (some #t))
    (check-equal? (value-cmpu-bool valid-pointer? Clt (pointer 2 (bv 0 32)) (bv 0 32)) none)
    ;; pointer? pointer?
    (check-equal? (value-cmpu-bool valid-pointer? Clt (pointer 1 (bv 0 32)) (pointer 1 (bv 1 32))) (some #t))
    (check-equal? (value-cmpu-bool valid-pointer? Clt (pointer 1 (bv 0 32)) (pointer 1 (bv 4 32))) (some #t))
    (check-equal? (value-cmpu-bool valid-pointer? Cge (pointer 1 (bv 2 32)) (pointer 1 (bv 2 32))) (some #t))
    (check-equal? (value-cmpu-bool valid-pointer? Cge (pointer 1 (bv 2 32)) (pointer 2 (bv 2 32))) none)
    (check-equal? (value-cmpu-bool valid-pointer? Ceq (pointer 1 (bv 2 32)) (pointer 2 (bv 2 32))) (some #f))
    (check-equal? (value-cmpu-bool valid-pointer? Cne (pointer 1 (bv 2 32)) (pointer 2 (bv 2 32))) (some #t))
    ;; high-half? high-half?
    (check-equal? (value-cmpu-bool valid-pointer? Ceq (high-half (pointer 2 (bv 0 32))) (high-half (pointer 2 (bv 0 32)))) (some #t))
    (check-equal? (value-cmpu-bool valid-pointer? Ceq (high-half (pointer 2 (bv 3 32))) (high-half (pointer 2 (bv 3 32)))) (some #t))
    (check-equal? (value-cmpu-bool valid-pointer? Ceq (high-half (pointer 2 (bv 9 32))) (high-half (pointer 2 (bv 9 32)))) none)
    (check-equal? (value-cmpu-bool valid-pointer? Ceq (high-half (pointer 3 (bv 0 32))) (high-half (pointer 3 (bv 0 32)))) none)))
