#lang racket/base

(require
 "test-lib.rkt"
 crv32/parse crv32/environment crv32/machine crv32/register crv32/semantics crv32/value
 (prefix-in @ (combine-in rosette/safe rosutil))
 rackunit)

(test-case "branch table"
  (check-returns 821 "table.json"))

(test-case "branch table symbolic solving"
  (define-values (s0 environment symbol-table) (initialize-machine (list "table.json")))
  ;; set up argument for f, a symbolic
  (define x (@zero-extend (@fresh-symbolic 'x (@bitvector 8)) (@bitvector 32)))
  ;; set a0 register and set up pc to point to f
  (define s1
    (machine
     (write-ireg
      (write-pc (machine-registers s0) (pointer (hash-ref symbol-table "f") (@bv 0 32)))
      a0
      x)
     (machine-memory s0)))

  (define m
    (@solve
     (let* ([sf (run s1 environment)]
            [return-value (read-ireg (machine-registers sf) a0)])
       (@assert (@equal? return-value (@bv 805 32))))))
  (unless (@sat? m)
    (fail-check "unsat"))
  (define x* (@evaluate (@bitvector->natural x) m))
  (unless (= x* 66)
    (with-check-info (['x x*])
      (fail-check "didn't get an expected value for x"))))
