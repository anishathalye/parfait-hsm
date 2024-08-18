#lang racket/base

(require
 "test-lib.rkt"
 crv32/parse crv32/environment crv32/machine crv32/register crv32/semantics crv32/value
 (prefix-in @ rosette/safe)
 rackunit)

(test-case "solve: sanity-check"
  (check-returns* 30000 "solve.json"
                  (lambda (st env sym)
                    (machine (write-pc
                              (write-ireg (machine-registers st) a0 (@bv 500 32))
                              (pointer (hash-ref sym "f") (@bv 0 32)))
                             (machine-memory st)))))

(test-case "6.858 lab 3 exercise 1: solve for the value of x for which f returns 1234"
  (define-values (s0 environment symbol-table) (initialize-machine (list "solve.json")))
  ;; set up argument for f, a symbolic
  (@define-symbolic* x (@bitvector 32))
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
       (@assert (@equal? return-value (@bv 1234 32))))))
  (unless (@sat? m)
    (fail-check "unsat"))
  (define x* (@evaluate (@bitvector->natural x) m))
  (unless (<= 861 x* 983)
    (with-check-info (['x x*])
      (fail-check "didn't get an expected value for x"))))
