#lang racket/base

(require
 "test-lib.rkt"
 crv32/parse crv32/environment crv32/machine crv32/register crv32/semantics crv32/value
 (prefix-in @ rosette/safe)
 rackunit)

(test-case "comparing two implementations of popcnt, testing with concrete values"
  (check-returns 0 "popcnt_verif.json"))

(test-case "verify that the implementations of popcnt match"
  (define-values (s0 environment symbol-table) (initialize-machine (list "popcnt_verif.json")))
  ;; set up pc to point to verify
  (define s1
    (machine
     (write-pc (machine-registers s0) (pointer (hash-ref symbol-table "verify") (@bv 0 32)))
     (machine-memory s0)))
  ;; set up argument for verify, a symbolic
  (@define-symbolic* x (@bitvector 32))
  (define s2 (machine (write-ireg (machine-registers s1) a0 x) (machine-memory s0)))

  (define m
    (@verify
     (let* ([sf (run s2 environment)]
            [return-value (read-ireg (machine-registers sf) a0)])
       (@assert (@equal? return-value (@bv 1 32))))))

  (unless (@unsat? m)
    (with-check-info (['x (@evaluate x m)])
      (fail-check))))
