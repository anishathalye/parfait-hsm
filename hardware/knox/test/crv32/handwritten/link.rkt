#lang racket/base

(require
 "test-lib.rkt"
 crv32/machine
 crv32/register
 (prefix-in @ rosette/safe))

(test-case "linking multiple object files"
  (check-returns* 79 (list "link1.json" "link2.json")
                  (lambda (s env st)
                    (machine (write-ireg (machine-registers s) a0 (@bv 41 32)) (machine-memory s)))))
