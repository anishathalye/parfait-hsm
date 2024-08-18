#lang racket/base

(require
 "test-lib.rkt"
 crv32
 (prefix-in @ rosette/safe)
 rackunit)

(define (run-and-get-return-value)
  (define-values (s0 environment symbol-table) (initialize-machine (list "use_after_free.json")))
  (define s1
    (machine
     (write-pc (machine-registers s0) (pointer (hash-ref symbol-table "main") (@bv 0 32)))
     (machine-memory s0)))
  (define sf (run s1 environment))
  (read-ireg (machine-registers sf) a0))

(test-case "use after free, tracking freed memory"
  (parameterize ([track-freed-memory #t])
    (check-exn #rx"failed to load" (lambda () (run-and-get-return-value))))
  (@clear-vc!))

(test-case "use after free, tracking freed memory"
  (parameterize ([track-freed-memory #f])
    (check-equal? (run-and-get-return-value) (@bv 10045 32))))
