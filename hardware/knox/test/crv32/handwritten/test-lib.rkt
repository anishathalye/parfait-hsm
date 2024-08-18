#lang racket/base

(require
 crv32/parse
 crv32/environment
 crv32/machine
 crv32/register
 crv32/semantics
 crv32/value
 rackunit
 syntax/parse/define
 (prefix-in @ rosette))

(provide
 test-case ; from rackunit
 check-returns
 check-returns*)

(define-check (check-returns* expected-return paths setup)
  (check-returns-impl expected-return paths setup))

(define-check (check-returns expected-return paths)
  (check-returns-impl expected-return paths))

(define (check-returns-impl expected-return paths [setup (lambda (state environment symbol-table) state)])
  (define paths* (if (list? paths) paths (list paths)))
  (define-values (s0 environment symbol-table) (initialize-machine paths*))
  (define s1
    (if (hash-has-key? symbol-table "main")
        (machine
         (write-pc (machine-registers s0) (pointer (hash-ref symbol-table "main") (@bv 0 32)))
         (machine-memory s0))
        s0))
  (define s2 (setup s1 environment symbol-table))

  (define sf (run s2 environment))

  (define return-value (@bitvector->integer (read-ireg (machine-registers sf) a0)))

  (unless (equal? return-value expected-return)
    (with-check-info (['actual return-value]
                      ['expected expected-return])
      (fail-check))))
