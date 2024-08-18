#lang racket/base

(require
 "test-lib.rkt"
 crv32 crv32/memory
 (prefix-in @ (combine-in rosette/safe rosutil))
 rackunit)

(track-freed-memory #f)

;; not tracking freed memory really helps out Rosette here; if we don't do this,
;; this test takes time exponential in ALLOC-SIZE

(test-case "symbolic execution of branching followed by different function calls"
  (define ALLOC-SIZE 20)

  (define-values (s0 environment symbol-table) (initialize-machine (list "branch_stack_merge.json")))
  (define bm1 (alloc (machine-memory s0) ALLOC-SIZE))
  (define b1 (car bm1))
  (define m1 (cdr bm1))
  (define s1
    (machine
     (write-pc (machine-registers s0) (pointer (hash-ref symbol-table "main") (@bv 0 32)))
     m1))
  (@define-symbolic* xa0 xa1 (@bitvector 32))
  (define s2 (machine
              (write-ireg+ (machine-registers s1)
                           (list (cons a0 xa0)
                                 (cons a1 xa1)))
              (machine-memory s1)))

  (define sf (@check-no-asserts (run s2 environment)))
  (define mf (machine-memory sf))
  (define return-value (read-ireg (machine-registers sf) a0))

  ;; if we track freed memory, this takes exponential time and fails the check-no-asserts
  (@check-no-asserts (loadbytes mf b1 0 ALLOC-SIZE))

  (define m
    (@verify
     (@assert (@equal? return-value
                       (@if (@|| (@! (@bvzero? xa0)) (@! (@bvzero? xa1))) (@bv 1 32) (@bv 2 32))))))

  (unless (@unsat? m)
    (with-check-info (['xa0 (@evaluate xa0 m)]
                      ['xa1 (@evaluate xa1 m)]
                      ['return-value (@evaluate return-value m)])
      (fail-check))))
