#lang racket/base

(require
 "test-lib.rkt"
 crv32
 (prefix-in @ (combine-in rosette/safe rosutil))
 rackunit racket/match)

(test-case "verify dot product function, for a constant-sized vector"
  (define-values (s0 environment symbol-table) (initialize-machine (list "memory_io.json")))
  ;; set up pc
  (define s1
    (machine
     (write-pc (machine-registers s0) (pointer (hash-ref symbol-table "dot") (@bv 0 32)))
     (machine-memory s0)))

  ;; set up arguments
  (define LEN 5)
  (define (new-symbolic-vector name)
    (@vector->immutable-vector
     (@list->vector
      (build-list LEN (lambda (i) (@fresh-symbolic (format "~a[~a]" name i) (@bitvector 32)))))))
  (define a (new-symbolic-vector 'a))
  (define b (new-symbolic-vector 'b))

  ;; define spec version
  (define spec-dot-product
    (for/fold ([sum (@bv 0 32)])
              ([ai (in-vector a)]
               [bi (in-vector b)])
      (@bvadd sum (@bvmul ai bi))))

  ;; set up memory
  (define (store-vector m b o v)
    (for/fold ([m m])
              ([i (in-range (vector-length v))])
      (store chunk-int32 m b (+ o (* 4 i)) (vector-ref v i))))
  ;; let's put the vector a in its own allocation, and the vector b packed with
  ;; the result together in another allocation
  (match-define (cons (list b0 b1 b2) m1)
    (alloc+ (machine-memory s1)
            (list 7 ; extra allocation just for fun
                  (* LEN 4) ; storage for a
                  (+ (* LEN 4) 4)))) ; storage for [result, b]
  (define m2 (store-vector m1 b1 0 a))
  (define m3 (store-vector m2 b2 4 b)) ; store b starting at offset 4

  ;; set up arguments
  (define rf1 (write-ireg+ (machine-registers s1)
                           (list (cons a0 (pointer b1 (@bv 0 32))) ; addr of a
                                 (cons a1 (pointer b2 (@bv 4 32))) ; addr of b
                                 (cons a2 (@integer->bitvector LEN (@bitvector 32))) ; len
                                 (cons a3 (pointer b2 (@bv 0 32)))))) ; addr of res

  ;; define machine
  (define s2 (machine rf1 m3))

  (define m
    (@verify
     (let* ([sf (run s2 environment)]
            [res (load chunk-int32 (machine-memory sf) b2 0)])
       (@assert (@equal? res spec-dot-product)))))

  (unless (@unsat? m)
    (with-check-info (['a (@evaluate a m)]
                      ['b (@evaluate b m)])
      (fail-check))))
