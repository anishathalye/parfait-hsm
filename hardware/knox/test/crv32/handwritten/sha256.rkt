#lang racket/base

(require
 "test-lib.rkt"
 crv32/parse crv32/environment crv32/machine crv32/register crv32/semantics crv32/value crv32/memory crv32/memory-data
 (prefix-in @ (combine-in rosette/safe rosutil))
 rackunit racket/match)

(define BENCHMARK #f)

(test-case "sha256 on concrete input"
  (define-values (s0 environment symbol-table) (initialize-machine (list "sha256_main.json" "sha256.json")))
  ;; set up pc
  (define s1
    (machine
     (write-pc (machine-registers s0) (pointer (hash-ref symbol-table "main") (@bv 0 32)))
     (machine-memory s0)))

  ;; set up arguments
  (define msg (list (@bv #x68 8) (@bv #x65 8) (@bv #x6c 8) (@bv #x6c 8) (@bv #x6f 8)))
  (define ITER (if BENCHMARK 100 1)) ; set to a high number for benchmarking

  (define m1 (machine-memory s1))
  (match-define (cons b1 m2) (alloc m1 (length msg))) ; storage for msg
  (match-define (cons b2 m3) (alloc m2 32)) ; storage for out
  (define m4 (storebytes m3 b1 0 msg))

  ;; set up arguments
  (define rf1
    (for/fold ([rf (machine-registers s1)])
              ([reg (list a0 a1 a2 a3)]
               [val (list (pointer b1 (@bv 0 32)) ; addr of msg
                          (@integer->bitvector (length msg) (@bitvector 32)) ; len
                          (pointer b2 (@bv 0 32)) ; addr of out
                          (@bv ITER 32))]) ; count
      (write-ireg rf reg val)))

  ;; define machine
  (define s2 (machine rf1 m4))
  (define sf ((if BENCHMARK run* run) s2 environment))
  (define res (apply @concat (loadbytes (machine-memory sf) b2 0 32)))

  ;; sha256("hello")
  (check-equal? res (@bv #x2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824 256)))

(test-case "sha256 on symbolic input"
  (define-values (s0 environment symbol-table) (initialize-machine (list "sha256_main.json" "sha256.json")))
  ;; set up pc
  (define s1
    (machine
     (write-pc (machine-registers s0) (pointer (hash-ref symbol-table "main") (@bv 0 32)))
     (machine-memory s0)))

  ;; set up arguments
  (define LEN 5)
  (define msg (build-list LEN (lambda (i) (@fresh-symbolic (format "msg[~a]" i) (@bitvector 8)))))
  (define ITER (if BENCHMARK 100 1)) ; set to a high number for benchmarking

  (define m1 (machine-memory s1))
  (match-define (cons b1 m2) (alloc m1 LEN)) ; storage for msg
  (match-define (cons b2 m3) (alloc m2 32)) ; storage for out
  (define m4 (storebytes m3 b1 0 msg))

  ;; set up arguments
  (define rf1
    (for/fold ([rf (machine-registers s1)])
              ([reg (list a0 a1 a2 a3)]
               [val (list (pointer b1 (@bv 0 32)) ; addr of msg
                          (@integer->bitvector (length msg) (@bitvector 32)) ; len
                          (pointer b2 (@bv 0 32)) ; addr of out
                          (@bv ITER 32))]) ; count
      (write-ireg rf reg val)))

  ;; define machine
  (define s2 (machine rf1 m4))
  (define sf ((if BENCHMARK run* run) s2 environment))
  (define res (loadbytes (machine-memory sf) b2 0 32))

  ;; check that it's all defined?
  (for ([b res])
    (check-pred (@bitvector 8) b))

  ;; plug in "hello" for the input and evaluate the output
  (define m (@solve (@assert (@equal? (@apply @concat msg) (@bv #x68656c6c6f 40)))))
  (define res-concrete (@evaluate (@apply @concat res) m))
  (check-equal? res-concrete (@bv #x2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824 256)))
