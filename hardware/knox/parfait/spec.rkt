#lang racket/base

(require
 (prefix-in @ (combine-in rosette/safe rosutil))
 crv32)

(provide
 (struct-out spec) make-spec)

(struct spec
  (handle ; state, cmd -> machine
  environment
  get-state
  get-response
  init-state
  new-symbolic-state
  new-symbolic-command
  new-symbolic-response)
  #:transparent)

;; sources is a list of paths, generated using (define-runtime-path-list ...)
(define (make-spec sources main state-length command-length response-length)
  (define-values (m0 environment symbol-table)
    (initialize-machine sources))
  ;; set up memory, allocate memory for command, state, and result
  (define bsmem1 (alloc+ (machine-memory m0)
                         (list command-length state-length response-length)))
  (define mem1 (cdr bsmem1))
  (define blocks (car bsmem1))
  (define command-block (car blocks))
  (define state-block (cadr blocks))
  (define result-block (caddr blocks))
  ;; set up registers, pc + args
  (define rf1
    (write-ireg+ (write-pc (machine-registers m0) (pointer (hash-ref symbol-table main) (@bv 0 32)))
                 (list (cons a0 (pointer state-block (@bv 0 32)))
                       (cons a1 (pointer command-block (@bv 0 32)))
                       (cons a2 (pointer result-block (@bv 0 32))))))
  ;; function that takes state/command and returns a machine that's ready to go
  (define (handle state command)
    (define mem2 (storebytes mem1 command-block 0 command))
    (define mem3 (storebytes mem2 state-block 0 state))
    (machine rf1 mem3))
  ;; getters for final results
  (define (get-state m)
    (loadbytes (machine-memory m) state-block 0 state-length))
  (define (get-response m)
    (loadbytes (machine-memory m) result-block 0 response-length))
  ;; constructors
  (define init-state
    (build-list state-length (lambda (i) (@bv 0 8))))
  (define (new-symbolic-state)
    (build-list state-length (lambda (i) (@fresh-symbolic (format "state[~a]" i) (@bitvector 8)))))
  (define (new-symbolic-command)
    (build-list command-length (lambda (i) (@fresh-symbolic (format "command[~a]" i) (@bitvector 8)))))
  (define (new-symbolic-response)
    (build-list response-length (lambda (i) (@fresh-symbolic (format "response[~a]" i) (@bitvector 8)))))

  (spec handle environment get-state get-response init-state new-symbolic-state new-symbolic-command new-symbolic-response))
