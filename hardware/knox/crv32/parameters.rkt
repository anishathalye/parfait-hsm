#lang racket/base

(provide
 track-freed-memory
 strict-compcert-semantics)

;; Garbage collect freed memory? CompCert's memory model
;; doesn't re-use the block number for previously allocated memory,
;; which lets the semantics e.g., catch use-after-free bugs. But we're
;; mostly interested in reasoning about C code that's already verified to
;; be free of such low-level bugs (e.g., by extraction from Low* code).
;; The real benefit of doing this is that even under symbolic branching
;; where there are different numbers of function calls in the branches,
;; it keeps the memory representation free of symbolic unions, which
;; prevents blowup.

(define track-freed-memory
  (make-parameter #f
                  (lambda (v)
                    (unless (boolean? v)
                      (raise-argument-error 'track-freed-memory "boolean?" v))
                    v)))

;; Strictly follow CompCert semantics? We make certain other tweaks
;; for ease of use, which shouldn't make any difference in program
;; behavior:
;;
;; - Initialize SP and RA to undef instead of nullptr
;;
;; This parameter must be set before initializing a machine.

(define strict-compcert-semantics
  (make-parameter #f
                  (lambda (v)
                    (unless (boolean? v)
                      (raise-argument-error 'strict-compcert-semantics "boolean?" v))
                    v)))
