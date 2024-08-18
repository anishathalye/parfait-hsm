#lang rosette/safe

(require
 "value.rkt"
 "lib.rkt"
 "parameters.rkt"
 rosutil
 (only-in racket/base build-list))

(provide
 pc pc? ireg? reg?
 (struct-out regfile) initial-regfile
 read-ireg write-ireg read-pc write-pc
 zero ra sp gp tp t0 t1 t2 s0 fp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)

;; The definition of registers and the register file is adapted from CompCert/riscV/Asm.v
;;
;; Registers include the 32 integer registers, along with the program counter. We do not
;; model floating-point registers.
;; Registers map to values.

;; The program counter is represented by this singleton.

(define-singleton pc)

;; Integer registers are represented by a (bitvector 5)

(define ireg?
  (bitvector 5))

(define (reg? x)
  (or (pc? x) (ireg? x)))

;; The register file contains:
;; - iregs: a vector of length 32 of values
;; - pc: a value

(addressable-struct regfile (iregs pc))

;; initial-pc should be a pointer to the first instruction to execute
(define (initial-regfile initial-pc)
  (define iregs (list->vector (build-list 32 (lambda (i) undef))))
  (vector-set!-bv iregs sp (if (strict-compcert-semantics) nullptr undef))
  (vector-set!-bv iregs ra (if (strict-compcert-semantics) nullptr undef))
  (regfile (vector->immutable-vector iregs) initial-pc))

(define (read-ireg rf rs)
  (if (bvzero? rs) (bv 0 32) (vector-ref-bv (regfile-iregs rf) rs)))

(define (write-ireg rf rd v)
  (if (bvzero? rd)
      rf
      (regfile (vector-set-bv (regfile-iregs rf) rd v) (regfile-pc rf))))

(define (read-pc rf)
  (regfile-pc rf))

(define (write-pc rf v)
  (regfile (regfile-iregs rf) v))

(define zero (bv 0 5))
(define ra (bv 1 5))
(define sp (bv 2 5))
(define gp (bv 3 5))
(define tp (bv 4 5))
(define t0 (bv 5 5))
(define t1 (bv 6 5))
(define t2 (bv 7 5))
(define s0 (bv 8 5))
(define fp (bv 8 5))
(define s1 (bv 9 5))
(define a0 (bv 10 5))
(define a1 (bv 11 5))
(define a2 (bv 12 5))
(define a3 (bv 13 5))
(define a4 (bv 14 5))
(define a5 (bv 15 5))
(define a6 (bv 16 5))
(define a7 (bv 17 5))
(define s2 (bv 18 5))
(define s3 (bv 19 5))
(define s4 (bv 20 5))
(define s5 (bv 21 5))
(define s6 (bv 22 5))
(define s7 (bv 23 5))
(define s8 (bv 24 5))
(define s9 (bv 25 5))
(define s10 (bv 26 5))
(define s11 (bv 27 5))
(define t3 (bv 28 5))
(define t4 (bv 29 5))
(define t5 (bv 30 5))
(define t6 (bv 31 5))
