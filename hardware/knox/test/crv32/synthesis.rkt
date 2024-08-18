#lang rosette/safe

(require
 crv32 crv32/instruction crv32/types crv32/memory crv32/environment
 rosette/lib/angelic
 rackunit)

(define (instruction??)
  ;; rather than using all registers, let's just use a0 (x10) -- a7 (x17) (which are caller-saved)
  (define (symbolic-register)
    (define-symbolic* r (bitvector 3))
    (bvadd (bv 10 5) (zero-extend r (bitvector 5))))
  (define rd (symbolic-register))
  (define rs (symbolic-register))
  (define rs1 (symbolic-register))
  (define rs2 (symbolic-register))
  (define-symbolic* imm12* (bitvector 12))
  (define imm12 (sign-extend imm12* int32?))
  (define-symbolic* shamt* (bitvector 5))
  (define shamt (zero-extend shamt* (bitvector 32)))
  (define-symbolic* imm20* (bitvector 20))
  (define imm20 (zero-extend imm20* (bitvector 32))) ; CompCert semantics do the (imm << 12)

  ;; only considering register-immediate and integer-register, and:
  ;; - no nonlinear arithmetic
  ;; - no unconditional jumps
  ;; - no conditional branches
  ;; - no loads and stores
  ;; - no pseudo-instructions
  (choose*
   ;; register-immediate instructions
   (Paddiw rd rs imm12)
   (Psltiw rd rs imm12)
   (Psltiuw rd rs imm12)
   (Pandiw rd rs imm12)
   (Poriw rd rs imm12)
   (Pxoriw rd rs imm12)
   (Pslliw rd rs shamt)
   (Psrliw rd rs shamt)
   (Psraiw rd rs shamt)
   (Pluiw rd imm20)
   ;; register-register instructions
   (Paddw rd rs1 rs2)
   (Psubw rd rs1 rs2)
   #;(Pmulw rd rs1 rs2)
   #;(Pmulhw rd rs1 rs2)
   #;(Pmulhuw rd rs1 rs2)
   #;(Pdivw rd rs1 rs2)
   #;(Premw rd rs1 rs2)
   (Psltw rd rs1 rs2)
   (Psltuw rd rs1 rs2)
   #;(Pseqw rd rs1 rs2)
   #;(Psnew rd rs1 rs2)
   (Pandw rd rs1 rs2)
   (Porw rd rs1 rs2)
   (Psllw rd rs1 rs2)
   (Psrlw rd rs1 rs2)
   (Psraw rd rs1 rs2)))

(define (prog?? fuel)
  (list->vector
   (let rec ([fuel fuel])
     (if (= fuel 0) (list (Pj_r ra))
         (cons (instruction??) (rec (sub1 fuel)))))))

(define code (prog?? 2))

(define env (global-environment (list #f (function-definition code))))

(define mem
  (let* ([m0 (cdr (alloc empty-memory 1))]
         [m1 (drop-perm m0 1 nonempty)])
    m1))

(define-symbolic* xa0 int32?)

(define rf
  (let* ([rf0 (initial-regfile (pointer 1 (bv 0 32)))]
         [rf1 (write-ireg rf0 a0 xa0)])
    rf1))

(define m0 (machine rf mem))

(test-case "load constant"
  (define (spec x)
    (bv #xdeadbeef 32))

  (define solution
    (synthesize
     #:forall m0
     #:guarantee
     (begin
       (define m1 (run m0 env))
       (assert (equal? (read-ireg (machine-registers m1) a0)
                       (spec xa0))))))

  (check-pred sat? solution))

(test-case "multiply by 17 (doable)"
  (define (spec x)
    (bvmul x (bv 17 32)))

  (define solution
    (synthesize
     #:forall m0
     #:guarantee
     (begin
       (define m1 (run m0 env))
       (assert (equal? (read-ireg (machine-registers m1) a0)
                       (spec xa0))))))

  (check-pred sat? solution))

(test-case "multiply by 18 (not doable)"
  (define (spec x)
    (bvmul x (bv 18 32)))

  (define solution
    (synthesize
     #:forall m0
     #:guarantee
     (begin
       (define m1 (run m0 env))
       (assert (equal? (read-ireg (machine-registers m1) a0)
                       (spec xa0))))))

  (check-pred unsat? solution))
