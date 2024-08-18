#lang rosette/safe

(require
 "types.rkt" "lib.rkt"
 rosutil)

(provide
 value? undef undef? (struct-out pointer) (struct-out high-half) nullptr
 fresh-symbolic-int32 fresh-symbolic-int64 fresh-symbolic-pointer fresh-symbolic-high-half
 offset-pointer
 value-cmpu-bool value-cmpu
 value-cmp-bool value-cmp
 value-longofwords value-loword value-hiword
 value-addl value-mull* value-mulhs value-mulhu
 value-divs-total value-divu-total value-mods-total value-modu-total
 value-negl value-subl
 value-add value-sub value-and value-or value-xor value-mul value-shr value-shru value-shl)

;; The definition of values is adapted from CompCert/common/Values.v
;;
;; We only implement a subset of values, only the ones that we need (no floating-point):
;; - Machine integer (bitvector 32)
;; - Long integer (bitvector 64)
;; - Pointer (pointer)
;; - Undefined
;;
;; Furthermore, we add a new kind of value that's not in CompCert:
;; - High half of a pointer (high-half)
;;
;; In CompCert, this is axiomatized (there's a parameter high_half, and there's an axiom
;; about how low and high halves are combined). We can't do this because we want our
;; semantics to be executable.

(define (value? v)
  (or
   (int32? v)
   (int64? v)
   (pointer? v)
   (high-half? v)
   (undef? v)))

(define (fresh-symbolic-int32) (fresh-symbolic 'v int32?))
(define (fresh-symbolic-int64) (fresh-symbolic 'v int64?))
(define (fresh-symbolic-pointer)
  (pointer
   (fresh-symbolic 'block integer?)
   (fresh-symbolic 'offset int32?)))
(define (fresh-symbolic-high-half)
  (high-half (fresh-symbolic-pointer)))

(define-singleton undef)

;; A pointer consists of:
;; - block: a positive integer
;; - offset: a ptrofs? (same as int32? but interpreted as unsigned)
(addressable-struct pointer (block offset))

(define nullptr (bv 0 32))

;; A high-half wraps a pointer
(addressable-struct high-half (pointer))

;; v is a value?
;; offset is an offset?: so either an immediate delta, or an offset-low
(define (offset-pointer v offset)
  (cond
    [(and (pointer? v) (ptrofs? offset))
     (pointer (pointer-block v) (bvadd (pointer-offset v) offset))]
    ;; our high-half case; note, we do not need to support mixing and
    ;; matching (adding a concrete delta to a high-half,
    ;; or adding an offset-low to a pointer: those can return undef,
    ;; they're not covered by CompCert's Asm.low_high_half axiom anyways
    [(and (high-half? v) (offset-low? offset))
     (let ([ptr (high-half-pointer v)])
       (if (and (equal? (pointer-block ptr) (offset-low-id offset))
                (equal? (pointer-offset ptr) (offset-low-ofs offset)))
           ;; get back the pointer if the low and high halves correspond
           ptr
           undef))]
    [else undef]))

;; Values.longofwords
(define (value-longofwords v1 v2)
  (cond
    [(and (int32? v1) (int32? v2))
     (concat v1 v2)]
    [else undef]))

;; Values.loword
(define (value-loword v)
  (cond
    [(int64? v) (extract 31 0 v)]
    [else undef]))

;; Values.hiword
(define (value-hiword v)
  (cond
    [(int64? v) (extract 63 32 v)]
    [else undef]))

;; Values.addl
(define (value-addl v1 v2)
  (cond
    [(and (int64? v1) (int64? v2)) (bvadd v1 v2)]
    [else undef]))

;; Values.subl
(define (value-subl v1 v2)
  (cond
    [(and (int64? v1) (int64? v2)) (bvsub v1 v2)]
    [else undef]))

;; Values.mull'
(define (value-mull* v1 v2)
  (cond
    [(and (int32? v1) (int32? v2))
     (bvmul (zero-extend v1 (bitvector 64)) (zero-extend v2 (bitvector 64)))]
    [else undef]))

;; Values.mulhs
(define (value-mulhs v1 v2)
  (cond
    [(and (int32? v1) (int32? v2))
     (extract 63 32 (bvmul (sign-extend v1 (bitvector 64)) (sign-extend v2 (bitvector 64))))]
    [else undef]))

;; Values.mulhu
(define (value-mulhu v1 v2)
  (cond
    [(and (int32? v1) (int32? v2))
     (extract 63 32 (bvmul (zero-extend v1 (bitvector 64)) (zero-extend v2 (bitvector 64))))]
    [else undef]))

;; Values.maketotal o Values.divs
;;
;; Rather than have Value.divs return an option, and then call maketotal on the result,
;; we combine the two into a single function.
(define (value-divs-total v1 v2)
  (cond
    [(and (int32? v1) (int32? v2))
     (if (or (bvzero? v2) (and (bveq v1 int32-min) (bveq v2 int32-mone)))
         undef
         (bvsdiv v1 v2))]
    [else undef]))

;; Values.maketotal o Values.divu
(define (value-divu-total v1 v2)
  (cond
    [(and (int32? v1) (int32? v2))
     (if (bvzero? v2)
         undef
         (bvudiv v1 v2))]
    [else undef]))

;; Values.maketotal o Values.mods
(define (value-mods-total v1 v2)
  (cond
    [(and (int32? v1) (int32? v2))
     (if (or (bvzero? v2) (and (bveq v1 int32-min) (bveq v2 int32-mone)))
         undef
         (bvsrem v1 v2))]
    [else undef]))

;; Values.maketotal o Value.modu
(define (value-modu-total v1 v2)
  (cond
    [(and (int32? v1) (int32? v2))
     (if (bvzero? v2)
         undef
         (bvurem v1 v2))]
    [else undef]))

;; Values.negl
(define (value-negl v)
  (cond
    [(int64? v) (bvneg v)]
    [else undef]))

;; Values.add
(define (value-add v1 v2)
  (cond
    [(and (int32? v1) (int32? v2)) (bvadd v1 v2)]
    [(and (pointer? v1) (int32? v2))
     (pointer (pointer-block v1) (bvadd (pointer-offset v1) v2))]
    ;; custom case for high-half: do the underlying pointer addition, and wrap back up in a high-half
    [(and (high-half? v1) (int32? v2))
     (high-half (value-add (high-half-pointer v1) v2))]
    [(and (int32? v1) (pointer? v2)) (value-add v2 v1)]
    [(and (int32? v1) (high-half? v2)) (value-add v2 v1)]
    [else undef]))

;; Values.sub
(define (value-sub v1 v2)
  (cond
    [(and (int32? v1) (int32? v2)) (bvsub v1 v2)]
    [(and (pointer? v1) (int32? v2))
     (pointer (pointer-block v1) (bvsub (pointer-offset v1) v2))]
    [(and (pointer? v1) (pointer? v2))
     (if (equal? (pointer-block v1) (pointer-block v2))
         (bvsub (pointer-offset v1) (pointer-offset v2))
         undef)]))

;; Values.mul
(define (value-mul v1 v2)
  (cond
    [(and (int32? v1) (int32? v2)) (bvmul v1 v2)]
    [else undef]))

;; Values.and
(define (value-and v1 v2)
  (cond
    [(and (int32? v1) (int32? v2)) (bvand v1 v2)]
    [else undef]))

;; Values.or
(define (value-or v1 v2)
  (cond
    [(and (int32? v1) (int32? v2)) (bvor v1 v2)]
    [else undef]))

;; Values.xor
(define (value-xor v1 v2)
  (cond
    [(and (int32? v1) (int32? v2)) (bvxor v1 v2)]
    [else undef]))

;; Values.shr
;;
;; arithmetic shift right
(define (value-shr v1 v2)
  (cond
    [(and (int32? v1) (int32? v2))
     (if (bvult v2 (bv 32 32)) ; only defined in this case
         (bvashr v1 v2)
         undef)]
    [else undef]))

;; Values.shru
;;
;; logical shift right
(define (value-shru v1 v2)
  (cond
    [(and (int32? v1) (int32? v2))
     (if (bvult v2 (bv 32 32)) ; only defined in this case
         (bvlshr v1 v2)
         undef)]
    [else undef]))

;; Values.shl
;;
;; logical shift left
(define (value-shl v1 v2)
  (cond
    [(and (int32? v1) (int32? v2))
     (if (bvult v2 (bv 32 32)) ; only defined in this case
         (bvshl v1 v2)
         undef)]
    [else undef]))

;; Values.weak_valid_ptr
(define (weak-valid-pointer? valid-pointer? block offset)
  (or (valid-pointer? block offset) (valid-pointer? block (sub1 offset))))

;; Compare two int32?s, interpreting them as unsigned
(define (int32-cmpu c x1 x2)
  (cond
    [(Ceq? c) (bveq x1 x2)]
    [(Cne? c) (! (bveq x1 x2))]
    [(Clt? c) (bvult x1 x2)]
    [(Cle? c) (bvule x1 x2)]
    [(Cgt? c) (bvugt x1 x2)]
    [(Cge? c) (bvuge x1 x2)]
    [else (assert #f "int32-cmpu: bad comparison")]))

;; Compare two int32?s, interpreting them as signed
(define (int32-cmp c x1 x2)
  (cond
    [(Ceq? c) (bveq x1 x2)]
    [(Cne? c) (! (bveq x1 x2))]
    [(Clt? c) (bvslt x1 x2)]
    [(Cle? c) (bvsle x1 x2)]
    [(Cgt? c) (bvsgt x1 x2)]
    [(Cge? c) (bvsge x1 x2)]
    [else (assert #f "int32-cmp: bad comparison")]))

(define (ptrofs-cmpu c x1 x2)
  ;; same as comparing int32s
  (int32-cmpu c x1 x2))

(define (cmp-different-blocks c)
  (cond
    [(Ceq? c) (some #f)]
    [(Cne? c) (some #t)]
    [else none]))

;; Values.of_optbool
(define (of-optbool ob)
  (cond
    [(some? ob) (if (some-value ob) (bv 1 32) (bv 0 32))]
    [else undef]))

;; Values.cmpu
(define (value-cmpu valid-pointer? comparison v1 v2)
  (of-optbool (value-cmpu-bool valid-pointer? comparison v1 v2)))

;; Values.cmpu_bool
;;
;; We pass in mem rather than the partially applied function to get valid_ptr
;;
;; Returns an option
(define (value-cmpu-bool valid-pointer? comparison v1 v2)
  (cond
    [(and (int32? v1) (int32? v2))
     (some (int32-cmpu comparison v1 v2))]
    [(and (int32? v1) (pointer? v2))
     ;; only comparison that's valid is a test that a pointer equals
     ;; (or doesn't equal) nullptr
     (if (and (equal? v1 nullptr)
              (weak-valid-pointer? valid-pointer? (pointer-block v2) (bitvector->natural (pointer-offset v2))))
         (cmp-different-blocks comparison)
         none)]
    [(and (pointer? v1) (pointer? v2))
     (let ([b1 (pointer-block v1)]
           [ofs1 (pointer-offset v1)]
           [b2 (pointer-block v2)]
           [ofs2 (pointer-offset v2)])
       (if (equal? b1 b2)
           (if (and (weak-valid-pointer? valid-pointer? b1 (bitvector->natural ofs1))
                    (weak-valid-pointer? valid-pointer? b2 (bitvector->natural ofs2)))
               (some (ptrofs-cmpu comparison ofs1 ofs2))
               none)
           (if (and (valid-pointer? b1 (bitvector->natural ofs1))
                    (valid-pointer? b2 (bitvector->natural ofs2)))
               (cmp-different-blocks comparison)
               none)))]
    [(and (pointer? v1) (int32? v2))
     (if (and (equal? v2 nullptr)
              (weak-valid-pointer? valid-pointer? (pointer-block v1) (bitvector->natural (pointer-offset v1))))
         (cmp-different-blocks comparison)
         none)]
    ;; only high-half case that we need is when we're comparing a high-half with another high-half:
    ;; not valid to compare high-half to e.g., int32
    [(and (high-half? v1) (high-half? v2))
     (value-cmpu-bool valid-pointer? comparison (high-half-pointer v1) (high-half-pointer v2))]
    [else none]))

;; Values.cmp
(define (value-cmp comparison v1 v2)
  (of-optbool (value-cmp-bool comparison v1 v2)))

;; Values.cmp_bool
(define (value-cmp-bool comparison v1 v2)
  (cond
    [(and (int32? v1) (int32? v2)) (some (int32-cmp comparison v1 v2))]
    [else none]))
