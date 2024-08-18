#lang rosette/safe

(require
 "value.rkt"
 "register.rkt"
 rosette/lib/destruct)

(provide
 (struct-out external-function)
 (struct-out EF_builtin)
 (struct-out EF_memcpy)
 (struct-out builtin)
 (struct-out BI_negl)
 (struct-out BI_addl)
 (struct-out BI_subl)
 (struct-out BI_mull)
 (struct-out builtin-arg)
 (struct-out BA)
 (struct-out BA_int)
 (struct-out BA_long)
 (struct-out BA_loadstack)
 (struct-out BA_addrstack)
 (struct-out BA_loadglobal)
 (struct-out BA_addrglobal)
 (struct-out BA_splitlong)
 (struct-out BA_addptr)
 (struct-out builtin-res)
 (struct-out BR)
 (struct-out BR_none)
 (struct-out BR_splitlong)
 eval-builtin
 destroyed-by-builtin)

(struct external-function () #:transparent)
;; AST.external_function
;;
;; We don't support all external functions, just the ones we need (EF_builtin and EF_memcpy)
;;
;; Rather than using string names for builtins and doing the lookup in the semantics, we do
;; the lookup at parse time.
(struct EF_builtin external-function (fn) #:transparent) ; builtin?
(struct EF_memcpy external-function (sz al) #:transparent) ; integer?, integer?

(struct builtin-arg () #:transparent)
;; AST.builtin_arg preg
(struct BA builtin-arg (x) #:transparent) ; reg?
(struct BA_int builtin-arg (n) #:transparent) ; int32?
(struct BA_long builtin-arg (n) #:transparent) ; int64?
(struct BA_loadstack builtin-arg (chunk ofs) #:transparent) ; chunk?, ptrofs?
(struct BA_addrstack builtin-arg (ofs) #:transparent) ; ptrofs?
(struct BA_loadglobal builtin-arg (chunk id ofs) #:transparent) ; chunk?, ident?, ptrofs?
(struct BA_addrglobal builtin-arg (id ofs) #:transparent) ; ident?, ptrofs?
(struct BA_splitlong builtin-arg (hi lo) #:transparent) ; builtin-arg?, builtin-arg?
(struct BA_addptr builtin-arg (a1 a2) #:transparent) ; builtin-arg?, builtin-arg?

(struct builtin-res () #:transparent)
;; AST.builtin_res preg
(struct BR builtin-res (x) #:transparent) ; reg?
(struct BR_none builtin-res () #:transparent)
(struct BR_splitlong builtin-res (hi lo) #:transparent) ; builtin-res?, builtin-res?

;; from Builtins0

(struct builtin () #:transparent)
;; chosen to match the names from CompCert: see Builtins0.standard_builtin
;;
;; We don't support all builtin functions, just the ones we need
(struct BI_addl builtin () #:transparent)
(struct BI_mull builtin () #:transparent)
(struct BI_negl builtin () #:transparent)
(struct BI_subl builtin () #:transparent)

(define (eval-builtin f vargs)
  (destruct
   f
   [(BI_addl) (value-addl (first vargs) (second vargs))]
   [(BI_mull) (value-mull* (first vargs) (second vargs))]
   [(BI_negl) (value-negl (first vargs))]
   [(BI_subl) (value-subl (first vargs) (second vargs))]
   [else (assert #f "eval-builtin: unsupported builtin")]))

;; Machregs.destroyed_by_builtin
(define (destroyed-by-builtin ef)
  (destruct
   ef
   [(EF_builtin f)
    '()]
   [(EF_memcpy sz al)
    (list t0 t1 t2)]))
