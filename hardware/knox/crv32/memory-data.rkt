#lang rosette/safe

(require
 "types.rkt"
 "value.rkt"
 "lib.rkt"
 rosutil
 rosette/lib/destruct
 (only-in racket/base error))

(provide
 byte? (struct-out fragment) memval?
 memory-chunk?
 chunk-size
 chunk-int8signed chunk-int8signed? chunk-int8unsigned chunk-int8unsigned?
 chunk-int16signed chunk-int16signed? chunk-int16unsigned chunk-int16unsigned?
 chunk-int32 chunk-int32? chunk-any32 chunk-any32?
 chunk-int64 chunk-int64? chunk-any64 chunk-any64?
 encode-val decode-val)

;; These definitions are adapted mainly from CompCert/common/Memdata.v.

(define (byte? v)
  ((bitvector 8) v))

;; A byte-sized fragment of an opaque value.
;;
;; - value: value?
;; - quantity: integer? (number of bytes this fragment is split into)
;; - n: integer?
(addressable-struct fragment (value quantity n))

(define (memval? v)
  (or (undef? v) (byte? v) (fragment? v)))

;; Adapted from CompCert/common/AST.v

(define-singleton chunk-int8signed)
(define-singleton chunk-int8unsigned)
(define-singleton chunk-int16signed)
(define-singleton chunk-int16unsigned)
(define-singleton chunk-int32)
(define-singleton chunk-any32)
(define-singleton chunk-int64)
(define-singleton chunk-any64)

(define (memory-chunk? chunk)
  (or (chunk-int8signed? chunk)
      (chunk-int8unsigned? chunk)
      (chunk-int16signed? chunk)
      (chunk-int16unsigned? chunk)
      (chunk-int32? chunk)
      (chunk-any32? chunk)
      (chunk-int64? chunk)
      (chunk-any64? chunk)))

(define (chunk-size chunk)
  (cond
    [(chunk-int8signed? chunk) 1]
    [(chunk-int8unsigned? chunk) 1]
    [(chunk-int16signed? chunk) 2]
    [(chunk-int16unsigned? chunk) 2]
    [(chunk-int32? chunk) 4]
    [(chunk-any32? chunk) 4]
    [(chunk-int64? chunk) 8]
    [(chunk-any64? chunk) 8]
    [else (assert #f "chunk-size: not a chunk")]))

(define (encode-int x nbytes [offset (* (- nbytes 1) 8)] [acc '()])
  (if (zero? nbytes)
      acc
      (encode-int x (sub1 nbytes) (- offset 8) (cons (extract (+ offset 7) offset x) acc))))

;; note: CompCert seems to use big-endian encoding (and decoding) of
;; the byte numbers here, regardless of Archi.big_endian; we follow
;; the same convention
(define (inj-value v q [i 0] [acc '()])
  (if (equal? i q)
      acc
      (inj-value v q (add1 i) (cons (fragment v q i) acc))))

;; returns a list of memval
;;
;; corresponding to Memdata.v's encode_val
;;
;; in CompCert, RISC-V is little-endian (Archi.big_endian = false)
(define (encode-val chunk v)
  (cond
    [(and (int32? v) (or (chunk-int8signed? chunk) (chunk-int8unsigned? chunk)))
     (encode-int v 1)]
    [(and (int32? v) (or (chunk-int16signed? chunk) (chunk-int16unsigned? chunk)))
     (encode-int v 2)]
    [(and (int32? v) (chunk-int32? chunk))
     (encode-int v 4)]
    [(and (pointer? v) (chunk-int32? chunk))
     (inj-value v 4)]
    ;; case we added for high-half
    [(and (high-half? v) (chunk-int32? chunk))
     (inj-value v 4)]
    [(and (int64? v) (chunk-int64? chunk))
     (encode-int v 8)]
    [(and (pointer? v) (chunk-int64? chunk))
     (repeat undef 8)]
    ;; case we added for high-half
    [(and (high-half? v) (chunk-int64? chunk))
     (repeat undef 8)]
    [(chunk-any32? chunk)
     (inj-value v 4)]
    [(chunk-any64? chunk)
     (inj-value v 8)]
    [else
     (repeat undef (chunk-size chunk) #:bound 8)]))

(define (decode-int bl)
  (apply concat (reverse bl)))

(module+ test
  (require rackunit)

  (test-case "decode-int of encode-int"
    (define-symbolic* x (bitvector 32))
    (check-pred unsat? (verify (assert (equal? (decode-int (encode-int x 4)) x))))
    (check-pred unsat? (verify (assert (equal? (decode-int (encode-int x 2)) (extract 15 0 x)))))))

(define (check-value n v q vl)
  (cond
    [(empty? vl) (zero? n)]
    [(fragment? (first vl))
     (destruct
      (first vl)
      [(fragment v* q* n*)
       (and (equal? v v*) (equal? q q*) (equal? (sub1 n) n*)
            (check-value (sub1 n) v q (rest vl)))]
      [else #f])]
    [else #f]))

;; checks and re-assembles a fragment, and if it's bad, returns undef
(define (proj-value vl q)
  (if (or (empty? vl) (not (fragment? (first vl))))
      undef
      (destruct
       (first vl)
       [(fragment v _ n) ; don't want to use q from here, use the q that was passed in
        (if (check-value q v q vl) v undef)]
       [else undef])))

;; corresponding to CompCert's Values.load_result
(define (load-result chunk v)
  (cond
    [(and (chunk-int8signed? chunk) (int32? v))
     (sign-extend (extract 7 0 v) (bitvector 32))]
    [(and (chunk-int8unsigned? chunk) (int32? v))
     (zero-extend (extract 7 0 v) (bitvector 32))]
    [(and (chunk-int16signed? chunk) (int32? v))
     (sign-extend (extract 15 0 v) (bitvector 32))]
    [(and (chunk-int16unsigned? chunk) (int32? v))
     (zero-extend (extract 15 0 v) (bitvector 32))]
    [(and (chunk-int32? chunk) (int32? v))
     v]
    [(and (chunk-int32? chunk) (pointer? v))
     v]
    ;; case we added for high-half
    [(and (chunk-int32? chunk) (high-half? v))
     v]
    [(and (chunk-int64? chunk) (int64? v))
     v]
    [(and (chunk-int64? chunk) (pointer? v))
     undef]
    ;; case we added for high-half
    [(and (chunk-int64? chunk) (high-half? v))
     undef]
    [(and (chunk-any32? chunk) (int32? v))
     v]
    [(and (chunk-any32? chunk) (pointer? v))
     v]
    ;; case we added for high-half
    [(and (chunk-any32? chunk) (high-half? v))
     v]
    [(chunk-any64? chunk)
     v]
    [else undef]))

;; corresponding to CompCert's decode_value
;;
;; takes in a list of memval and returns a val
;;
;; the caller is responsible for ensuring that (equal? (length vl) (chunk-size chunk))
(define (decode-val chunk vl)
  (define all-bytes (apply && (map byte? vl)))
  (if all-bytes
      ;; byte
      (let ([x (decode-int vl)])
        (cond
          ;; we always read the appropriate number of bytes (as given by the chunk type),
          ;; so e.g., if we load a chunk-int8signed, x will be a (bitvector 8)
          [(chunk-int8signed? chunk)
           (sign-extend x (bitvector 32))]
          [(chunk-int8unsigned? chunk)
           (zero-extend x (bitvector 32))]
          [(chunk-int16signed? chunk)
           (sign-extend x (bitvector 32))]
          [(chunk-int16unsigned? chunk)
           (zero-extend x (bitvector 32))]
          [(chunk-int32? chunk) x]
          [(chunk-int64? chunk) x]
          [(chunk-any32? chunk) undef]
          [(chunk-any64? chunk) undef]))
      ;; try to parse as fragment
      (cond
        [(or (chunk-int32? chunk) (chunk-any32? chunk))
         (load-result chunk (proj-value vl 4))]
        [(chunk-int64? chunk) undef]
        [(chunk-any64? chunk)
         (load-result chunk (proj-value vl 8))]
        [else undef])))
