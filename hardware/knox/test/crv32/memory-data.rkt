#lang rosette/safe

(require
 crv32/memory-data
 crv32/value
 rosutil
 rackunit)

(define all-chunks
  (list
   chunk-int8signed
   chunk-int8unsigned
   chunk-int16signed
   chunk-int16unsigned
   chunk-int32
   chunk-any32
   chunk-int64
   chunk-any64))
(define (choose-chunk)
  (apply choose all-chunks))

(define-check (verify-encode-decode v1 chunk1 chunk2 v2)
  (define m (verify (assert (equal? (decode-val chunk2 (encode-val chunk1 v1))
                                    v2))))
  (cond
    [(unknown? m) (fail-check "solver returned unknown")]
    [(sat? m)
     (let* ([m (complete-solution m (symbolics (list v1 chunk1 chunk2 v2)))]
            [v1 (evaluate v1 m)]
            [chunk1 (evaluate chunk1 m)]
            [chunk2 (evaluate chunk2 m)]
            [v2 (evaluate v2 m)]
            [encoded (encode-val chunk1 v1)]
            [decoded (decode-val chunk2 encoded)])
       (with-check-info (['v1 v1]
                         ['chunk1 chunk1]
                         ['chunk2 chunk2]
                         ['encoded encoded]
                         ['decoded decoded]
                         ['v2 v2])
         (fail-check)))]))

(test-case "Memdata.decode_encode_val: Vundef case"
  (define chunk1 (choose-chunk))
  (define chunk2 (choose-chunk))
  (verify-encode-decode undef chunk1 chunk2 undef))

(test-case "Memdata.decode_encode_val: Vint cases"
  (define v (fresh-symbolic-int32))
  (verify-encode-decode v chunk-int8signed chunk-int8signed
                        (sign-extend (extract 7 0 v) (bitvector 32)))
  (verify-encode-decode v chunk-int8unsigned chunk-int8signed
                        (sign-extend (extract 7 0 v) (bitvector 32)))
  (verify-encode-decode v chunk-int8signed chunk-int8unsigned
                        (zero-extend (extract 7 0 v) (bitvector 32)))
  (verify-encode-decode v chunk-int8unsigned chunk-int8unsigned
                        (zero-extend (extract 7 0 v) (bitvector 32)))
  (verify-encode-decode v chunk-int16signed chunk-int16signed
                        (sign-extend (extract 15 0 v) (bitvector 32)))
  (verify-encode-decode v chunk-int16unsigned chunk-int16signed
                        (sign-extend (extract 15 0 v) (bitvector 32)))
  (verify-encode-decode v chunk-int16signed chunk-int16unsigned
                        (zero-extend (extract 15 0 v) (bitvector 32)))
  (verify-encode-decode v chunk-int16unsigned chunk-int16unsigned
                        (zero-extend (extract 15 0 v) (bitvector 32)))
  (verify-encode-decode v chunk-int32 chunk-int32 v)
  (verify-encode-decode v chunk-any32 chunk-any32 v)
  (verify-encode-decode v chunk-any64 chunk-any64 v)
  ;; in the following, manually have to exclude chunk2 = chunk-any64; in Coq, it's ruled
  ;; out by an earlier case in the pattern match
  (define chunk-except-any64 (apply choose (filter (lambda (c) (not (chunk-any64? c))) all-chunks)))
  (verify-encode-decode v (choose chunk-int64 chunk-any64) chunk-except-any64 undef))

(test-case "Memdata.decode_encode_val: Vptr cases"
  (define v (fresh-symbolic-pointer))
  (define chunk1 (choose-chunk))
  (define chunk2 (choose-chunk))
  (verify-encode-decode v chunk1 chunk2
                        (cond
                          [(and
                            (or (chunk-int32? chunk1) (chunk-any32? chunk1))
                            (or (chunk-int32? chunk2) (chunk-any32? chunk2)))
                           v]
                          [(and
                            (chunk-int64? chunk1)
                            (or (chunk-int64? chunk2) (chunk-any64? chunk2)))
                           undef]
                          [(and (chunk-any64? chunk1) (chunk-any64? chunk2))
                           v]
                          [(and (chunk-any64? chunk1) (chunk-int64? chunk2))
                           undef]
                          [else undef])))

(test-case "Memdata.decode_encode_val: Vlong cases"
  (define v (fresh-symbolic-int64))
  (verify-encode-decode v chunk-int64 chunk-int64 v)
  (verify-encode-decode v chunk-any64 chunk-any64 v)
  (define chunk-except-*64 (apply choose (filter (lambda (c) (and (not (chunk-any64? c)) (not (chunk-int64? c)))) all-chunks)))
  (verify-encode-decode v chunk-except-*64 (choose-chunk) undef))

;; based on Vptr cases
(test-case "Memdata.decode_encode_val: high-half cases"
  (define v (fresh-symbolic-high-half))
  (define chunk1 (choose-chunk))
  (define chunk2 (choose-chunk))
  (verify-encode-decode v chunk1 chunk2
                        (cond
                          [(and
                            (or (chunk-int32? chunk1) (chunk-any32? chunk1))
                            (or (chunk-int32? chunk2) (chunk-any32? chunk2)))
                           v]
                          [(and
                            (chunk-int64? chunk1)
                            (or (chunk-int64? chunk2) (chunk-any64? chunk2)))
                           undef]
                          [(and (chunk-any64? chunk1) (chunk-any64? chunk2))
                           v]
                          [(and (chunk-any64? chunk1) (chunk-int64? chunk2))
                           undef]
                          [else undef])))
