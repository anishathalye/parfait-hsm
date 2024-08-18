#lang rosette/safe

(require
 crv32/memory crv32/memory-data crv32/value
 rosutil
 rackunit
 racket/set racket/match)

(test-case "loads and stores"
  (match-define (cons b1 m1) (alloc empty-memory 10))
  (define m2 (store chunk-int32 m1 1 2 (bv #x1234A678 32)))
  (check-equal? (load chunk-int32 m2 1 2) (bv #x1234A678 32))
  (check-equal? (load chunk-int32 m2 1 0) undef) ; because bytes 0 and 1 are undef
  (define m3 (store chunk-int16unsigned m2 1 0 (bv 0 32))) ; initialize it
  (check-equal? (load chunk-int32 m3 1 0) (bv #xA6780000 32))
  (check-equal? (load chunk-int16unsigned m3 1 2) (bv #x0000A678 32))
  (check-equal? (load chunk-int16signed m3 1 2) (bv #xFFFFA678 32))
  (match-define (cons b2 m4) (alloc m3 12))
  (check-false (store chunk-int32 m3 2 10 (bv 0 32)))
  (define m5 (store chunk-int32 m4 2 8 (pointer 1 (bv 1 32))))
  (check-equal? (load chunk-int8unsigned m5 2 8) undef)
  (check-equal? (load chunk-int32 m5 2 8) (pointer 1 (bv 1 32)))
  (check-equal? (load chunk-any32 m5 2 8) (pointer 1 (bv 1 32)))
  (define m6 (store chunk-int32 m5 2 0 (high-half (pointer 1 (bv 1 32)))))
  (check-equal? (load chunk-int32 m6 2 0) (high-half (pointer 1 (bv 1 32)))))

(test-case "symbolic load blocks and offsets"
  (define v (fresh-symbolic-pointer))
  (define m1 (cdr (alloc (cdr (alloc empty-memory 10)) 12)))
  (define m2 (store chunk-int32 m1 2 3 v))
  (define m3 (store chunk-int32 m2 2 5 (bv #x12345678 32))) ; clobber pointer
  (define m4 (store chunk-int32 m3 2 6 v)) ; save another copy that's intact
  (define-symbolic* block offset integer?)
  ;; let's see if we can find the location that contains the pointer
  (define m (solve (assert (equal? (load chunk-int32 m4 block offset) v))))
  (check-equal? (evaluate block m) 2)
  (check-equal? (evaluate offset m) 6))

(test-case "symbolic store blocks and offsets"
  (define v (fresh-symbolic-pointer))
  (define m1 (cdr (alloc (cdr (alloc empty-memory 10)) 12)))
  (define m2 (store chunk-int32 m1 2 3 v))
  (define-symbolic* block offset integer?)
  ;; the following adds to vc (block and offset need to be reasonable), so we capture it
  (define r (with-vc (store chunk-int16signed m2 block offset (bv #x12345678 32))))
  (define m3 (result-value r))
  (define p (result-state r))
  ;; let's see if we can find all locations that clobbers the pointer, but is not the same address as the pointer
  (define r2 (with-vc (and p (equal? (load chunk-int32 m3 2 3) undef))))
  (check-pred unsat? (verify (result-state r2))) ; dismiss this
  (define ret-eq-undef (result-value r2))
  (define clobber-locations
    (all-values (cons block offset) ret-eq-undef))
  (check-equal? (list->set clobber-locations) (set (cons 2 2) (cons 2 3) (cons 2 4) (cons 2 5) (cons 2 6))))

(test-case "loadv and storev"
  (define m1 (cdr (alloc (cdr (alloc empty-memory 10)) 12)))
  (define addr (fresh-symbolic-pointer))
  ;; values that fit in 32 bits
  (define v (choose (fresh-symbolic-int32) (fresh-symbolic-pointer) (fresh-symbolic-high-half) undef))
  (define chunk (choose chunk-int32 chunk-any32))
  ;; loading and storing at the same place should return the same value
  (define m
    (verify
     (begin
       (assume (or (and (equal? (pointer-block addr) 1) (bvult (pointer-offset addr) (bv 7 32)))
                   (and (equal? (pointer-block addr) 2) (bvult (pointer-offset addr) (bv 9 32)))))
       (define m2 (storev chunk m1 addr v))
       (define v* (loadv chunk m2 addr))
       (assert (equal? v v*)))))
  (check-pred unsat? m))
