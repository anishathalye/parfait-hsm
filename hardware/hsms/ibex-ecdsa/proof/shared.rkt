#lang rosette/safe

(require rosutil
         "../spec/spec.rkt"
         (only-in racket/list range))

(provide AbsF R I)

(define (split32le b)
  (list
   (extract 7 0 b)
   (extract 15 8 b)
   (extract 23 16 b)
   (extract 31 24 b)))

;; gives spec state corresponding to a circuit state
(define (AbsF ci)
  ;; sizeof(struct entry) == 8 bytes, which is 2 entries in the vector
  (define fram (get-field ci 'wrapper.soc.fram.fram))
  (define active (vector-ref fram 0))
  (define active0 (bvzero? active))
  (append
   (split32le (if active0 (vector-ref fram 2) (vector-ref fram 16)))
   (split32le (if active0 (vector-ref fram 3) (vector-ref fram 17)))
   (split32le (if active0 (vector-ref fram 4) (vector-ref fram 18)))
   (split32le (if active0 (vector-ref fram 5) (vector-ref fram 19)))
   (split32le (if active0 (vector-ref fram 6) (vector-ref fram 20)))
   (split32le (if active0 (vector-ref fram 7) (vector-ref fram 21)))
   (split32le (if active0 (vector-ref fram 8) (vector-ref fram 22)))
   (split32le (if active0 (vector-ref fram 9) (vector-ref fram 23)))
   (split32le (if active0 (vector-ref fram 10) (vector-ref fram 24)))
   (split32le (if active0 (vector-ref fram 11) (vector-ref fram 25)))
   (split32le (if active0 (vector-ref fram 12) (vector-ref fram 26)))
   (split32le (if active0 (vector-ref fram 13) (vector-ref fram 27)))
   (split32le (if active0 (vector-ref fram 14) (vector-ref fram 28)))
   (split32le (if active0 (vector-ref fram 15) (vector-ref fram 29)))))

(define (R f ci)
  #;(printf "R AbsF~n  ci: ~v~n  f: ~v~n  I: ~v~n" (AbsF ci) f (I ci))
  (&&
   (equal? (AbsF ci) f)
   (I ci)))

(define (I ci)
  (bveq (get-field ci 'wrapper.pwrmgr_state) (bv #b01 2)))