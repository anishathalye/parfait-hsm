#lang rosette/safe

(require
 crv32/environment
 crv32/memory
 crv32/memory-data
 crv32/value
 rackunit)

(test-case "initialize-memory: all global types"
  (define environment
    (global-environment
     (list
      ;; dummy block 0
      #f
      ;; block 1: a function
      (function-definition '()) ; empty code, don't need it for this test
      ;; block 2: a readonly region, with mixed types of init data
      (variable-definition (list (init-int8 (bv 3 8)) (init-int16 (bv 32 16))) #t)
      ;; block 3: an int32
      (variable-definition (list (init-int32 (bv #x1337 32))) #f)
      ;; block 4: an int64 list
      (variable-definition (list (init-int64 (bv #x1234 64)) (init-int64 (bv #x1111 64))) #f)
      ;; block 5: an allocation followed by free space
      (variable-definition (list (init-int8 (bv 42 8)) (init-space 7)) #f)
      ;; block 6: a readonly pointer to block 5
      (variable-definition (list (init-address 5 (bv 0 32))) #t))))
  (define init-mem (initialize-memory environment))
  (check-equal?
   init-mem
   (memory
    ;; contents
    (list
     (vector-immutable (fragment (pointer 5 (bv 0 32)) 4 3)
                       (fragment (pointer 5 (bv 0 32)) 4 2)
                       (fragment (pointer 5 (bv 0 32)) 4 1)
                       (fragment (pointer 5 (bv 0 32)) 4 0))
     (vector-immutable (bv 42 8) (bv 0 8) (bv 0 8) (bv 0 8) (bv 0 8) (bv 0 8) (bv 0 8) (bv 0 8))
     (vector-immutable (bv #x34 8) (bv #x12 8) (bv 0 8) (bv 0 8) (bv 0 8) (bv 0 8) (bv 0 8) (bv 0 8)
                       (bv #x11 8) (bv #x11 8) (bv 0 8) (bv 0 8) (bv 0 8) (bv 0 8) (bv 0 8) (bv 0 8))
     (vector-immutable (bv #x37 8) (bv #x13 8) (bv 0 8) (bv 0 8))
     (vector-immutable (bv 3 8) (bv 32 8) (bv 0 8)) ; block 2
     (vector-immutable undef) ; block 1: function pointer
     (vector-immutable)) ; block 0: dummy entry
    ;; permissions
    (list
     readable ; block 6: read-only var
     writable
     writable
     writable
     readable ; block 2: read-only var
     nonempty ; block 1: function pointer
     invalid) ; block 0
    ;; next-block
    7)))
