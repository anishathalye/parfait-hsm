#lang rosette/safe

(require
 "value.rkt"
 "lib.rkt"
 "memory-data.rkt"
 "parameters.rkt"
 rosutil)

(provide
 freeable writable readable nonempty invalid
 (struct-out memory)
 empty-memory
 alloc free drop-perm valid-pointer? valid-pointer?*
 load store loadv storev loadbytes storebytes
 block-size)

;; These definitions are adapted mainly from CompCert/common/Memory.v.
;;
;; The memory model here is greatly simplified. We don't do fine-grained allocations or permissions.
;; Instead, all allocations start at 0, and permissions are per-block.
;; Furthermore, we don't need the distinction between current and maximum permissions,
;; because we don't support external calls here.

(define-singleton freeable) ; malloc'ed structures + the stack are freeable
(define-singleton writable) ; global variables
(define-singleton readable) ; global readonly variables
(define-singleton nonempty) ; function pointers
(define-singleton invalid)  ; deallocated memory

(define (permission? perm)
  (or (freeable? perm) (nonempty? perm) (invalid? perm)))

(define (permission<=? p1 p2)
  (cond
    [(equal? p1 p2) #t] ; reflexive
    [(invalid? p1) #t]
    [(nonempty? p1) (or (readable? p2) (writable? p2) (freeable? p2))]
    [(readable? p1) (or (writable? p2) (freeable? p2))]
    [(writable? p1) (or (freeable? p2))]
    [else #f]))

;; A memory
;;
;; Stored in reverse order, so when we allocate, we can cons onto the lists
(addressable-struct memory
                    (contents ;; listof (vectorof memval?)
                     permissions ;; listof permission?
                     next-block)) ;; integer?

(define empty-vector (vector-immutable))

(define empty-memory
  (memory (list empty-vector)
          (list invalid)
          1))

(define (block->index block next-block)
  (- next-block block 1))

(define (get-block mem block)
  (list-ref (memory-contents mem) (block->index block (memory-next-block mem))))

(define (block-size mem block)
  (vector-length (get-block mem block)))

;; returns a cons cell of the new block index and the new memory
(define (alloc mem len)
  (define block (memory-next-block mem))
  (define new-block (list->immutable-vector (repeat undef len)))
  (define new-mem
    (memory (cons new-block (memory-contents mem))
            (cons freeable (memory-permissions mem))
            (add1 block)))
  (cons block new-mem))

(define (free mem block)
  (define next-block (memory-next-block mem))
  (if (and (not (track-freed-memory)) (= block (sub1 next-block)))
      (memory (cdr (memory-contents mem))
              (cdr (memory-permissions mem))
              (sub1 next-block))
      (let* ([perms (memory-permissions mem)]
             [index (block->index block next-block)]
             [old-perm (list-ref perms index)])
        (unless (freeable? old-perm)
          (assert #f "free: block is not freeable"))
        ;; CompCert doesn't do this, but we also clear out the contents so they can be GCed;
        ;; they're never going to be accessed anyways
        (memory (list-set (memory-contents mem) index empty-vector)
                (list-set perms index invalid)
                next-block))))

(define (drop-perm mem block new-permission)
  (define next-block (memory-next-block mem))
  (define perms (memory-permissions mem))
  (define index (block->index block next-block))
  (define old-permission (list-ref perms index))
  (unless (permission<=? new-permission old-permission)
    (assert #f "drop-perm: attempting to raise permissions"))
  (memory (memory-contents mem)
          (list-set perms index new-permission)
          next-block))

;; offset is an integer?
(define (valid-pointer? mem block offset)
  (valid-access? mem chunk-int8unsigned block offset nonempty))

(define ((valid-pointer?* mem) block offset)
  (valid-pointer? mem block offset))

;; is a memory access with a given chunk size at the block, offset
;; allowed at the given permission?
;;
;; offset is an integer? (not a (bitvector 32))
(define (valid-access? mem chunk block offset permission)
  (define next-block (memory-next-block mem))
  (define index (block->index block next-block))
  (define offset-end (+ offset (chunk-size chunk))) ; one past the end of the chunk
  (cond
    ;; out of bounds block?
    [(>= block next-block) #f]
    ;; incorrect permission level?
    [(not (permission<=? permission (list-ref (memory-permissions mem) index))) #f]
    ;; invalid offset?
    [(> offset-end (vector-length (get-block mem block))) #f]
    ;; if none of the above, it's ok: in-bounds block/offset, and permissions ok
    [else #t]))

;; offset is an integer?
;;
;; returns #f if it's an invalid load
;; (rather than None, as in Coq; #f is not a value? so this is okay)
(define (load chunk mem block offset)
  (cond
    [(valid-access? mem chunk block offset readable)
     (define raw-data (vector-slice/list (get-block mem block) offset (chunk-size chunk)))
     (decode-val chunk raw-data)]
    [else #f]))

;; similar to load, but the address and offset are a pointer? value
(define (loadv chunk mem addr)
  (if (pointer? addr)
      (load chunk mem (pointer-block addr) (bitvector->natural (pointer-offset addr)))
      #f))

;; Memory.loadbytes
;;
;; returns #f if it's an invalid load
(define (loadbytes mem block offset n)
  (if (and (>= offset 0) (valid-access? mem chunk-int8unsigned block (sub1 (+ offset n)) readable))
      (vector-slice/list (get-block mem block) offset n)
      #f))

;; returns #f if it's an invalid store
;; otherwise, returns the new memory
(define (store chunk mem block offset val)
  (cond
    [(valid-access? mem chunk block offset writable)
     (let* ([encoded-value (encode-val chunk val)]
            [old-block-contents (get-block mem block)]
            [new-block-contents (vector-set-range old-block-contents offset encoded-value)]
            [index (block->index block (memory-next-block mem))]
            [new-contents (list-set (memory-contents mem) index new-block-contents)])
       (memory new-contents (memory-permissions mem) (memory-next-block mem)))]
    [else #f]))

;; similar to store, but the address and offset are a pointer? value
(define (storev chunk mem addr val)
  (if (pointer? addr)
      (store chunk mem (pointer-block addr) (bitvector->natural (pointer-offset addr)) val)
      #f))

;; Memory.storebytes
;;
;; returns #f if it's an invalid store
(define (storebytes mem block offset bytes)
  (if (and (>= offset 0) (valid-access? mem chunk-int8unsigned block (sub1 (+ offset (length bytes))) writable))
      (let* ([old-block-contents (get-block mem block)]
             [new-block-contents (vector-set-range old-block-contents offset bytes)]
             [index (block->index block (memory-next-block mem))]
             [new-contents (list-set (memory-contents mem) index new-block-contents)])
        (memory new-contents (memory-permissions mem) (memory-next-block mem)))
      #f))

(module+ test
  (require rackunit racket/match)

  (test-case "alloc/free/drop-perm and validity/permissions"
    (match-define (cons b1 m1) (alloc empty-memory 12))
    (check-equal? b1 1)
    (check-false (valid-pointer? m1 0 3))
    (match-define (cons b2 m2) (alloc m1 4))
    (check-equal? b2 2)
    (check-true (valid-pointer? m2 1 3))
    (check-true (valid-pointer? m2 1 11))
    (check-false (valid-pointer? m2 1 12))
    (check-false (valid-pointer? m2 1 13))
    (define m3 (free m2 1))
    (check-false (valid-pointer? m3 1 3))
    (check-false (valid-pointer? m3 1 11))
    (check-true (valid-access? m3 chunk-int8unsigned 2 0 writable))
    (define m4 (drop-perm m3 2 readable))
    (check-false (valid-access? m4 chunk-int8unsigned 2 0 writable))
    (check-true (valid-access? m4 chunk-int8unsigned 2 0 readable))
    (check-true (valid-access? m4 chunk-int8unsigned 2 0 nonempty))))
