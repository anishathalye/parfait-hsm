#lang rosette/safe

(require "memory.rkt" "memory-data.rkt" "value.rkt" "types.rkt")

(provide
 (struct-out init-data)
 (struct-out init-int8)
 (struct-out init-int16)
 (struct-out init-int32)
 (struct-out init-int64)
 (struct-out init-space)
 (struct-out init-address)
 (struct-out global-definition)
 (struct-out variable-definition)
 (struct-out function-definition)
 (struct-out global-environment)
 initialize-memory)

;; The definition of global environment is adapted from CompCert/common/Globalenvs.v
;;
;; A global environment has:
;; - A mapping from block to definition (globdef: a Gfun or Gvar)
;;
;; The CompCert GENV.t also has some other components, including a mapping from symbol to block,
;; but as far as I understand, the code relies on an identity mapping here anyways:
;; Globalenvs.add_globals allocates the symbol to block mappings sequentially starting at 1,
;; and later, Globalenvs.init_mem relies on the behavior that the memory allocates sequentially
;; starting with block 1. For this reason, we don't track the mapping at all (it's the identity).
;;
;; Globals consist of (as defined in CompCert/common/AST.v):
;; - Function definitions
;; - Global variable (descriptions; the memory itself is separate)
;;     - CompCert/riscV/Asm.v uses the unit type for extra information
;;       gvar_info attached to variables; so we only need init data, readonly,
;;       and volatile

(struct init-data () #:transparent)

(struct init-int8 init-data (v) #:transparent) ;; (bitvector 8)
(struct init-int16 init-data (v) #:transparent) ;; (bitvector 16)
(struct init-int32 init-data (v) #:transparent) ;; (bitvector 32)
(struct init-int64 init-data (v) #:transparent) ;; (bitvector 64)
(struct init-space init-data (v) #:transparent) ;; integer?
(struct init-address init-data (id ofs) #:transparent) ;; integer? int32?

(define (init-data-size id)
  (cond
    [(init-int8? id) 1]
    [(init-int16? id) 2]
    [(init-int32? id) 4]
    [(init-int64? id) 8]
    [(init-address? id) 4]
    [(init-space? id) (max (init-space-v id) 0)]
    [else (assert #f "init-data-size: not an init-data")]))

(struct global-definition () #:transparent)

(struct variable-definition global-definition (init-data readonly) #:transparent) ;; listof initdata?, boolean?

(struct function-definition global-definition (code) #:transparent) ;; vectorof instruction?

;; The global environment
;;
;; We want to use Rosette-friendly data structures here, so we don't use
;; hash maps; rather, we use lists. Symbols/blocks (the integer identifiers,
;; which are also block numbers thanks to an identity mapping) start at 1 and
;; are dense, and we can choose block numbers with the same property.
;;
;; We store a sentinel value (#f) at index 0; the code should never access this.
(struct global-environment
  (definitions) #:transparent) ; maps a block (integer?) to a definition

;; Globalenvs.store_zeros
(define (store-zeros mem block offset n)
  (if (<= n 0)
      mem
      (let ([mem* (store chunk-int8unsigned mem block offset (bv 0 32))])
        (and mem* (store-zeros mem* block (add1 offset) (sub1 n))))))

;; Globalenvs.store_init_data
(define (store-init-data mem block offset id)
  (cond
    [(init-int8? id) (store chunk-int8unsigned mem block offset (zero-extend (init-int8-v id) int32?))]
    [(init-int16? id) (store chunk-int16unsigned mem block offset (zero-extend (init-int16-v id) int32?))]
    [(init-int32? id) (store chunk-int32 mem block offset (init-int32-v id))]
    [(init-int64? id) (store chunk-int64 mem block offset (init-int64-v id))]
    ;; for init-address, the id is the identifier/symbol, but the pointer takes the block number;
    ;; thanks to the identity mapping, these are the same
    [(init-address? id) (store chunk-int32 mem block offset (pointer (init-address-id id) (init-address-ofs id)))]
    [(init-space? id) mem])) ; just reserving space, no need to write data

;; Globalenvs.store_init_data_list
(define (store-init-data-list mem block offset ids)
  (if (empty? ids)
      mem
      (let* ([id (first ids)]
             [ids* (rest ids)]
             [mem* (store-init-data mem block offset id)])
        (and mem* (store-init-data-list mem* block (+ offset (init-data-size id)) ids*)))))

;; Globalenvs.alloc_global.
(define (alloc-global mem gd)
  (cond
    [(function-definition? gd)
     (let* ([r (alloc mem 1)]
            [b (car r)]
            [m (cdr r)])
       (drop-perm m b nonempty))]
    [(variable-definition? gd)
     (let* ([id (variable-definition-init-data gd)]
            [sz (apply + (map init-data-size id))]
            [r (alloc mem sz)]
            [b (car r)]
            [m1 (cdr r)]
            [m2 (store-zeros m1 b 0 sz)])
       (and m2 ; if m2 is #f, return #f
            (let ([m3 (store-init-data-list m2 b 0 id)])
              (and m3
                   (drop-perm m3 b (if (variable-definition-readonly gd) readable writable))))))]))

;; Globalenvs.alloc_globals
(define (alloc-globals mem gds)
  (if (empty? gds)
      mem
      (let ([mem* (alloc-global mem (first gds))])
        (and mem* (alloc-globals mem* (rest gds))))))

(define (initialize-memory environment)
  ;; skip dummy entry
  (alloc-globals empty-memory (rest (global-environment-definitions environment))))
