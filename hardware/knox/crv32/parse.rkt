#lang racket/base

(require
 "instruction.rkt"
 "builtins.rkt"
 "types.rkt"
 "environment.rkt"
 "register.rkt"
 "memory-data.rkt"
 (prefix-in @ rosette/safe)
 json racket/match
 (only-in racket/list range rest))

(provide link-and-load)

;; implements basic "name mangling" for static variables, combining their
;; name with the path of the file where they are defined
(define (identifier-name variable-or-function path)
  ;; is it a variable or function?
  (define is-function (hash-has-key? variable-or-function '|Fun Name|))
  (define name
    (hash-ref variable-or-function
              (if is-function '|Fun Name| '|Var Name|)))
  (define is-extern
    (equal?
     (hash-ref variable-or-function (if is-function '|Fun Storage Class| '|Var Storage Class|))
     "Extern"))
  (if is-extern
      name
      (cons name path)))

(define (add-symbol! symbol-table name value)
  (when (hash-has-key? symbol-table name)
    (error 'add-symbol! "multiple definitions of symbol ~v" name)))

;; first tries looking up static variable, otherwise falls back to extern variables
(define ((lookup-symbol symbol-table path) name)
  (define static-name (cons name path))
  (hash-ref symbol-table static-name (lambda () (hash-ref symbol-table name))))

;; updates the base table and returns the new next ident
;;
;; symbol-table is a hash, next-ident is a positive integer
;;
;; symbol table maps names to identifiers
;; but for static functions/variables, it maps (cons name filename) to the identifier
(define (update-symbol-table! asm-ast symbol-table next-ident path)
  (define functions (hash-ref asm-ast 'Functions))
  (define global-variables (hash-ref asm-ast '|Global Variables|))
  (for ([function (in-list functions)])
    (define name (identifier-name function path))
    (when (hash-has-key? symbol-table name)
      (error 'update-symbol-table! "multiple definitions of symbol ~v" name))
    (hash-set! symbol-table name next-ident)
    (set! next-ident (add1 next-ident)))
  (for ([global-variable (in-list global-variables)])
    (define name (identifier-name global-variable path))
    (when (hash-has-key? symbol-table name)
      (error 'update-symbol-table! "multiple definitions of symbol ~v" name))
    (hash-set! symbol-table name next-ident)
    (set! next-ident (add1 next-ident)))
  next-ident)

(define (parse-code instructions lookup-symbol)
  (vector->immutable-vector
   (for/vector ([instruction instructions])
     (parse-instruction instruction lookup-symbol))))

(define (regname->register x)
  (@bv (string->number (substring x 1)) 5))

(define (parse-builtin name)
  (match name
    ["__builtin_addl" (BI_addl)]
    ["__builtin_mull" (BI_mull)]
    ["__builtin_negl" (BI_negl)]
    ["__builtin_subl" (BI_subl)]
    [else (error 'parse-builtin "unsupported builtin ~v" name)]))

(define (parse-external-function ef)
  (match ef
    [(hash-table ('ExternalFunction "EF_builtin") ('Name name)) (EF_builtin (parse-builtin name))]
    [(hash-table ('ExternalFunction "EF_memcpy") ('Size sz) ('Alignment al))
     (EF_memcpy sz al)]
    [else
     (error 'parse-external-function "unsupported external function")]))

(define (parse-register r)
  (if (equal? r "pc") pc (regname->register r)))

(define (parse-chunk chunk)
  (match chunk
    ["Mint8signed" chunk-int8signed]
    ["Mint8unsigned" chunk-int8unsigned]
    ["Mint16signed" chunk-int16signed]
    ["Mint16unsigned" chunk-int16unsigned]
    ["Mint32" chunk-int32]
    ["Many32" chunk-any32]
    ["Mint64" chunk-int64]
    ["Many64" chunk-any64]
    [else (error 'parse-chunk "unsupported chunk type ~v" chunk)]))

(define (parse-builtin-arg arg lookup-symbol)
  (match arg
    [(hash-table ('Register r)) (BA (parse-register r))]
    [(hash-table ('Int i)) (BA_int (@bv i 32))]
    [(hash-table ('Long i)) (BA_long (@bv i 64))]
    [(hash-table ('LoadStack (hash-table ('Chunk chunk) ('Offset offset))))
     (BA_loadstack (parse-chunk chunk)
                   (@bv offset 32))]
    [(hash-table ('AddrStack (hash-table ('Offset offset))))
     (BA_addrstack (@bv offset 32))]
    [(hash-table ('LoadGlobal (hash-table ('Chunk chunk) ('Name name) ('Offset offset))))
     (BA_loadglobal (parse-chunk chunk) (lookup-symbol name) (@bv offset 32))]
    [(hash-table ('AddrGlobal (hash-table ('Name name) ('Offset offset))))
     (BA_addrglobal (lookup-symbol name) (@bv offset 32))]
    [(hash-table ('SplitLong (hash-table ('Hi hi) ('Lo lo))))
     (BA_splitlong (parse-builtin-arg hi lookup-symbol) (parse-builtin-arg lo lookup-symbol))]
    [(hash-table ('AddPtr (hash-table ('A1 a1) ('A2 a2))))
     (BA_addptr (parse-builtin-arg a1 lookup-symbol) (parse-builtin-arg a2 lookup-symbol))]
    [else (error 'parse-builtin-arg "unsupported builtin arg")]))

(define (parse-builtin-res res)
  (match res
    [(hash-table ('Register r)) (BR (parse-register r))]
    ["None" (BR_none)]
    [(hash-table ('SplitLong (hash-table ('Hi hi) ('Lo lo))))
     (BR_splitlong (parse-builtin-res hi) (parse-builtin-res lo))]))

(define (parse-instruction instruction lookup-symbol)
  (define name (hash-ref instruction '|Instruction Name|))
  (define args (hash-ref instruction 'Args))
  (define (get-arg n field-name)
    (hash-ref (list-ref args n) field-name))
  (define (get-register n)
    (regname->register (get-arg n 'Register)))
  (define (get-integer n)
    (get-arg n 'Integer))
  (define (get-int32 n)
    (@bv (get-integer n) 32))
  (define (get-offset n)
    (define off-arg (list-ref args n))
    (if (hash-has-key? off-arg 'Integer)
        (@bv (hash-ref off-arg 'Integer) 32)
        (let* ([off-sym-low (hash-ref off-arg 'OffsetSymbolLow)]
               [sym-name (hash-ref off-sym-low 'Name)]
               [sym-id (lookup-symbol sym-name)]
               [offset (@bv (hash-ref off-sym-low 'Offset) 32)])
          (offset-low sym-id offset))))
  (define (get-atom n)
    (lookup-symbol (get-arg n 'Atom)))
  (define (get-label n)
    (get-arg n 'ALabel))

  (match name
    ;; there's a case here for each case in instruction.rkt

    ["Pmv"
     (Pmv (get-register 0) (get-register 1))]

    ;; 32-bit integer register-immediate instructions
    ["Paddiw"
     (Paddiw (get-register 0) (get-register 1) (get-int32 2))]
    ["Psltiw"
     (Psltiw (get-register 0) (get-register 1) (get-int32 2))]
    ["Psltiuw"
     (Psltiuw (get-register 0) (get-register 1) (get-int32 2))]
    ["Pandiw"
     (Pandiw (get-register 0) (get-register 1) (get-int32 2))]
    ["Poriw"
     (Poriw (get-register 0) (get-register 1) (get-int32 2))]
    ["Pxoriw"
     (Pxoriw (get-register 0) (get-register 1) (get-int32 2))]
    ["Pslliw"
     (Pslliw (get-register 0) (get-register 1) (get-int32 2))]
    ["Psrliw"
     (Psrliw (get-register 0) (get-register 1) (get-int32 2))]
    ["Psraiw"
     (Psraiw (get-register 0) (get-register 1) (get-int32 2))]
    ["Pluiw"
     (Pluiw (get-register 0) (get-int32 1))]

    ;; 32-bit integer register-register instructions
    ["Paddw"
     (Paddw (get-register 0) (get-register 1) (get-register 2))]
    ["Psubw"
     (Psubw (get-register 0) (get-register 1) (get-register 2))]
    ["Pmulw"
     (Pmulw (get-register 0) (get-register 1) (get-register 2))]
    ["Pmulhw"
     (Pmulhw (get-register 0) (get-register 1) (get-register 2))]
    ["Pmulhuw"
     (Pmulhuw (get-register 0) (get-register 1) (get-register 2))]
    ["Pdivw"
     (Pdivw (get-register 0) (get-register 1) (get-register 2))]
    ["Pdivuw"
     (Pdivuw (get-register 0) (get-register 1) (get-register 2))]
    ["Premw"
     (Premw (get-register 0) (get-register 1) (get-register 2))]
    ["Premuw"
     (Premuw (get-register 0) (get-register 1) (get-register 2))]
    ["Psltw"
     (Psltw (get-register 0) (get-register 1) (get-register 2))]
    ["Psltuw"
     (Psltuw (get-register 0) (get-register 1) (get-register 2))]
    ["Pseqw"
     (Pseqw (get-register 0) (get-register 1) (get-register 2))]
    ["Psnew"
     (Psnew (get-register 0) (get-register 1) (get-register 2))]
    ["Pandw"
     (Pandw (get-register 0) (get-register 1) (get-register 2))]
    ["Porw"
     (Porw (get-register 0) (get-register 1) (get-register 2))]
    ["Pxorw"
     (Pxorw (get-register 0) (get-register 1) (get-register 2))]
    ["Psllw"
     (Psllw (get-register 0) (get-register 1) (get-register 2))]
    ["Psrlw"
     (Psrlw (get-register 0) (get-register 1) (get-register 2))]
    ["Psraw"
     (Psraw (get-register 0) (get-register 1) (get-register 2))]

    ;; unconditional jumps
    ["Pj_l"
     (Pj_l (get-label 0))]
    ["Pj_s"
     (Pj_s (get-atom 0))]
    ["Pj_r"
     (Pj_r (get-register 0))]
    ["Pjal_s"
     (Pjal_s (get-atom 0))]
    ["Pjal_r"
     (Pjal_r (get-register 0))]

    ;; conditional branches, 32-bit comparisons
    ["Pbeqw"
     (Pbeqw (get-register 0) (get-register 1) (get-label 2))]
    ["Pbnew"
     (Pbnew (get-register 0) (get-register 1) (get-label 2))]
    ["Pbltw"
     (Pbltw (get-register 0) (get-register 1) (get-label 2))]
    ["Pbltuw"
     (Pbltuw (get-register 0) (get-register 1) (get-label 2))]
    ["Pbgew"
     (Pbgew (get-register 0) (get-register 1) (get-label 2))]
    ["Pbgeuw"
     (Pbgeuw (get-register 0) (get-register 1) (get-label 2))]

    ;; loads and stores
    ["Plb"
     (Plb (get-register 0) (get-register 1) (get-offset 2))]
    ["Plbu"
     (Plbu (get-register 0) (get-register 1) (get-offset 2))]
    ["Plh"
     (Plh (get-register 0) (get-register 1) (get-offset 2))]
    ["Plhu"
     (Plhu (get-register 0) (get-register 1) (get-offset 2))]
    ["Plw"
     (Plw (get-register 0) (get-register 1) (get-offset 2))]
    ["Plw_a"
     (Plw_a (get-register 0) (get-register 1) (get-offset 2))]
    ["Psb"
     (Psb (get-register 0) (get-register 1) (get-offset 2))]
    ["Psh"
     (Psh (get-register 0) (get-register 1) (get-offset 2))]
    ["Psw"
     (Psw (get-register 0) (get-register 1) (get-offset 2))]
    ["Psw_a"
     (Psw_a (get-register 0) (get-register 1) (get-offset 2))]

    ;; pseudo-instructions
    ["Pallocframe"
     (Pallocframe (get-integer 0) (get-int32 1))]
    ["Pfreeframe"
     (Pfreeframe (get-integer 0) (get-int32 1))]
    ["Plabel"
     (Plabel (get-label 0))]
    ["Ploadsymbol"
     (let* ([sym (get-arg 1 'Symbol)]
            [sym-id (lookup-symbol (hash-ref sym 'Name))]
            [ofs (@bv (hash-ref sym 'Offset) 32)])
       (Ploadsymbol (get-register 0) sym-id ofs))]
    ["Ploadsymbol_high"
     (let* ([sym (get-arg 1 'Symbol)]
            [sym-id (lookup-symbol (hash-ref sym 'Name))]
            [ofs (@bv (hash-ref sym 'Offset) 32)])
       (Ploadsymbol_high (get-register 0) sym-id ofs))]
    ["Pbtbl"
     (Pbtbl (get-register 0) (map (lambda (obj) (hash-ref obj 'ALabel)) (rest args)))]
    ["Pbuiltin"
     (Pbuiltin (parse-external-function (get-arg 0 'ExternalFunction))
               (map (lambda (arg) (parse-builtin-arg arg lookup-symbol)) (get-arg 1 'Args))
               (parse-builtin-res (get-arg 2 'Res)))]

    [else (error 'parse-instruction "unsupported instruction ~v" name)]))

(define (parse-variable init-data lookup-symbol)
  (for/list ([d init-data])
    (unless (equal? (hash-count d) 1)
      (error 'parse-variable "init data has more than one key"))
    (match-define (list (cons type value)) (hash->list d))
    (match type
      ['Init_int8 (init-int8 (@bv value 8))]
      ['Init_int16 (init-int16 (@bv value 16))]
      ['Init_int32 (init-int32 (@bv value 32))]
      ['Init_int64 (init-int64 (@bv value 64))]
      ['Init_space (init-space value)]
      ['Init_addrof
       (define id (lookup-symbol (hash-ref value 'Addr)))
       (define ofs (@bv (hash-ref value 'Offset) 32))
       (init-address id ofs)])))

;; paths is a list of paths to CompCert-generated JSON dumps
;;
;; returns two values, the symbol table (mapping strings/cons to integer identifiers, for debugging)
;; and the global environment
(define (link-and-load paths)
  ;; load all the JSON ASTs
  (define asm-asts
    (for/list ([path paths])
      (hash-ref (with-input-from-file path read-json) '|Asm Ast|)))
  ;; populate symbol table
  (define symbol-table
    (for/fold ([symbol-table (make-hash)]
               [next-ident 1]
               #:result symbol-table)
              ([path paths]
               [ast asm-asts])
      (values symbol-table (update-symbol-table! ast symbol-table next-ident path))))
  ;; construct global environment
  ;;
  ;; we start off putting contents in a hash map because it's easier
  (define definitions (make-hash))
  (for ([path paths]
        [ast asm-asts])
    ;; collect function definitions
    (for ([function (hash-ref ast 'Functions)])
      (let* ([name (hash-ref function '|Fun Name|)]
             [ident ((lookup-symbol symbol-table path) name)]
             [instructions (hash-ref function '|Fun Code|)])
        (hash-set! definitions ident (function-definition (parse-code instructions (lookup-symbol symbol-table path))))))
    ;; collect variable definitions
    (for ([variable (hash-ref ast '|Global Variables|)])
      (let* ([name (hash-ref variable '|Var Name|)]
             [ident ((lookup-symbol symbol-table path) name)]
             [init-data (hash-ref variable '|Var Init|)]
             [readonly (hash-ref variable '|Var Readonly|)])
        (hash-set! definitions ident (variable-definition (parse-variable init-data (lookup-symbol symbol-table path)) readonly)))))
  ;; make the definitions a list (it's dense, and we want this to be a Rosette-compatible
  ;; data structure
  (define symbol-count (hash-count symbol-table))
  (define definitions-list
    (cons #f (for/list ([i (in-range 1 (add1 symbol-count))])
               (hash-ref definitions i))))
  (values symbol-table (global-environment definitions-list)))
