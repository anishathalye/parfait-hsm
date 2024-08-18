#lang rosette/safe

(require
 "parse.rkt"
 "environment.rkt"
 "register.rkt"
 "value.rkt"
 rosutil
 (only-in racket/base values let*-values))

(provide (struct-out machine) initialize-machine)

(addressable-struct machine (registers memory))

;; Like Asm.initial_state
;;
;; But leaves program counter uninitialized. The caller will likely
;; want to add contents to memory and set some of the register values
;; before running the program.
;;
;; Returns three values:
;; - the state
;; - the environment
;; - the symbol table (a hash mapping strings to integers: not Rosette-compatible)
(define (initialize-machine paths)
  (let*-values ([(symbol-table environment) (link-and-load paths)]
                [(memory) (initialize-memory environment)]
                [(rf) (initial-regfile undef)])
    (values (machine rf memory) environment symbol-table)))
