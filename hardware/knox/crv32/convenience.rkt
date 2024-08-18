#lang rosette/safe

(require
 "memory.rkt"
 "register.rkt")

(provide alloc+ write-ireg+)

;; mem: memory?
;; lengths: listof integer?
(define (alloc+ mem lengths)
  ;; we use foldr so the result order matches the lengths
  (foldr
   (lambda (len blocks-and-memory)
     (let* ([bs (car blocks-and-memory)]
            [mem1 (cdr blocks-and-memory)]
            [bm (alloc mem1 len)]
            [b (car bm)]
            [mem2 (cdr bm)])
       (cons (cons b bs) mem2)))
   (cons '() mem)
   lengths))

;; listof (cons ireg? value?)
(define (write-ireg+ rf regs-and-values)
  (foldl
   (lambda (rv rf)
     (write-ireg rf (car rv) (cdr rv)))
   rf
   regs-and-values))
