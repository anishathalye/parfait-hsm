#lang racket/base

(require
 crv32/instruction crv32/parse crv32/environment
 rackunit racket/set)

;; a basic check to see that the test cases cumulatively contain every supported instruction
(test-case "instruction coverage"
  (define progs
    (list "return.json" "init_value.json" "stack.json" "goto.json" "pointer_comparison.json"
          "addl.json" "builtins.json" "implicit_memcpy.json" "popcnt_verif.json" "memory_io.json"
          (list "link1.json" "link2.json") "solve.json" "table.json" "divrem.json"
          "function_pointer.json" "shift_and_compare.json" "misc.json"))

  ;; manually taken from instruction.rkt
  (define instructions
    (set Paddiw? Paddw? Pallocframe? Pandiw? Pandw? Pbeqw? Pbgeuw? Pbgew? Pbltuw? Pbltw? Pbnew?
         Pbtbl? Pbuiltin? Pdivuw? Pdivw? Pfreeframe? Pj_l? Pj_r? Pj_s? Pjal_r? Pjal_s? Plabel?
         Plb? Plbu? Plh? Plhu? Ploadsymbol? Ploadsymbol_high? Pluiw? Plw? Plw_a? Pmulhuw? Pmulhw?
         Pmulw? Pmv? Poriw? Porw? Premuw? Premw? Psb? Pseqw? Psh? Pslliw? Psllw? Psltiuw? Psltiw?
         Psltuw? Psltw? Psnew? Psraiw? Psraw? Psrliw? Psrlw? Psubw? Psw? Psw_a? Pxoriw? Pxorw?))

  (define envs
    (for/list ([p progs])
      (define-values (st env) (link-and-load (if (list? p) p (list p))))
      env))

  (define present-instructions
    (for*/list ([env (in-list envs)]
                [def (in-list (global-environment-definitions env))]
                #:when (function-definition? def)
                [instr (in-vector (function-definition-code def))])
      instr))

  (define missing-instructions
    (for/fold ([not-found-yet instructions])
              ([instr present-instructions])
      (for/fold ([not-found-yet not-found-yet])
                ([to-check not-found-yet])
        #:final (to-check instr)
        (if (to-check instr)
            (set-remove not-found-yet to-check)
            not-found-yet))))

  (unless (set-empty? missing-instructions)
    (with-check-info (['missing-instructions missing-instructions])
      (fail-check "some instructions are missing"))))
