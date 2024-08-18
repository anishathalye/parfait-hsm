#lang rosette/safe

(provide
 (struct-out instruction)
 (struct-out Paddiw)
 (struct-out Paddw)
 (struct-out Pallocframe)
 (struct-out Pandiw)
 (struct-out Pandw)
 (struct-out Pbeqw)
 (struct-out Pbgeuw)
 (struct-out Pbgew)
 (struct-out Pbltuw)
 (struct-out Pbltw)
 (struct-out Pbnew)
 (struct-out Pbtbl)
 (struct-out Pbuiltin)
 (struct-out Pdivuw)
 (struct-out Pdivw)
 (struct-out Pfreeframe)
 (struct-out Pj_l)
 (struct-out Pj_r)
 (struct-out Pj_s)
 (struct-out Pjal_r)
 (struct-out Pjal_s)
 (struct-out Plabel)
 (struct-out Plb)
 (struct-out Plbu)
 (struct-out Plh)
 (struct-out Plhu)
 (struct-out Ploadsymbol)
 (struct-out Ploadsymbol_high)
 (struct-out Pluiw)
 (struct-out Plw)
 (struct-out Plw_a)
 (struct-out Pmulhuw)
 (struct-out Pmulhw)
 (struct-out Pmulw)
 (struct-out Pmv)
 (struct-out Poriw)
 (struct-out Porw)
 (struct-out Premuw)
 (struct-out Premw)
 (struct-out Psb)
 (struct-out Pseqw)
 (struct-out Psh)
 (struct-out Pslliw)
 (struct-out Psllw)
 (struct-out Psltiuw)
 (struct-out Psltiw)
 (struct-out Psltuw)
 (struct-out Psltw)
 (struct-out Psnew)
 (struct-out Psraiw)
 (struct-out Psraw)
 (struct-out Psrliw)
 (struct-out Psrlw)
 (struct-out Psubw)
 (struct-out Psw)
 (struct-out Psw_a)
 (struct-out Pxoriw)
 (struct-out Pxorw))

(struct instruction () #:transparent)

;; instruction names are chosen to match the names from CompCert, even though
;; they don't match Racket's naming conventions
;;
;; These come from compcert.riscV.Asm.instruction

(struct Pmv instruction (rd rs) #:transparent) ; ireg? ireg?

;; 32-bit integer register-immediate instructions
(struct Paddiw instruction (rd rs imm) #:transparent) ; ireg? ireg? int32?
(struct Psltiw instruction (rd rs imm) #:transparent) ; ireg? ireg? int32?
(struct Psltiuw instruction (rd rs imm) #:transparent) ; ireg? ireg? int32?
(struct Pandiw instruction (rd rs imm) #:transparent) ; ireg? ireg? int32?
(struct Poriw instruction (rd rs imm) #:transparent) ; ireg? ireg? int32?
(struct Pxoriw instruction (rd rs imm) #:transparent) ; ireg? ireg? int32?
(struct Pslliw instruction (rd rs imm) #:transparent) ; ireg? ireg? int32?
(struct Psrliw instruction (rd rs imm) #:transparent) ; ireg? ireg? int32?
(struct Psraiw instruction (rd rs imm) #:transparent) ; ireg? ireg? int32?
(struct Pluiw instruction (rd imm) #:transparent) ; ireg? int32?

;; 32-bit integer register-register instructions
(struct Paddw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Psubw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Pmulw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Pmulhw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Pmulhuw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Pdivw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Pdivuw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Premw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Premuw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Psltw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Psltuw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Pseqw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Psnew instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Pandw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Porw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Pxorw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Psllw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Psrlw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?
(struct Psraw instruction (rd rs1 rs2) #:transparent) ; ireg? ireg? ireg?

;; 64-bit integer register-immediate instructions: we don't implement these

;; 64-bit integer register-register instructions: we don't implement these

;; unconditional jumps
(struct Pj_l instruction (lbl) #:transparent) ; label?
(struct Pj_s instruction (id) #:transparent) ; ident?
(struct Pj_r instruction (r) #:transparent) ; ireg?
(struct Pjal_s instruction (id) #:transparent) ; ident?
(struct Pjal_r instruction (r) #:transparent) ; ireg?

;; conditional branches, 32-bit comparisons
(struct Pbeqw instruction (rs1 rs2 lbl) #:transparent) ; ireg? ireg? label?
(struct Pbnew instruction (rs1 rs2 lbl) #:transparent) ; ireg? ireg? label?
(struct Pbltw instruction (rs1 rs2 lbl) #:transparent) ; ireg? ireg? label?
(struct Pbltuw instruction (rs1 rs2 lbl) #:transparent) ; ireg? ireg? label?
(struct Pbgew instruction (rs1 rs2 lbl) #:transparent) ; ireg? ireg? label?
(struct Pbgeuw instruction (rs1 rs2 lbl) #:transparent) ; ireg? ireg? label?

;; conditional branches, 64-bit comparisons: we don't implement these

;; loads and stores
(struct Plb instruction (rd ra ofs) #:transparent) ; ireg? ireg? offset?
(struct Plbu instruction (rd ra ofs) #:transparent) ; ireg? ireg? offset?
(struct Plh instruction (rd ra ofs) #:transparent) ; ireg? ireg? offset?
(struct Plhu instruction (rd ra ofs) #:transparent) ; ireg? ireg? offset?
(struct Plw instruction (rd ra ofs) #:transparent) ; ireg? ireg? offset?
(struct Plw_a instruction (rd ra ofs) #:transparent) ; ireg? ireg? offset?
;; Pld: we don't implement this (no 64-bit)
;; Pld_a: we don't implement this (no 64-bit)
(struct Psb instruction (rs ra ofs) #:transparent) ; ireg? ireg? offset?
(struct Psh instruction (rs ra ofs) #:transparent) ; ireg? ireg? offset?
(struct Psw instruction (rs ra ofs) #:transparent) ; ireg? ireg? offset?
(struct Psw_a instruction (rs ra ofs) #:transparent) ; ireg? ireg? offset?
;; Psd: we don't implement this (no 64-bit)
;; Psd_a: we don't implement this (no 64-bit)

;; Pfmv: floating point register move: we don't implement this

;; 32-bit (single-precision) floating point: we don't implement these

;; 64-bit (double-precision) floating point: we don't implement these

;; pseudo-instructions
(struct Pallocframe instruction (sz pos) #:transparent) ; integer? ptrofs?
(struct Pfreeframe instruction (sz pos) #:transparent) ; integer? ptrofs?
(struct Plabel instruction (lbl) #:transparent) ; label?
(struct Ploadsymbol instruction (rd id ofs) #:transparent) ; ireg? ident? ptrofs?
(struct Ploadsymbol_high instruction (rd id ofs) #:transparent) ; ireg? ident? ptrofs?
;; Ploadli: we don't implement this (no 64-bit)
;; Ploadfi: we don't implement this (no floating point)
;; Ploadsi: we don't implement this (no floating point)
(struct Pbtbl instruction (r tbl) #:transparent) ; ireg?, listof label?
(struct Pbuiltin instruction (ef args res) #:transparent) ; external-function?, listof builtin-arg?, builtin-res?
