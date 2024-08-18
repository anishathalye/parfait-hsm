module K2.Framework.Hacks

(* TODO migrate to HACL's Lib.RawIntTypes *)

open Lib.IntTypes

friend Lib.IntTypes

let xeq #t #l x y =
  x = y

let xeq_lemma #t #l x y = ()
