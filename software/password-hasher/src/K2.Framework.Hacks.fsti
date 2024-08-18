module K2.Framework.Hacks

open Lib.IntTypes

inline_for_extraction
val xeq: #t:inttype -> #l:secrecy_level -> int_t t l -> int_t t l -> bool

inline_for_extraction
val xeq_lemma: #t:inttype
  -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> Lemma (a `xeq` b == (v a = v b))
  [SMTPat (xeq #t a b)]
