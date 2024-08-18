module K2.Ecdsa.Lib

open Lib.IntTypes
open FStar.Ghost

// needs to be inlined, can't extract a polymorphic saturating_incr

[@(strict_on_arguments [0])]
inline_for_extraction
val saturating_incr:
    #t:inttype{unsigned t}
  -> a:int_t t SEC
  -> Pure (int_t t SEC)
    (requires True)
    (ensures fun r -> r == (if uint_v a < maxint t then incr a else a))

[@(strict_on_arguments [0])]
let saturating_incr #t a =
  let incremented = a +. uint 1 in
  let mask = eq_mask #t incremented (uint #t #SEC 0) in
  let result = logor incremented mask in
  let _: erased unit =
  if uint_v a < maxint t then begin
    logor_zeros incremented;
    incr_lemma a 
  end else
    logor_ones incremented in
  result
