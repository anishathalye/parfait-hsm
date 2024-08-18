module K2.Ecdsa.IO

open K2.Ecdsa.Spec

open K2.Framework

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
module S = FStar.Seq
module U8 = FStar.UInt8

let command_len:nat = 49

val decode_command:command_decoder command_len spec.command_t
let decode_command s =
  let tag = S.index s 0 in
  if xeq tag (uint 1) then
    let prf_key:prf_key_t = S.slice s 1 17 in
    let private_key:private_key_t = S.slice s 17 49 in
    Some (Initialize prf_key private_key)
  else if xeq tag (uint 2) then
    let message:message_t = S.slice s 1 33 in
    // note, on the encoding side, we don't need to check that the encoding is deterministic
    Some (Sign message)
  else
    None

val encode_command:command_encoder decode_command
let encode_command cmd =
  match cmd with
  | Initialize prf_key private_key ->
    let enc = S.cons (uint 1) (S.append prf_key private_key) in
    assert (S.equal (S.slice enc 1 17) prf_key);
    // assert (prf_key == uint8s_from_lseq (S.slice enc 1 17));
    assert (S.equal (S.slice enc 17 49) private_key);
    // assert (private_key == uint8s_from_lseq (S.slice enc 17 49));
    enc
  | Sign message ->
    let enc = S.cons (uint 2) (S.append message (create 16 (uint 0))) in
    assert (S.equal (S.slice enc 1 33) message);
    enc

let response_len:nat = 65

val decode_response:response_decoder response_len spec.response_t
let decode_response s =
  let tag = S.index s 0 in
  if xeq tag (uint 1) then
    Initialized
  else if xeq tag (uint 2) then
    Signature None
  else if xeq tag (uint 3) then
    let signature = S.slice s 1 65 in
    Signature (Some signature)
  else
    Initialized // will be unreachable for good inputs/outputs

val encode_response:response_encoder decode_response
let encode_response resp =
  match resp with
  | Some Initialized -> S.cons (uint 1) (create 64 (uint 0))
  | Some (Signature None) -> S.cons (uint 2) (create 64 (uint 0))
  | Some (Signature (Some signature)) ->
    let enc = S.cons (uint 3) signature in
    assert (S.equal (S.slice enc 1 65) signature);
    enc
  | None -> create 65 (uint 0)

let state_len:nat = 56

let encode_zero (): Lemma (equal (uint_to_bytes_be (uint #U64 #SEC 0)) (create (numbytes U64) (uint 0))) =
  let zero64 = uint #U64 #SEC 0 in
  let arithmetic0 (d:pos) (m:pos): Lemma (0 / d % m = 0) = () in
  let arithmetic1 (i:nat): Lemma (0 / pow2 (8 * i) % pow2 8 = 0) = arithmetic0 (pow2 (8 * i)) (pow2 8) in
  let arithmetic2 (i:nat{i < numbytes U64}): Lemma (uint #U8 #SEC (v zero64 / pow2 (8 * i) % pow2 8) == uint #U8 #SEC 0) =
    assert (v zero64 = 0);
    arithmetic1 i;
    () in
  let enc_zero64 = uint_to_bytes_be zero64 in
  index_uint_to_bytes_be zero64;
  let lemma (i:nat{i < numbytes U64}): Lemma (index enc_zero64 (numbytes U64 - i - 1) == uint #U8 #SEC 0) =
    arithmetic2 i in
  lemma 7;
  lemma 6;
  lemma 5;
  lemma 4;
  lemma 3;
  lemma 2;
  lemma 1;
  lemma 0;
  assert (forall i. index enc_zero64 i == uint #U8 #SEC 0);
  ()

val encode_state:state_encoder state_len spec.state_t spec.initial_state
let encode_state st =
  let prf_key_enc = st.prf_key in
  let prf_counter_enc: lseq uint8 8 = uint_to_bytes_be st.prf_counter in
  encode_zero ();
  let enc = S.append st.prf_key (S.append prf_counter_enc st.private_key) in
  assert (S.equal (S.slice enc 0 16) st.prf_key);
  assert (S.equal (S.slice enc 16 24) prf_counter_enc);
  assert (S.equal (S.slice enc 24 56) st.private_key);
  enc
