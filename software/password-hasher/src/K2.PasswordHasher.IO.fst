module K2.PasswordHasher.IO

open K2.PasswordHasher.Spec

open K2.Framework

open Lib.IntTypes
open Lib.Sequence
open Lib.ByteSequence

open FStar.Mul
module S = FStar.Seq
module U8 = FStar.UInt8

let command_len:nat = 33

val decode_command:command_decoder command_len spec.command_t
let decode_command s =
  let tag = S.index s 0 in
  if xeq tag (uint 1) then
    let secret:secret_t = S.slice s 1 21 in
    Some (Initialize secret)
  else if xeq tag (uint 2) then
    let message:message_t = S.slice s 1 33 in
    Some (Hash message)
  else
    None

val encode_command:command_encoder decode_command
let encode_command cmd =
  match cmd with
  | Initialize secret ->
    let enc = S.cons (uint 1) (S.append secret (create 12 (uint 0))) in
    assert (S.equal (S.slice enc 1 21) secret);
    enc
  | Hash message ->
    let enc = S.cons (uint 2) message in
    assert (S.equal (S.slice enc 1 33) message);
    enc

let response_len:nat = 33

val decode_response:response_decoder response_len spec.response_t
let decode_response s =
  let tag = S.index s 0 in
  if xeq tag (uint 1) then
    Initialized
  else if xeq tag (uint 2) then
    let digest = S.slice s 1 33 in
    Hashed digest
  else
    Initialized // will be unreachable for good inputs/outputs

val encode_response:response_encoder decode_response
let encode_response resp =
  match resp with
  | Some Initialized -> S.cons (uint 1) (create 32 (uint 0))
  | Some (Hashed digest) ->
    let enc = S.cons (uint 2) digest in
    assert (S.equal (S.slice enc 1 33) digest);
    enc
  | None -> create 33 (uint 0)

let state_len:nat = 20

val encode_state:state_encoder state_len spec.state_t spec.initial_state
let encode_state st =
  st.secret
