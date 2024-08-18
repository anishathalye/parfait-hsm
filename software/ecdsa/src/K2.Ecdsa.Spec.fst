module K2.Ecdsa.Spec

open K2.Framework

open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes

open Spec.P256
open Spec.Agile.HMAC
open Spec.Hash.Definitions

module S = FStar.Seq

let prf_key_t = lseq uint8 16
let private_key_t = lseq uint8 32
let message_t = lseq uint8 32
let signature_t = lseq uint8 64

noeq type state_t = {
  prf_key:prf_key_t;
  prf_counter:uint64;
  private_key:private_key_t;
}

let state_init:state_t = {
  prf_key = S.create 16 (uint 0);
  prf_counter = uint 0;
  private_key = S.create 32 (uint 0);
}

noeq type command_t =
| Initialize : new_prf_key:prf_key_t -> new_private_key:private_key_t -> command_t
| Sign : message:message_t -> command_t

noeq type response_t =
| Initialized : response_t
| Signature : maybe_signature:option signature_t -> response_t

let transition (state:state_t) (cmd:command_t) : state_t & response_t =
  match cmd with
  | Initialize prf_key private_key ->
    { prf_key = prf_key; prf_counter = uint 0; private_key = private_key }, Initialized

  | Sign message ->
    let response =
      if uint_v state.prf_counter < maxint U64 then
      // a subtle detail here: if we get "unlucky" with the nonce,
      // we'll return an error to the caller, and the caller will have to try again
      let nonce = hmac SHA2_256 state.prf_key (uint_to_bytes_be state.prf_counter) in
      let signature = ecdsa_signature_agile NoHash _ message state.private_key nonce in
      Signature signature
    else
      Signature None in
    let next_counter = if uint_v state.prf_counter < maxint U64 then
      incr state.prf_counter
    else
      state.prf_counter in
    { state with prf_counter = next_counter }, response

let spec:spec_t = {
  state_t = state_t;
  command_t = command_t;
  response_t = response_t;
  initial_state = state_init;
  transition = transition;
}
