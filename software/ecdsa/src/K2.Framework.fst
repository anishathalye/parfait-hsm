module K2.Framework

module Seq = FStar.Seq

open FStar.Ghost
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
open LowStar.BufferOps
module M = LowStar.Modifies

open Lib.IntTypes

include K2.Framework.Hacks

noeq type spec_t = {
  state_t:Type;
  command_t:Type;
  response_t:Type;
  initial_state:state_t;
  transition:state_t -> command_t -> (state_t & response_t);
}

let command_decoder (len:nat) (command_t:Type) = (s:Seq.seq uint8{Seq.length s = len}) -> option command_t

let command_encoder (#len:nat) (#command_t:Type) (decoder:command_decoder len command_t) =
  cmd:command_t ->
  Pure (s:Seq.seq uint8{Seq.length s = len})
  (requires True)
  (ensures fun ret -> decoder ret == Some cmd)

let response_decoder (len:nat) (response_t:Type) = (s:Seq.seq uint8{Seq.length s = len}) -> response_t

let response_encoder (#len:nat) (#response_t:Type) (decoder:response_decoder len response_t) =
  (r:option response_t) ->
  Pure (s:Seq.seq uint8{Seq.length s = len})
  (requires True)
  (ensures fun ret -> Some? r ==> decoder ret == Some?.v r)

let state_encoder (len:nat) (state_t:Type) (initial_state:state_t) =
  (st:state_t) ->
  Pure (s:Seq.seq uint8{Seq.length s = len})
  (requires True)
  (ensures fun ret -> st == initial_state ==> Seq.equal ret (Seq.create len (uint 0)))

inline_for_extraction
let handle_st
  (spec: spec_t)
  (#state_len:nat)
  (encode_state:state_encoder state_len spec.state_t spec.initial_state)
  (#command_len:nat)
  (#decode_command:command_decoder command_len spec.command_t)
  (encode_command:command_encoder decode_command)
  (#response_len:nat)
  (#decode_response:response_decoder response_len spec.response_t)
  (encode_response:response_encoder decode_response) =
    state:B.buffer uint8{B.length state = state_len}
  -> state_spec:erased spec.state_t
  -> command:B.buffer uint8{B.length command = command_len}
  -> cmd_spec:erased (option spec.command_t)
  -> response:B.buffer uint8{B.length response = response_len} ->
  Stack unit
  (requires fun h ->
    B.live h state /\
    B.live h command /\
    B.live h response /\
    B.disjoint state command /\
    B.disjoint command response /\
    B.disjoint state response /\
    Seq.equal (encode_state state_spec) (B.as_seq h state) /\
    decode_command (B.as_seq h command) == reveal cmd_spec
  )
  (ensures fun h0 () h1 ->
    B.live h1 state /\
    B.live h1 command /\
    B.live h1 response /\
    M.modifies (M.loc_union (M.loc_buffer state) (M.loc_buffer response)) h0 h1 /\
    (match cmd_spec with
     | Some v -> let (state_spec_final, resp_spec) = spec.transition state_spec (Some?.v cmd_spec) in
                Seq.equal (encode_state state_spec_final) (B.as_seq h1 state) /\
                Seq.equal (encode_response (Some resp_spec)) (B.as_seq h1 response)
     | None -> Seq.equal (B.as_seq h1 state) (B.as_seq h0 state) /\
              Seq.equal (encode_response None) (B.as_seq h1 response)
   ))
