module K2.PasswordHasher.Impl

module S = FStar.Seq
module SS = Lib.Sequence

open FStar.Ghost
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies

module HMAC = Hacl.HMAC
open Lib.IntTypes
open Lib.Buffer
module BS = Lib.ByteSequence
open Lib.ByteBuffer
open LowStar.BufferOps

open K2.PasswordHasher.Spec
open K2.PasswordHasher.IO
open K2.Framework

// hugely important for getting proofs to go through:
#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

val do_none:
    state:B.buffer uint8{B.length state = state_len}
  -> command:B.buffer uint8{B.length command = command_len}
  -> response:B.buffer uint8{B.length response = response_len} ->
  Stack unit
  (requires fun h0 ->
    B.live h0 state /\
    B.live h0 command /\
    B.live h0 response /\
    B.disjoint response state /\
    decode_command (B.as_seq h0 command) == None
  )
  (ensures fun h0 () h1 ->
    M.modifies (M.loc_union (M.loc_buffer state) (M.loc_buffer response)) h0 h1 /\
    S.equal (B.as_seq h1 state) (B.as_seq h0 state) /\
    S.equal (encode_response None) (B.as_seq h1 response))
let do_none state command response =
  let zero:uint8 = uint 0 in
  memset #_ #33ul response zero 33ul

val do_initialize_write_response:
    response:B.buffer uint8{B.length response = response_len} ->
    Stack unit
    (requires fun h0 ->
      B.live h0 response)
    (ensures fun h0 () h1 ->
      M.modifies (M.loc_buffer response) h0 h1 /\
      S.equal (encode_response (Some Initialized)) (B.as_seq h1 response))

let do_initialize_write_response response =
  let zero:uint8 = uint 0 in
  memset #_ #33ul response zero 33ul;
  response.(0ul) <- uint 1;
  let h1 = ST.get () in
  assert (S.equal (encode_response (Some Initialized)) (B.as_seq h1 response))

val do_initialize_initialize_state:
    state:B.buffer uint8{B.length state = state_len}
  -> state_spec:erased spec.state_t
  -> state_spec_final:erased spec.state_t
  -> state_spec_final_enc:erased (s:S.seq uint8{S.length s = state_len})
  -> command:B.buffer uint8{B.length command = command_len}
  -> cmd_spec:erased spec.command_t ->
  Stack unit
  (requires fun h0 ->
    B.live h0 state /\
    B.live h0 command /\
    B.disjoint state command /\
    decode_command (B.as_seq h0 command) == Some (reveal cmd_spec) /\
    Initialize? cmd_spec /\
    reveal state_spec_final == fst (spec.transition state_spec cmd_spec) /\
    reveal state_spec_final_enc == encode_state state_spec_final)
  (ensures fun h0 () h1 ->
    M.modifies (M.loc_buffer state) h0 h1 /\
    S.equal (B.as_seq h1 state) state_spec_final_enc)

let do_initialize_initialize_state state state_spec state_spec_final state_spec_final_enc command cmd_spec =
  B.blit command 1ul state 0ul 20ul

val do_initialize:
    state:B.buffer uint8{B.length state = state_len}
  -> state_spec:erased spec.state_t
  -> command:B.buffer uint8{B.length command = command_len}
  -> cmd_spec:erased spec.command_t
  -> response:B.buffer uint8{B.length response = response_len} ->
  Stack unit
  (requires fun h0 ->
    B.live h0 state /\
    B.live h0 command /\
    B.live h0 response /\
    B.disjoint state command /\
    B.disjoint command response /\
    B.disjoint state response /\
    S.equal (encode_state state_spec) (B.as_seq h0 state) /\
    decode_command (B.as_seq h0 command) == Some (reveal cmd_spec) /\
    Initialize? cmd_spec
  )
  (ensures fun h0 () h1 ->
    (M.modifies (M.loc_union (M.loc_buffer state) (M.loc_buffer response)) h0 h1) /\
    (let (state_spec_final, resp_spec) = spec.transition state_spec cmd_spec in
      S.equal (encode_state state_spec_final) (B.as_seq h1 state) /\
      S.equal (encode_response (Some resp_spec)) (B.as_seq h1 response))
  )

let do_initialize state state_spec command cmd_spec response = 
  let spec_result: erased _ = hide (spec.transition state_spec cmd_spec) in
  let state_spec_final: erased state_t = hide (fst spec_result) in
  let resp_spec: erased response_t = hide (snd spec_result) in
  let state_spec_final_enc: erased (s:S.seq uint8{S.length s = state_len}) = hide (encode_state state_spec_final) in
  let new_secret: erased _ = Initialize?.secret cmd_spec in
  
  do_initialize_write_response response;
  do_initialize_initialize_state state state_spec state_spec_final state_spec_final_enc command cmd_spec

val do_hash:
    state:B.buffer uint8{B.length state = state_len}
  -> state_spec:erased spec.state_t
  -> command:B.buffer uint8{B.length command = command_len}
  -> cmd_spec:erased spec.command_t
  -> response:B.buffer uint8{B.length response = response_len} ->
  Stack unit
  (requires fun h0 ->
    B.live h0 state /\
    B.live h0 command /\
    B.live h0 response /\
    B.disjoint state command /\
    B.disjoint command response /\
    B.disjoint state response /\
    S.equal (encode_state state_spec) (B.as_seq h0 state) /\
    decode_command (B.as_seq h0 command) == Some (reveal cmd_spec) /\
    Hash? cmd_spec
  )
  (ensures fun h0 () h1 ->
    M.modifies (M.loc_union (M.loc_buffer state) (M.loc_buffer response)) h0 h1 /\
    (let (state_spec_final, resp_spec) = spec.transition state_spec cmd_spec in
      S.equal (encode_state state_spec_final) (B.as_seq h1 state) /\
      S.equal (encode_response (Some resp_spec)) (B.as_seq h1 response))
  )

let do_hash state state_spec command cmd_spec response = 
  let h0 = ST.get () in

  let message: lbuffer uint8 32ul = sub #_ #_ #33ul command 1ul 32ul in
  let response_tag:lbuffer uint8 1ul = sub #_ #_ #33ul response 0ul 1ul in
  let response_digest: lbuffer uint8 32ul = sub #_ #_ #33ul response 1ul 32ul in

  assert_norm (Spec.Agile.HMAC.keysized Spec.Hash.Definitions.Blake2S state_len);

  HMAC.compute_blake2s_32 response_digest state 20ul message 32ul;
  upd response_tag 0ul (uint 2)


val main:handle_st spec encode_state encode_command encode_response
let main state state_spec command cmd_spec response =
  push_frame ();

  let cmd_type:uint8 = command.(0ul) in
  if xeq cmd_type (uint 1)
  then begin
    do_initialize state state_spec command (Some?.v cmd_spec) response
  end else if xeq cmd_type (uint 2)
  then begin
    do_hash state state_spec command (Some?.v cmd_spec) response
  end else begin
    assert (None? cmd_spec);
    do_none state command response
  end;

  pop_frame ()
