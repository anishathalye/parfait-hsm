module K2.Ecdsa.Impl

module S = FStar.Seq
module SS = Lib.Sequence

open FStar.Ghost
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack
module B = LowStar.Buffer
module M = LowStar.Modifies

module P256 = Hacl.P256
module HMAC = Hacl.HMAC
open Lib.IntTypes
open Lib.Buffer
module BS = Lib.ByteSequence
open Lib.ByteBuffer
open LowStar.BufferOps

open K2.Ecdsa.Spec
open K2.Ecdsa.IO
open K2.Ecdsa.Lib
open K2.Ecdsa.Lemmas
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
  memset #_ #65ul response zero 65ul

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
  memset #_ #65ul response zero 65ul;
  response.(0ul) <- uint 1;
  let h1 = ST.get () in
  assert (S.equal (encode_response (Some Initialized)) (B.as_seq h1 response))

val do_initialize_initialize_counter:
    state:B.buffer uint8{B.length state = state_len}
  -> state_spec_final:erased spec.state_t
  -> state_spec_final_enc:erased (s:S.seq uint8{S.length s = state_len}) ->
  Stack unit
  (requires fun h0 ->
    B.live h0 state /\
    state_spec_final.prf_counter == uint 0 /\
    reveal state_spec_final_enc == encode_state state_spec_final)
  (ensures fun h0 () h1 ->
    M.modifies (M.loc_buffer state) h0 h1 /\
    S.equal (S.slice (B.as_seq h1 state) 16 24) (S.slice state_spec_final_enc 16 24))

let do_initialize_initialize_counter state state_spec_final state_spec_final_enc =
  // zero out state, which zeros out region that has counter
  let zero: uint8 = uint 0 in
  memset #_ #56ul state zero 56ul;
  let h1 = ST.get () in
  assert (S.equal (S.slice (B.as_seq h1 state) 16 24) (SS.create 8 zero));
  let prf_counter: erased _ = state_spec_final.prf_counter in
  assert (reveal prf_counter == uint #U64 #SEC 0);
  let prf_counter_enc: erased _ = BS.uint_to_bytes_be prf_counter in
  encode_zero ();
  assert (SS.equal (BS.uint_to_bytes_be prf_counter) (SS.create 8 zero));
  assert (SS.equal prf_counter_enc (SS.create 8 zero));
  // assert (S.equal (S.slice state_spec_final_enc 16 24) prf_counter_enc);
  // assert (S.equal (S.slice (B.as_seq h1 state) 16 24) (SS.create 8 0uy));
  assert (S.equal (S.slice (B.as_seq h1 state) 16 24) (S.slice state_spec_final_enc 16 24))

val do_initialize_initialize_prf_key:
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
    reveal state_spec_final_enc == encode_state state_spec_final /\
    S.equal (S.slice (B.as_seq h0 state) 16 24) (S.slice state_spec_final_enc 16 24))
  (ensures fun h0 () h1 ->
    M.modifies (M.loc_buffer state) h0 h1 /\
    // S.equal (S.slice (B.as_seq h1 state) 0 16) (S.slice state_spec_final_enc 0 16) /\
    // S.equal (S.slice (B.as_seq h0 state) 16 24) (S.slice state_spec_final_enc 16 24))
    S.equal (S.slice (B.as_seq h1 state) 0 24) (S.slice state_spec_final_enc 0 24))

let do_initialize_initialize_prf_key state state_spec state_spec_final state_spec_final_enc command cmd_spec =
  let h0 = ST.get () in
  B.blit command 1ul state 0ul 16ul;
  let h1 = ST.get () in
  assert (S.equal (S.slice (B.as_seq h1 state) 0 16) (S.slice state_spec_final_enc 0 16));

  // need this intermediate assertion:
  assert (S.equal (S.slice (S.slice (B.as_seq h0 state) 16 56) 0 8) (S.slice (S.slice (B.as_seq h1 state) 16 56) 0 8));
  // to prove this one:
  assert (S.equal (S.slice (B.as_seq h0 state) 16 24) (S.slice (B.as_seq h1 state) 16 24));
  // so we can re-establish this after this blit:
  assert (S.equal (S.slice (B.as_seq h1 state) 16 24) (S.slice state_spec_final_enc 16 24));

  lemma_slice_equal_parts (B.as_seq h1 state) state_spec_final_enc 0 16 24

val do_initialize_initialize_private_key:
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
    reveal state_spec_final_enc == encode_state state_spec_final /\
    S.equal (S.slice (B.as_seq h0 state) 0 24) (S.slice state_spec_final_enc 0 24))
  (ensures fun h0 () h1 ->
    M.modifies (M.loc_buffer state) h0 h1 /\
    S.equal (S.slice (B.as_seq h1 state) 0 56) (S.slice state_spec_final_enc 0 56))

let do_initialize_initialize_private_key state state_spec state_spec_final state_spec_final_enc command cmd_spec =
  B.blit command 17ul state 24ul 32ul;
  let h1 = ST.get () in
  lemma_slice_equal_parts (B.as_seq h1 state) state_spec_final_enc 0 24 56

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
  let new_prf_key: erased _ = Initialize?.new_prf_key cmd_spec in
  let new_private_key: erased _ = Initialize?.new_private_key cmd_spec in
  
  do_initialize_write_response response;
  do_initialize_initialize_counter state state_spec_final state_spec_final_enc;
  do_initialize_initialize_prf_key state state_spec state_spec_final state_spec_final_enc command cmd_spec;
  do_initialize_initialize_private_key state state_spec state_spec_final state_spec_final_enc command cmd_spec

// for convenience, a mask bool that's ones if the counter is ok

val do_sign_counter_ok:
    state:B.buffer uint8{B.length state = state_len}
  -> state_spec:erased spec.state_t ->
  Stack uint8
  (requires fun h0 ->
    B.live h0 state /\
    S.equal (encode_state state_spec) (B.as_seq h0 state))
  (ensures fun h0 r h1 ->
    h0 == h1 /\
    (if uint_v state_spec.prf_counter < maxint U64 then v r == ones_v U8 else v r == 0))

let do_sign_counter_ok state state_spec =
  let prf_counter_buf:lbuffer uint8 8ul = sub #_ #_ #56ul state 16ul 8ul in
  let h1 = ST.get () in
  assert (S.equal (as_seq h1 prf_counter_buf) (BS.uint_to_bytes_be state_spec.prf_counter));
  let prf_counter = uint_from_bytes_be #U64 prf_counter_buf in
  BS.lemma_uint_to_from_bytes_be_preserves_value #U64 #SEC state_spec.prf_counter;
  assert (prf_counter == state_spec.prf_counter);
  // we use normalize_term so it doesn't call pow2 etc at runtime
  let mask = lt_mask prf_counter (uint (normalize_term (maxint U64))) in
  to_u8 mask

val do_sign_update_state:
    state:B.buffer uint8{B.length state = state_len}
  -> state_spec:erased spec.state_t
  -> command:B.buffer uint8{B.length command = command_len}
  -> cmd_spec:erased spec.command_t ->
  Stack unit
  (requires fun h0 ->
    B.live h0 state /\
    B.live h0 command /\
    B.disjoint state command /\
    S.equal (encode_state state_spec) (B.as_seq h0 state) /\
    decode_command (B.as_seq h0 command) == Some (reveal cmd_spec) /\
    Sign? cmd_spec
  )
  (ensures fun h0 () h1 ->
    M.modifies (M.loc_buffer state) h0 h1 /\
    S.equal (B.as_seq h1 state) (encode_state (fst (spec.transition state_spec cmd_spec)))
  )

let do_sign_update_state state state_spec command cmd_spec = 
  let spec_result: erased _ = hide (spec.transition state_spec cmd_spec) in
  let state_spec_final: erased state_t = hide (fst spec_result) in
  let state_spec_final_enc: erased (s:S.seq uint8{S.length s = state_len}) = hide (encode_state state_spec_final) in

  assert (state_spec_final.prf_key == state_spec.prf_key);
  assert (state_spec_final.private_key == state_spec.private_key);
  let h0 = ST.get () in
  assert (S.equal (S.slice (B.as_seq h0 state) 0 16) (S.slice state_spec_final_enc 0 16));
  assert (S.equal (S.slice (B.as_seq h0 state) 24 56) (S.slice state_spec_final_enc 24 56));

  // even though we don't use prf_key_buf, somehow, slicing this buffer makes the proof go through
  let prf_key_buf:erased (lbuffer uint8 16ul) = hide (gsub #_ #_ #56ul state 0ul 16ul) in
  let prf_counter_buf:lbuffer uint8 8ul = sub #_ #_ #56ul state 16ul 8ul in
  // same thing with this private_key_buf
  let private_key_buf:erased (lbuffer uint8 32ul) = hide (gsub #_ #_ #56ul state 24ul 32ul) in
  let h1 = ST.get () in
  assert (S.equal (as_seq h1 prf_counter_buf) (BS.uint_to_bytes_be state_spec.prf_counter));
  assert ((S.slice (B.as_seq h1 state) 0 16) == (S.slice (B.as_seq h0 state) 0 16));
  assert ((S.slice (B.as_seq h1 state) 24 56) == (S.slice (B.as_seq h0 state) 24 56));

  let prf_counter = uint_from_bytes_be #U64 prf_counter_buf in
  BS.lemma_uint_to_from_bytes_be_preserves_value #U64 #SEC state_spec.prf_counter;
  assert (prf_counter == state_spec.prf_counter);
  let next_counter = saturating_incr prf_counter in

  uint_to_bytes_be prf_counter_buf next_counter;
  let h2 = ST.get () in
  assert (S.equal (S.slice (B.as_seq h2 state) 16 24) (BS.uint_to_bytes_be state_spec_final.prf_counter));
  assert (S.equal (as_seq h2 prf_counter_buf) (BS.uint_to_bytes_be state_spec_final.prf_counter));
  assert ((S.slice (B.as_seq h2 state) 0 16) == (S.slice (B.as_seq h1 state) 0 16));
  assert ((S.slice (B.as_seq h2 state) 24 56) == (S.slice (B.as_seq h1 state) 24 56));

  lemma_slice_equal_parts3_full (B.as_seq h2 state) state_spec_final_enc 16 24

val do_sign_signature:
    state:B.buffer uint8{B.length state = state_len}
  -> state_spec:erased spec.state_t
  -> command:B.buffer uint8{B.length command = command_len}
  -> cmd_spec:erased spec.command_t
  -> response:B.buffer uint8{B.length response = response_len} ->
  Stack uint8
  (requires fun h0 ->
    B.live h0 state /\
    B.live h0 command /\
    B.live h0 response /\
    B.disjoint state command /\
    B.disjoint command response /\
    B.disjoint state response /\
    S.equal (encode_state state_spec) (B.as_seq h0 state) /\
    decode_command (B.as_seq h0 command) == Some (reveal cmd_spec) /\
    Sign? cmd_spec
  )
  (ensures fun h0 flag h1 ->
    (M.modifies (M.loc_buffer response) h0 h1) /\
    (uint_v flag = ones_v U8 \/ uint_v flag = 0) /\
    (let nonce = Spec.Agile.HMAC.hmac Spec.Hash.Definitions.SHA2_256 state_spec.prf_key (BS.uint_to_bytes_be state_spec.prf_counter) in
     let maybe_signature: option (BS.lbytes 64) = Spec.P256.ecdsa_signature_agile Spec.P256.NoHash 32 (Sign?.message cmd_spec) state_spec.private_key nonce in
     ((uint_v flag = ones_v U8) <==> Some? maybe_signature) /\
     ((uint_v flag = ones_v U8) ==> S.slice (B.as_seq h1 response) 1 65 == Some?.v maybe_signature)))

let do_sign_signature state state_spec command cmd_spec response = 
  push_frame ();

  let nonce:b:B.buffer uint8{B.length b = 32} = B.alloca (uint #U8 #SEC 0) 32ul in
  let prf_key_buf:lbuffer uint8 16ul = sub #_ #_ #56ul state 0ul 16ul in
  let prf_counter_buf:lbuffer uint8 8ul = sub #_ #_ #56ul state 16ul 8ul in
  let private_key_buf:lbuffer uint8 32ul = sub #_ #_ #56ul state 24ul 32ul in
  let msg: lbuffer uint8 32ul = sub #_ #_ #49ul command 1ul 32ul in
  let h0 = ST.get () in
  assert (S.equal (as_seq h0 private_key_buf) state_spec.private_key);
  assert ((as_seq h0 private_key_buf) == state_spec.private_key);

  let h1 = ST.get () in
  assert (S.equal (as_seq h1 prf_counter_buf) (BS.uint_to_bytes_be state_spec.prf_counter));
  assert (S.equal (as_seq h1 prf_key_buf) state_spec.prf_key);
  HMAC.compute_sha2_256 nonce prf_key_buf 16ul prf_counter_buf 8ul;

  let signature: lbuffer uint8 64ul = sub #_ #_ #65ul response 1ul 64ul in
  let flag = Hacl.P256.ecdsa_sign_p256_without_hash signature 32ul msg private_key_buf nonce in

  pop_frame ();
  cast U8 SEC flag

val maybe_clear_buffer:
    buflen:size_t
  -> buf:lbuffer uint8 buflen
  -> clear_mask:uint8
  -> Stack unit
  (requires fun h0 ->
    live h0 buf /\
    (uint_v clear_mask = ones_v U8 \/ uint_v clear_mask = 0))
  (ensures fun h0 () h1 ->
    modifies1 buf h0 h1 /\
    ((uint_v clear_mask = ones_v U8) ==> S.equal (as_seq h1 buf) (as_seq h0 buf)) /\
    ((uint_v clear_mask = 0) ==> S.equal (as_seq h1 buf) (S.create (v buflen) (uint 0))))

// relies on slice_plus_one
let maybe_clear_buffer buflen buf clear_mask =
  let h00 = ST.get () in
  let inv = fun (h:HS.mem) (i:nat{0 <= i /\ i <= v buflen}) ->
    live h buf /\
    modifies1 buf h00 h /\
    // IH for true case: whole buffer never changes
    ((uint_v clear_mask = ones_v U8) ==> as_seq h buf == as_seq h00 buf) /\
    // IH for false case: prefix of buffer has been zeroed out
    ((uint_v clear_mask = 0) ==> S.equal (S.slice (as_seq h buf) 0 i) (S.slice (S.create (v buflen) (uint 0)) 0 i)) in
  let body:i:size_t{0 <= v i /\ v i < v buflen} ->
           Stack unit
           (requires fun h -> inv h (v i))
           (ensures fun h0 r h1 -> inv h0 (v i) /\ inv h1 (v i + 1)) = fun i ->
    let h0 = ST.get () in
    let x = index buf i in
    let x' = logand x clear_mask in
    upd buf i x';
    let h1 = ST.get () in
    if uint_v clear_mask = ones_v U8 then begin
      logand_ones x;
      // assert (x' == x);
      assert (S.equal (as_seq h1 buf) (as_seq h0 buf))
    end else begin
      logand_zeros x;
      // assert (x' == uint 0);
      assert (S.equal (S.slice (as_seq h1 buf) 0 (v i + 1)) (S.slice (S.create (v buflen) (uint 0)) 0 (v i + 1)))
    end in
  Lib.Loops.for 0ul buflen inv body
  
val do_sign:
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
    Sign? cmd_spec
  )
  (ensures fun h0 () h1 ->
    M.modifies (M.loc_union (M.loc_buffer state) (M.loc_buffer response)) h0 h1 /\
    (let (state_spec_final, resp_spec) = spec.transition state_spec cmd_spec in
      S.equal (encode_state state_spec_final) (B.as_seq h1 state) /\
      S.equal (encode_response (Some resp_spec)) (B.as_seq h1 response))
  )

let do_sign state state_spec command cmd_spec response = 
  let spec_result: erased _ = hide (spec.transition state_spec cmd_spec) in
  let state_spec_final: erased state_t = hide (fst spec_result) in
  let resp_spec: erased response_t = hide (snd spec_result) in
  let state_spec_final_enc: erased (s:S.seq uint8{S.length s = state_len}) = hide (encode_state state_spec_final) in
  let message: erased _ = Sign?.message cmd_spec in
  let spec_nonce:erased (s:S.seq uint8{S.length s = 32}) = hide (Spec.Agile.HMAC.hmac Spec.Hash.Definitions.SHA2_256 state_spec.prf_key (BS.uint_to_bytes_be state_spec.prf_counter)) in
  let spec_signature:erased (option (BS.lbytes 64)) = Spec.P256.ecdsa_signature_agile Spec.P256.NoHash 32 (Sign?.message cmd_spec) state_spec.private_key spec_nonce in

  let ctr_ok = do_sign_counter_ok state state_spec in
  let sig_ok = do_sign_signature state state_spec command cmd_spec response in
  let all_ok = logand ctr_ok sig_ok in
  logand_lemma ctr_ok sig_ok;
  assert (uint_v all_ok = ones_v U8 \/ uint_v all_ok = 0);
  assert ((uint_v all_ok = ones_v U8) <==> (uint_v ctr_ok = ones_v U8 && uint_v sig_ok = ones_v U8));

  do_sign_update_state state state_spec command cmd_spec;
  let response_tag:lbuffer uint8 1ul = sub #_ #_ #65ul response 0ul 1ul in
  let response_signature: lbuffer uint8 64ul = sub #_ #_ #65ul response 1ul 64ul in
  maybe_clear_buffer 64ul response_signature all_ok;

  // set tag: 2 if not ok, 3 if ok
  let tag0 = logand all_ok (uint 1) in
  logand_lemma all_ok (uint 1);
  let tag = tag0 +! (uint 2) in
  assert (uint_v all_ok = ones_v U8 ==> uint_v tag = 3);
  assert (uint_v all_ok = 0 ==> uint_v tag = 2);
  // we need Lib.Buffer.upd, not LowStar.Buffer.upd, so we can't use the op_Array_Assignment syntax
  upd response_tag 0ul tag

val handle:handle_st spec encode_state encode_command encode_response
let handle state state_spec command cmd_spec response =
  push_frame ();

  let cmd_type:uint8 = command.(0ul) in
  if xeq cmd_type (uint 1)
  then begin
    do_initialize state state_spec command (Some?.v cmd_spec) response
  end else if xeq cmd_type (uint 2)
  then begin
    do_sign state state_spec command (Some?.v cmd_spec) response
  end else begin
    assert (None? cmd_spec);
    do_none state command response
  end;

  pop_frame ()
