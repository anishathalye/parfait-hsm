module K2.PasswordHasher.Spec

open K2.Framework

open Lib.Sequence
open Lib.ByteSequence
open Lib.IntTypes

open Spec.Agile.HMAC
open Spec.Hash.Definitions

let secret_t = lseq uint8 20
let message_t = lseq uint8 32
let digest_t = lseq uint8 32

noeq type state_t = {
  secret:secret_t;
}

let state_init:state_t = {
  secret = create 20 (uint 0);
}

noeq type command_t =
| Initialize : secret:secret_t -> command_t
| Hash : message:message_t -> command_t

noeq type response_t =
| Initialized : response_t
| Hashed : digest:digest_t -> response_t

let transition (state:state_t) (command:command_t) : state_t & response_t =
  match command with
  | Initialize secret ->
    { secret = secret }, Initialized

  | Hash message ->
    let digest = hmac Blake2S state.secret message in
    state, Hashed digest

let spec:spec_t = {
  state_t = state_t;
  command_t = command_t;
  response_t = response_t;
  initial_state = state_init;
  transition = transition;
}
