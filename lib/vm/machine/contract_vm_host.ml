(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type write =
  | Set of string * string
  | Del of string

type object_result = {
  version : int64;
  writes : write list;
}

let max_fhe_proof_bytes = 49_152
let cipher_text value = value
let cipher_ok _ = false
let zero_proof _ = None
let range_proof _ = None
let commitment _ = None
let verify_zero ~pubkey:_ ~cipher:_ ~proof:_ = false
let verify_range ~pubkey:_ ~cipher:_ ~proof:_ = false
let verify_claim ~pubkey:_ ~cipher:_ ~proof:_ ~commitment:_ = false
let state_path_key _ = None
let member_count _ _ = 0
let has_member _ _ _ = false
let member_at _ _ _ = None

let apply_object
    ~current_epoch:_
    ~storage:_
    ~transition_ref:_
    ~object_ref:_
    ~previous_state_ref:_
    ~next_state_ref:_
    ~member_bundle:_
    ~touched_members_hash:_
    ~proof_kind:_
    ~proof_receipt_hash:_
    ~status:_
    ~intent_id:_ =
  Error "object host operation is unavailable"

let ed25519 ~key:_ ~message:_ ~signature:_ = false
let groth16 ~key:_ ~proof:_ ~inputs:_ = false
let spawn_error ~reason:_ ~octets:_ = ()
let spawn2_error ~reason:_ ~octets:_ ~args:_ = ()