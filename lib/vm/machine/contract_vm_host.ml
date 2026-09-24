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
let state_ref raw =
  let reference = String.lowercase_ascii (String.trim raw) in
  let hex = function '0' .. '9' | 'a' .. 'f' -> true | _ -> false in
  if String.length reference <> 64 || not (String.for_all hex reference) then None
  else Some reference

let state_path_key raw =
  state_ref raw |> Option.map (fun reference ->
    let path = "/_state/" ^ reference in
    let size = String.init 4 (fun index ->
      Char.chr ((String.length path lsr (24 - index * 8)) land 255)) in
    Digestif.SHA256.digest_string ("octra:asset_state_path:v1\000" ^ size ^ path)
      |> Digestif.SHA256.to_hex)
let member_refs storage object_ref =
  let prefix = "object_member:" ^ object_ref ^ ":" in
  let suffix = ":state_ref" in
  Hashtbl.fold (fun key _ refs ->
    let size = String.length key - String.length prefix - String.length suffix in
    if size > 0 && String.starts_with ~prefix key && String.ends_with ~suffix key then
      key :: refs
    else refs) storage []
  |> List.sort_uniq String.compare
  |> List.map (fun key -> String.sub key (String.length prefix)
    (String.length key - String.length prefix - String.length suffix))

let member_count storage object_ref =
  List.length (member_refs storage object_ref)

let has_member storage object_ref member_ref =
  let key = "object_member:" ^ object_ref ^ ":" ^ member_ref ^ ":state_ref" in
  match Hashtbl.find_opt storage key with
  | None -> false
  | Some value -> Option.is_some (state_ref value)

let member_at storage object_ref index =
  if index < 0 then None
  else List.nth_opt (member_refs storage object_ref) index

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

let ed25519 ~key ~message ~signature =
  try Octra_ed25519.verify ~pub:key ~msg:message signature
  with _ -> false
let groth16 ~key:_ ~proof:_ ~inputs:_ = false
let spawn_error ~reason:_ ~octets:_ = ()
let spawn2_error ~reason:_ ~octets:_ ~args:_ = ()