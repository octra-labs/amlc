(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type write =
  | Set of string * string
  | Del of string

type object_result = {
  version : int64;
  writes : write list;
}

val max_fhe_proof_bytes : int
val cipher_text : Pvac_ffi.cipher -> string
val cipher_ok : Pvac_ffi.cipher -> bool
val zero_proof : string -> string option
val range_proof : string -> string option
val commitment : string -> string option
val verify_zero :
  pubkey:Pvac_ffi.pubkey ->
  cipher:Pvac_ffi.cipher ->
  proof:string ->
  bool
val verify_range :
  pubkey:Pvac_ffi.pubkey ->
  cipher:Pvac_ffi.cipher ->
  proof:string ->
  bool
val verify_claim :
  pubkey:Pvac_ffi.pubkey ->
  cipher:Pvac_ffi.cipher ->
  proof:string ->
  commitment:string ->
  bool
val state_path_key : string -> string option
val member_count : (string, string) Hashtbl.t -> string -> int
val has_member : (string, string) Hashtbl.t -> string -> string -> bool
val member_at : (string, string) Hashtbl.t -> string -> int -> string option
val apply_object :
  current_epoch:int ->
  storage:(string, string) Hashtbl.t ->
  transition_ref:string ->
  object_ref:string ->
  previous_state_ref:string ->
  next_state_ref:string ->
  member_bundle:string ->
  touched_members_hash:string ->
  proof_kind:string ->
  proof_receipt_hash:string ->
  status:string ->
  intent_id:string ->
  (object_result, string) result
val ed25519 : key:string -> message:string -> signature:string -> bool
val groth16 : key:bytes -> proof:bytes -> inputs:bytes -> bool
val spawn_error : reason:string -> octets:int -> unit
val spawn2_error : reason:string -> octets:int -> args:int -> unit