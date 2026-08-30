(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type cipher = string
type pubkey = string
type seckey = string

let unavailable () =
  invalid_arg "FHE host operation is unavailable"

let serialize_cipher value = Bytes.of_string value
let serialize_pubkey value = Bytes.of_string value
let deserialize_cipher value = Bytes.to_string value
let deserialize_pubkey value = Bytes.to_string value
let ct_add _ _ _ = unavailable ()
let ct_sub _ _ _ = unavailable ()
let ct_mul_seeded _ _ _ _ = unavailable ()
let ct_scale _ _ _ = unavailable ()
let ct_div_const _ _ _ _ = unavailable ()
let ct_add_const _ _ _ _ = unavailable ()
let ct_sub_const _ _ _ = unavailable ()
let commit_ct _ _ = unavailable ()
let pedersen_commit_amount _ _ = unavailable ()