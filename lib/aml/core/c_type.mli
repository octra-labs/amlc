(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type mul = Zero | One | Many
type kind = Data | Res

type t =
  | Unit
  | Bool
  | Int
  | Bytes of C_nat.t
  | Vec of C_nat.t * t
  | Cap of C_nat.t
  | Enc of C_nat.t * C_nat.t
  | Pair of t * t
  | Sum of t * t

val max_depth : int
val max_nodes : int
val equal : t -> t -> bool
val eq_work : t -> Z.t
val mul_text : mul -> string
val text : t -> string
val valid : t -> bool
val add_len : C_nat.t -> C_nat.t -> C_nat.t option
val kind : t -> kind
val equatable : t -> bool