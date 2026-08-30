(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type op = Add | Sub | Mul | Div | Mod | Neg | Abs
type mode = Prior | Active
type answer = Value of Z.t | Reject

val bits : Z.t -> int
val cells : Z.t -> int
val fixed : op -> int
val variable : op -> Z.t -> Z.t -> Z.t
val cost : mode -> op -> Z.t -> Z.t -> Z.t
val select : activate:Z.t option -> epoch:Z.t -> mode
val eval : op -> Z.t -> Z.t -> answer