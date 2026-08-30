(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type t

type error =
  | Work_cap of int
  | Program_counter of int
  | Value_type of int
  | Integer_range of int
  | Divide_zero of int
  | Modulo_zero of int

val make : ?cap:int -> ?activate:Z.t option -> ?epoch:Z.t -> unit -> t
val pc : t -> int
val steps : t -> int
val work : t -> Z.t
val halted : t -> bool
val value : t -> int -> C_emit.lit
val step : t -> C_octb.op -> (bool, error) result
val run : t -> C_octb.op array -> (unit, error) result
val result : t -> C_emit.lit
val text : error -> string