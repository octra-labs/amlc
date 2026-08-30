(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type op =
  | Load of int * C_emit.lit
  | Move of int * int
  | Plus of int * int * int
  | Times of int * int * int
  | Quotient of int * int * int
  | Remainder of int * int * int
  | Negate of int * int
  | Absolute of int * int
  | Same of int * int * int
  | Join of int * int * int
  | Minus of int * int * int
  | Size of int * int
  | Slice of int * int * int * int
  | Jump of int
  | Jump_if of int * int
  | Mark of int
  | Noop
  | Stop

type t = private {
  plan : C_mach.code;
  code : op array;
  octb : string;
  result : C_emit.lit;
  map : C_smap.t;
  live : C_live.t;
}

type decode_error =
  | Input_size of int
  | Header
  | Magic
  | Version of int
  | Constant_count of int
  | Instruction_count of int64
  | Constant_header of int
  | Constant_size of int * int
  | Constant_data of int
  | Constant_tag of int * int
  | Constant_value of int
  | Instruction_data of int
  | Constant_ref of int * int
  | Opcode of int * int
  | Register_ref of int * int
  | Jump_value of int * int64
  | Jump_ref of int * int
  | Jump_mark of int
  | Trailing_data of int
  | Empty_code

type error =
  | Mach of C_mach.error
  | Stack
  | Register
  | Label
  | Constants of int
  | Map
  | Smap of C_smap.error
  | Slot
  | Lmap of C_live.error
  | Output of decode_error
  | Output_code

type constant =
  | CInt of string
  | CBool of bool
  | CData of C_rval.t
  | CBytes of string

type const_row = private {
  id : int;
  at : int;
  size : int;
  value : constant;
}

type code_cell = private {
  pc : int;
  at : int;
  size : int;
}

type image = private {
  consts : const_row array;
  cells : code_cell array;
  text_at : int;
  code : op array;
}

val compile : string -> (t, error) result
val compile_feed : string -> C_feed.t -> (t, error) result
val encode : op array -> (string, error) result
val decode : string -> (image, decode_error) result
val op_text : op -> string
val decode_text : decode_error -> string
val text : error -> string