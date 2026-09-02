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
  | Less of int * int * int
  | Greater of int * int * int
  | Join of int * int * int
  | Minus of int * int * int
  | Size of int * int
  | Slice of int * int * int * int
  | Jump of int
  | Jump_if of int * int
  | Mark of int
  | Noop
  | Stop

type effect_layout = private {
  index : int;
  atom : C_eff.atom;
  payload : int list;
  scratch : int list;
}

type t = private {
  inputs : C_term.bind list;
  plan : C_mach.code;
  code : op array;
  octb : string;
  typ : C_type.t;
  result : C_emit.lit option;
  emission : C_mach.emission;
  veils : int;
  veil_depth : C_nat.t;
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
  | Result_header
  | Emission_invalid
  | Emission_repeated
  | Veil_invalid
  | Veil_repeated
  | Exact_image

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
  | Effect_map
  | Output of decode_error
  | Output_code

type constant =
  | CInt of string
  | CBool of bool
  | CText of string
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
  inputs : C_type.t array;
  output : C_type.t option;
  emission : C_mach.emission option;
  veil : (int * C_nat.t) option;
  consts : const_row array;
  cells : code_cell array;
  text_at : int;
  code : op array;
}

val input_limit : int
val compile : string -> (t, error) result
val compile_feed : string -> C_feed.t -> (t, error) result
val effect_layouts : C_low.prog -> (effect_layout list, error) result
val emit_effects :
  C_low.prog ->
  (effect_layout * Contract_vm.instr list) list ->
  (Contract_vm.instr array, error) result
val encode : op array -> (string, error) result
val decode : string -> (image, decode_error) result
val image_emission : image -> string
val veil_text : int -> string
val image_veil : image -> string
val image_veils : image -> string
val image_veil_depth : image -> string
val claims_aml : string -> bool
val claims_open : string -> bool
val op_text : op -> string
val decode_text : decode_error -> string
val text : error -> string