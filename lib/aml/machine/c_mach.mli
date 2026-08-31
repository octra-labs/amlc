(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type shape =
  | SUnit
  | SAtom
  | SPair of shape * shape
  | SVec of C_nat.t * shape

type code =
  | Done
  | Push of C_emit.lit * code
  | Void of code
  | Get of C_term.id * shape * code
  | Plus of code
  | Minus of code
  | Times of code
  | Quot of code
  | Rem of code
  | Negate of code
  | Absolute of code
  | Same of code
  | Join of code
  | Clip of C_nat.t * code
  | Skip of C_nat.t * code
  | Duo of code
  | First of code
  | Second of code
  | Empty of shape * code
  | Cons of code
  | Append of code
  | Pick of C_nat.t * code
  | Unhead of code
  | Effect of C_eff.atom * code
  | Scope of C_term.bind * code * code
  | Scope2 of C_term.bind * C_term.bind * code * code
  | Fork of shape * code * code * code

type loc =
  | LDone
  | LPush of C_lex.span * loc
  | LVoid of C_lex.span * loc
  | LGet of C_lex.span * loc
  | LPlus of C_lex.span * loc
  | LMinus of C_lex.span * loc
  | LTimes of C_lex.span * loc
  | LQuot of C_lex.span * loc
  | LRem of C_lex.span * loc
  | LNegate of C_lex.span * loc
  | LAbsolute of C_lex.span * loc
  | LSame of C_lex.span * loc
  | LJoin of C_lex.span * loc
  | LClip of C_nat.t * C_lex.span * loc
  | LSkip of C_nat.t * C_lex.span * loc
  | LDuo of C_lex.span * loc
  | LFirst of C_lex.span * loc
  | LSecond of C_lex.span * loc
  | LEmpty of C_lex.span * loc
  | LCons of C_lex.span * loc
  | LAppend of C_lex.span * loc
  | LPick of C_nat.t * C_lex.span * loc
  | LUnhead of C_lex.span * loc
  | LEffect of C_lex.span * loc
  | LScope of C_lex.span * loc * loc
  | LScope2 of C_lex.span * loc * loc
  | LFork of C_lex.span * C_lex.span * C_lex.span * loc * loc * loc

type t = private {
  code : code;
  loc : loc;
  result : C_emit.lit;
  veils : int;
  veil_depth : C_nat.t;
  span : C_lex.span;
}

type error =
  | Source of C_parse.error
  | Feed of C_feed.error
  | Inputs of int
  | Effects of C_eff.atom list
  | Term
  | Run of C_eval.error
  | Plan of C_eff.atom list
  | Value of C_type.t * C_eval.value
  | Replay
  | Map

val compile : string -> (t, error) result
val compile_feed : string -> C_feed.t -> (t, error) result
val lower : C_term.t -> code option
val replay_plan : code -> (C_emit.lit list * C_eff.atom list) option
val replay : code -> C_emit.lit list option
val effects : code -> C_eff.atom list
val equal : C_emit.lit -> C_emit.lit -> bool
val shape_of : C_type.t -> shape option
val shape_width : shape -> Z.t
val same_shape : shape -> shape -> bool
val text : error -> string