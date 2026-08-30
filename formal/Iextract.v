(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatBigInt.
From Stdlib Require Import ExtrOcamlZBigInt.
From Stdlib Require Import ZArith.ZArith.

Require Import Iwork.

Extraction Language OCaml.
Set Extraction Output Directory ".".
Extract Inductive comparison => "[ `CEq | `CLt | `CGt ]"
  ["`CEq" "`CLt" "`CGt"].
Extract Constant Nat.compare =>
  "(fun x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then `CEq else if s < 0 then `CLt else `CGt)".
Extract Constant N.compare =>
  "(fun x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then `CEq else if s < 0 then `CLt else `CGt)".
Extract Constant Pos.compare =>
  "(fun x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then `CEq else if s < 0 then `CLt else `CGt)".
Extract Constant Pos.compare_cont =>
  "(fun c x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then c else if s < 0 then `CLt else `CGt)".
Extract Constant Z.compare =>
  "(fun x y -> let s = Big_int_Z.compare_big_int x y in if s = 0 then `CEq else if s < 0 then `CLt else `CGt)".
Extraction "iwork_model.ml"
  Iwork.bits Iwork.cells Iwork.fixed Iwork.variable Iwork.cost Iwork.select
  Iwork.eval.