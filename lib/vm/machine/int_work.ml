(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type op = Add | Sub | Mul | Div | Mod | Neg | Abs
type mode = Prior | Active
type answer = Value of Z.t | Reject

let bits value = Int.max 1 (Z.numbits value)

let cells value =
  1 + ((bits value - 1) / 64)

let fixed = function
  | Add | Sub | Mul -> 3
  | Div | Mod | Neg | Abs -> 5

let variable op left right =
  let left = Z.of_int (cells left) in
  let right = Z.of_int (cells right) in
  match op with
  | Add | Sub -> Z.max left right
  | Mul | Div | Mod -> Z.mul left right
  | Neg | Abs -> left

let cost mode op left right =
  let base = Z.of_int (fixed op) in
  match mode with
  | Prior -> base
  | Active -> Z.add base (variable op left right)

let select ~activate ~epoch =
  match activate with
  | Some first when Z.sign first >= 0 && Z.leq first epoch -> Active
  | Some _ | None -> Prior

let eval op left right =
  match op with
  | Add -> Value (Z.add left right)
  | Sub -> Value (Z.sub left right)
  | Mul -> Value (Z.mul left right)
  | Div -> if Z.equal right Z.zero then Reject else Value (Z.div left right)
  | Mod -> if Z.equal right Z.zero then Reject else Value (Z.rem left right)
  | Neg -> Value (Z.neg left)
  | Abs -> Value (Z.abs left)