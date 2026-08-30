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

let max_depth = C_rule.local.ty_depth
let max_nodes = C_rule.local.ty_nodes

let equal left right =
  let rec walk = function
    | [] -> true
    | (left, right) :: rest ->
      match left, right with
      | Unit, Unit | Bool, Bool | Int, Int -> walk rest
      | Bytes left, Bytes right | Cap left, Cap right ->
        C_nat.equal left right && walk rest
      | Enc (left_key, left_rem), Enc (right_key, right_rem) ->
        C_nat.equal left_key right_key
        && C_nat.equal left_rem right_rem
        && walk rest
      | Vec (left_len, left), Vec (right_len, right) ->
        C_nat.equal left_len right_len && walk ((left, right) :: rest)
      | Pair (la, lb), Pair (ra, rb) | Sum (la, lb), Sum (ra, rb) ->
        walk ((la, ra) :: (lb, rb) :: rest)
      | _ -> false
  in
  walk [left, right]

let rec eq_work = function
  | Unit | Bool | Int | Cap _ | Enc _ -> Z.one
  | Bytes len -> Z.succ (C_nat.to_z len)
  | Vec (len, elem) ->
    Z.succ (Z.mul (C_nat.to_z len) (eq_work elem))
  | Pair (left, right) ->
    Z.succ (Z.add (eq_work left) (eq_work right))
  | Sum (left, right) ->
    Z.succ (Z.max (eq_work left) (eq_work right))

let mul_text = function
  | Zero -> "0"
  | One -> "1"
  | Many -> "many"

type part =
  | Typ of t
  | Text of string

let text typ =
  let out = C_text.make () in
  let rec walk = function
    | [] -> ()
    | _ when C_text.full out -> ()
    | Text value :: rest ->
      C_text.add out value;
      walk rest
    | Typ Unit :: rest -> C_text.add out "unit"; walk rest
    | Typ Bool :: rest -> C_text.add out "bool"; walk rest
    | Typ Int :: rest -> C_text.add out "int"; walk rest
    | Typ (Bytes len) :: rest ->
      C_text.add out ("bytes[" ^ C_nat.text len ^ "]");
      walk rest
    | Typ (Vec (len, elem)) :: rest ->
      walk (Text "vec[" :: Text (C_nat.text len) :: Text ", "
        :: Typ elem :: Text "]" :: rest)
    | Typ (Cap id) :: rest ->
      C_text.add out ("cap[" ^ C_nat.text id ^ "]");
      walk rest
    | Typ (Enc (key, rem)) :: rest ->
      C_text.add out ("enc[" ^ C_nat.text key ^ "," ^ C_nat.text rem ^ "]");
      walk rest
    | Typ (Pair (left, right)) :: rest ->
      walk (Text "(" :: Typ left :: Text " * " :: Typ right :: Text ")" :: rest)
    | Typ (Sum (left, right)) :: rest ->
      walk (Text "(" :: Typ left :: Text " + " :: Typ right :: Text ")" :: rest)
  in
  walk [Typ typ];
  C_text.get out

let valid typ =
  let rec walk nodes = function
    | [] -> true
    | (depth, typ) :: rest ->
      if depth > max_depth || nodes >= max_nodes then false
      else
        let next = depth + 1 in
        match typ with
        | Unit | Bool | Int -> walk (nodes + 1) rest
        | Bytes len | Cap len ->
          C_nat.valid len && walk (nodes + 1) rest
        | Enc (key, rem) ->
          C_nat.valid key && C_nat.valid rem && walk (nodes + 1) rest
        | Vec (len, elem) ->
          C_nat.valid len && walk (nodes + 1) ((next, elem) :: rest)
        | Pair (left, right) | Sum (left, right) ->
          walk (nodes + 1) ((next, left) :: (next, right) :: rest)
  in
  walk 0 [0, typ]

let add_len left right =
  C_nat.add left right

let kind typ =
  let rec walk = function
    | [] -> Data
    | Unit :: rest | Bool :: rest | Int :: rest | Bytes _ :: rest
    | Enc _ :: rest -> walk rest
    | Vec (len, _) :: rest when C_nat.equal len C_nat.zero -> walk rest
    | Cap _ :: _ -> Res
    | Vec (_, elem) :: rest -> walk (elem :: rest)
    | Pair (left, right) :: rest | Sum (left, right) :: rest ->
      walk (left :: right :: rest)
  in
  walk [typ]

let equatable typ =
  let rec walk = function
    | [] -> true
    | Unit :: rest | Bool :: rest | Int :: rest | Bytes _ :: rest -> walk rest
    | Vec (len, _) :: rest when C_nat.equal len C_nat.zero -> walk rest
    | Cap _ :: _ | Enc _ :: _ -> false
    | Vec (_, elem) :: rest -> walk (elem :: rest)
    | Pair (left, right) :: rest | Sum (left, right) :: rest ->
      walk (left :: right :: rest)
  in
  walk [typ]