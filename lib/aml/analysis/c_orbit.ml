(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type error =
  | Low of C_low.error
  | Check of C_check.error
  | Need of C_type.t * C_type.t
  | Nodes of Z.t
  | Depth of int

let ( let* ) value next =
  match value with
  | Ok value -> next value
  | Error error -> Error error

let fin = function
  | C_fin.Nodes actual -> Nodes actual
  | C_fin.Depth actual -> Depth actual

let body_check item term =
  let* state_typ = Result.map_error (fun error -> Low error)
    (C_low.typ item.C_syn.typ) in
  let* prog = Result.map_error (fun error -> Low error)
    (C_low.prog [item] term) in
  let* info = Result.map_error (fun error -> Check error)
    (C_check.check_in prog.inputs prog.term) in
  if C_type.equal info.typ state_typ then Ok state_typ
  else Error (Need (state_typ, info.typ))

let fit count seed body =
  let* seed_stat = Result.map_error fin (C_fin.stat seed) in
  let* body_stat = Result.map_error fin (C_fin.stat body) in
  let copies = C_nat.to_z count in
  let nodes = Z.add (Z.of_int seed_stat.nodes)
    (Z.mul copies (Z.of_int (body_stat.nodes + 1))) in
  let depth =
    if C_nat.equal count C_nat.zero then seed_stat.depth
    else C_nat.to_int count + max seed_stat.depth body_stat.depth
  in
  Result.map_error fin (C_fin.fit nodes depth)

let term count seed item body =
  let rec walk left out =
    if left = 0 then out
    else walk (left - 1) (C_syn.Let (item, out, body))
  in
  walk (C_nat.to_int count) seed

let make count seed item body =
  if not (C_nat.valid count) then Error (Low (C_low.Nat (C_nat.to_z count)))
  else
    let* _ = body_check item body in
    let* () = fit count seed body in
    Ok (term count seed item body)

let lower inputs count seed item body =
  let* term = make count seed item body in
  Result.map_error (fun error -> Low error) (C_low.prog inputs term)

let check inputs count seed item body =
  let* prog = lower inputs count seed item body in
  let* info = Result.map_error (fun error -> Check error)
    (C_check.check_in prog.inputs prog.term) in
  let* expected = Result.map_error (fun error -> Low error)
    (C_low.typ item.C_syn.typ) in
  if C_type.equal info.typ expected then Ok info
  else Error (Need (expected, info.typ))

let text = function
  | Low error -> C_low.text error
  | Check error -> C_check.text error
  | Need (expected, actual) ->
      "orbit type expected = " ^ C_type.text expected
      ^ " actual = " ^ C_type.text actual
  | Nodes actual ->
      "orbit node limit = " ^ string_of_int C_check.max_nodes
      ^ " actual = " ^ Z.to_string actual
  | Depth actual ->
      "orbit depth limit = " ^ string_of_int C_check.max_depth
      ^ " actual = " ^ string_of_int actual