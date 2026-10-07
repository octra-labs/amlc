(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

module M = Scope_model

let name value = "v" ^ Z.to_string value

let rec source kind = function
  | M.Done -> ""
  | M.Bind (value, rest) ->
    "let " ^ name value ^ " = 0\n" ^ source kind rest
  | M.Write (value, rest) ->
    name value ^ " = 1\n" ^ source kind rest
  | M.Block (body, rest) ->
    let block = source kind body in
    let text = match kind mod 4 with
      | 0 -> "if true {\n" ^ block ^ "}\n"
      | 1 -> "if false {} else {\n" ^ block ^ "}\n"
      | 2 -> "match E.A { E.A => {\n" ^ block ^ "} }\n"
      | _ -> "while false {\n" ^ block ^ "}\n" in
    text ^ source kind rest
  | M.Loop (value, body, rest) ->
    "for " ^ name value ^ " in 0..1 {\n" ^ source kind body ^ "}\n" ^ source kind rest

let compare kind body =
  let text = "program Scope { enum E { A } public pure fn run(): int {\n"
    ^ source kind body ^ "return 0\n} }" in
  let ast = Octra_vm.Oct_parse.parse text in
  let actual = Result.is_ok (Octra_vm.Oct_scope.check_loops ast) in
  if actual <> M.check [] body then
    failwith ("scope model mismatch case = " ^ string_of_int kind)

let () =
  let open M in
  let index = Z.zero in
  let write = Write (index, Done) in
  List.iteri compare
    [Loop (index, write, Done);
     Loop (index, Bind (index, write), Done);
     Loop (index, Block (Bind (index, Done), write), Done);
     Loop (index, Loop (Z.one, write, Done), Done);
     Loop (index, Loop (index, Bind (index, write), write), Done)];
  let random = Random.State.make [|1640000; 51|] in
  let rec make depth =
    if depth = 0 then Done
    else
      let value = Z.of_int (Random.State.int random 6) in
      match Random.State.int random 5 with
      | 0 -> Done
      | 1 -> Bind (value, make (depth - 1))
      | 2 -> Write (value, make (depth - 1))
      | 3 -> Block (make (depth / 2), make (depth / 2))
      | _ -> Loop (value, make (depth / 2), make (depth / 2)) in
  for index = 0 to 9999 do
    compare index (make 24)
  done;
  print_endline "event = scope_model status = pass cases = 10005"