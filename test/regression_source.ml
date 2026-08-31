(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

open Regression_support

let trailing = {|
contract First { pure fn value(): int { return 1 } }
contract Second { pure fn value(): int { return 2 } }
|}

let duplicate_function = {|
contract Duplicate {
  pure fn value(): int { return 1 }
  pure fn value(): int { return 2 }
}
|}

let duplicate_parameter = {|
contract Duplicate {
  pure fn value(number: int, number: int): int { return number }
}
|}

let duplicate_state = {|
contract Duplicate {
  state { value: int value: int }
  pure fn read(): int { return 0 }
}
|}

let duplicate_empty_state = {|
contract Duplicate {
  state { }
  state { }
  pure fn read(): int { return 0 }
}
|}

let duplicate_constructor = {|
contract Duplicate {
  constructor() { }
  constructor() { }
  pure fn read(): int { return 0 }
}
|}

let private_namespace = {|
contract PrivateNamespace {
  state { @aml: int }
  pure fn read(): int { return 0 }
}
|}

let core_form_position = {|
program Position {
  form broken [] (many value: int) ->[many] int marks {} =
    value + true
  term
    0
}
|}

let core_linearity_position = {|
program Position {
  term
    let many a: int = 1 in
    let once unused: int = 2 in
    a
}
|}

let core_vec_index =
  "program Position { term at[5](vec[int](1,2,3)) }"

let legacy_program = {|
program Store {
  state { value: string }
  public fn permit(input: string): string { return input }
}
|}

let direct_form = {|
program Direct {
  form add [many left: int] (many right: int) ->[many] int marks {} =
    left + right
  term add(20, 22)
}
|}

let used_form = {|
program Direct {
  form add [many left: int] (many right: int) ->[many] int marks {} =
    left + right
  term use add[20](22) as many value: int in value
}
|}

let let_use = {|
program LetUse {
  form keep [] (once value: int) ->[many] int marks {} = value
  term
    let once item: int = 42 in
    use keep[](item) as many value: int in
    value
}
|}

let let_use_twice = {|
program LetUseTwice {
  form keep [] (once value: int) ->[many] int marks {} = value
  term
    let once item: int = 21 in
    use keep[](item) as many value: int in
    item + value
}
|}

let nested_form = {|
program Direct {
  form add [many left: int] (many right: int) ->[many] int marks {} =
    left + right
  form triple [] (many value: int) ->[many] int marks {} =
    add(value, value) + value
  term triple(7)
}
|}

let order = {|
program Order {
  term
    if -3 < -2 then
      if -2 <= -2 then
        if 5 > 4 then
          if 5 >= 5 then 42 else 4
        else 3
      else 2
    else 1
}
|}

let order_edges = {|
program OrderEdges {
  term
    if 3 < 3 then 1 else
    if 3 <= 3 then
      if 2 > 3 then 2 else
      if 2 >= 3 then 3 else
      if 1 + 2 < 2 * 2 then 42 else 4
    else 5
}
|}

let order_type = "program BadOrder { term true < 5 }"
let order_chain = "program Chain { term 1 < 2 < 3 }"

let order_auto = "program AutoOrder { term 3 < 5 }"

let order_explicit = {|
program ExplicitOrder {
  term
    let many left: int = 3 in
    let many right: int = 5 in
    let many delta: int = right - left in
    if equal[int](left, right) then false
    else equal[int](abs(delta), delta)
}
|}

let order_left = {|
program LeftOrder {
  input once n: int
  term n < 5
}
|}

let order_right = {|
program RightOrder {
  input once n: int
  term 5 > n
}
|}

let order_form = {|
program FormOrder {
  form less [] (many left: int) ->[many] int marks {} =
    if left < 5 then 42 else 0
  term less(3)
}
|}

let finite_orbit = {|
program FiniteOrbit {
  input once n: int
  term orbit[64, n] from 0 with many state: int => state + 1
}
|}

let finite_orbit_huge = {|
program Huge {
  term orbit[1000000, 1] from 0 with many state: int => state + 1
}
|}

let finite_orbit_order = {|
program FiniteOrder {
  input once n: int
  term orbit[8, n] from 0 with many state: int =>
    if state < 3 then state + 1 else state
}
|}

let finite_orbit_zero = {|
program FiniteZero {
  input once n: int
  term orbit[0, n] from 7 with erase state: int => 8
}
|}

let finite_orbit_type = {|
program FiniteType {
  term orbit[4, true] from 0 with many state: int => state + 1
}
|}

let finite_orbit_body = {|
program FiniteBody {
  term orbit[0, 1] from 0 with erase state: int => true
}
|}

let orbit_seed_type = {|
program OrbitSeedType {
  term orbit[0] from true with erase state: int => 0
}
|}

let finite_orbit_seed_type = {|
program FiniteSeedType {
  term orbit[0, 1] from true with erase state: int => 0
}
|}

let order_matrix () =
  let values = List.init 33 (fun index -> index - 16) in
  let relations = [
    "<", (fun left right -> left < right);
    "<=", (fun left right -> left <= right);
    ">", (fun left right -> left > right);
    ">=", (fun left right -> left >= right);
  ] in
  List.iter
    (fun (symbol, decide) ->
      List.iter
        (fun left ->
          List.iter
            (fun right ->
              let source = Printf.sprintf
                "program Matrix { term %d %s %d }" left symbol right in
              core_result "order matrix"
                (Octra_vm.C_emit.Bool (decide left right)) source)
            values)
        values)
    relations

let order_limit () =
  let values = String.concat ", " (List.init 6000 (fun _ -> "0 < 1")) in
  let source = "program OrderLimit { term vec[bool](" ^ values ^ ") }" in
  core_refuse "order source limit" "syntax nodes limit = 100000" source;
  let item = Octra_vm.C_raw.Cmp (Octra_vm.C_syn.Lt,
    Octra_vm.C_raw.KInt Z.zero, Octra_vm.C_raw.KInt Z.one) in
  let term = Octra_vm.C_raw.KVec (Octra_vm.C_decl.Exact Octra_vm.C_syn.TBool,
    List.init 6000 (fun _ -> item)) in
  match Octra_vm.C_raw.elab Octra_vm.C_idx.empty term with
  | Error error ->
      let reason = Octra_vm.C_raw.text error in
      if not (includes reason "raw term nodes limit = 100000") then
        fail "order raw limit" ("unexpected reason = " ^ reason)
  | Ok _ -> fail "order raw limit" "raw term accepted"

let reuse_regs () =
  let expr = String.concat " + " (List.init 80 (fun _ -> "1")) in
  let source = "program Reuse { term " ^ expr ^ " }" in
  core_result "register reuse" (Octra_vm.C_emit.Int (Z.of_int 80)) source

let linear_form = {|
program Direct {
  form consume [] (once value: int) ->[many] int marks {} = value
  term consume(7)
}
|}

let effect_form = {|
program Direct {
  form touch [] (many value: int) ->[many] int marks {write[1]} =
    write[1](value)
  term touch(7)
}
|}

let short_call = {|
program Direct {
  form add [many left: int] (many right: int) ->[many] int marks {} =
    left + right
  term add(1)
}
|}

let wrong_call_type = {|
program Direct {
  form add [many left: int] (many right: int) ->[many] int marks {} =
    left + right
  term add(true, 1)
}
|}

let forward_call = {|
program Direct {
  form first [] (many value: int) ->[many] int marks {} = second(value)
  form second [] (many value: int) ->[many] int marks {} = value + 1
  term first(1)
}
|}

let veil = {|
program Veil {
  size d = 2
  veil Budget key[1] depth[d] under {
    add[1], mul[7], renew[20]
  } {
    param[10] room[1]
    param[20] room[2]
    input x: enc[1,d]
    input y: enc[1,d]
    term renew((x * y) * trim[1](x))
  }
  term 0
}
|}

let plain = "program Plain { term 0 }"

let nul_string =
  "program Nul { public view fn value(): string { return \"x"
  ^ String.make 1 '\000'
  ^ "y\" } }"

let run () =
  refuse "trailing source" "trailing source after declaration" trailing;
  refuse "duplicate function" "duplicate function name" duplicate_function;
  refuse "duplicate parameter" "duplicate parameter name" duplicate_parameter;
  refuse "duplicate state field" "duplicate state field name" duplicate_state;
  refuse "duplicate state block" "duplicate state declaration" duplicate_empty_state;
  refuse "duplicate constructor" "duplicate constructor" duplicate_constructor;
  refuse "private namespace" "unexpected character: @" private_namespace;
  refuse "NUL string" "NUL byte is not allowed in string" nul_string;
  core_refuse "form position" "line = 4 col = 5" core_form_position;
  core_refuse "linearity position" "line = 5 col = 5" core_linearity_position;
  core_refuse "vector index" "vec index = 5 size = 3" core_vec_index;
  if not (Contract_cli.legacy_source legacy_program) then
    fail "legacy source" "program not recognized";
  core_result "direct form" (Octra_vm.C_emit.Int (Z.of_int 42)) direct_form;
  core_equal "direct use equality" direct_form used_form;
  core_result "let before use" (Octra_vm.C_emit.Int (Z.of_int 42)) let_use;
  core_refuse "let use linear" "used id =" let_use_twice;
  core_result "nested form" (Octra_vm.C_emit.Int (Z.of_int 21)) nested_form;
  core_result "integer order" (Octra_vm.C_emit.Int (Z.of_int 42)) order;
  core_result "order edges" (Octra_vm.C_emit.Int (Z.of_int 42)) order_edges;
  core_refuse "order type" "type expected = int actual = bool" order_type;
  core_refuse "order chain" "expected = } actual = <" order_chain;
  core_equal "order erasure" order_auto order_explicit;
  core_input "order left once" (Octra_vm.C_eval.Bool true)
    (Octra_vm.C_eval.Int (Z.of_int 3)) order_left;
  core_input "order right once" (Octra_vm.C_eval.Bool true)
    (Octra_vm.C_eval.Int (Z.of_int 3)) order_right;
  core_result "order form" (Octra_vm.C_emit.Int (Z.of_int 42)) order_form;
  order_matrix ();
  order_limit ();
  reuse_regs ();
  core_input "finite orbit input" (Octra_vm.C_eval.Int (Z.of_int 5))
    (Octra_vm.C_eval.Int (Z.of_int 5)) finite_orbit;
  core_input "finite orbit negative" (Octra_vm.C_eval.Int Z.zero)
    (Octra_vm.C_eval.Int (Z.of_int (-3))) finite_orbit;
  core_input "finite orbit cap" (Octra_vm.C_eval.Int (Z.of_int 64))
    (Octra_vm.C_eval.Int (Z.of_int 100)) finite_orbit;
  let wide = Z.shift_left Z.one 256 in
  core_input "finite orbit wide" (Octra_vm.C_eval.Int (Z.of_int 64))
    (Octra_vm.C_eval.Int wide) finite_orbit;
  core_input "finite orbit wide negative" (Octra_vm.C_eval.Int Z.zero)
    (Octra_vm.C_eval.Int (Z.neg wide)) finite_orbit;
  core_refuse "finite orbit profile" "orbit node limit = 100000"
    finite_orbit_huge;
  core_input "finite orbit order" (Octra_vm.C_eval.Int (Z.of_int 3))
    (Octra_vm.C_eval.Int (Z.of_int 8)) finite_orbit_order;
  core_input "finite orbit zero" (Octra_vm.C_eval.Int (Z.of_int 7))
    (Octra_vm.C_eval.Int (Z.of_int 8)) finite_orbit_zero;
  core_refuse "finite orbit type" "type expected = int actual = bool"
    finite_orbit_type;
  core_refuse "finite orbit body" "orbit type expected = int actual = bool"
    finite_orbit_body;
  core_refuse "orbit seed type" "type expected = int actual = bool"
    orbit_seed_type;
  core_refuse "finite orbit seed type" "type expected = int actual = bool"
    finite_orbit_seed_type;
  core_refuse "linear direct form" "function requires explicit use" linear_form;
  core_refuse "effect direct form" "function requires explicit use" effect_form;
  core_refuse "direct arity" "expected = 2 actual = 1" short_call;
  core_refuse "direct type" "type expected = int actual = bool" wrong_call_type;
  core_refuse "direct order" "unknown function = second" forward_call;
  core_veil "veil evidence" veil plain