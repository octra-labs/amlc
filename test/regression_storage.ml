(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

open Regression_support

let option_source = {|
program Optional {
  state { a: option[int] b: option[int] xs: map[int]option[int] calls: int }
  private fn next(): int {
    self.calls += 1
    return self.calls
  }
  public fn copy_empty(): bool {
    self.a = none()
    self.b = self.a
    return is_some_opt(self.b)
  }
  public fn pick(): int {
    self.xs[1] = some(11)
    self.xs[2] = some(22)
    self.calls = 0
    return unwrap(self.xs[next()])
  }
  private fn pass(value: option[int]): option[int] { return value }
  public view fn present(): bool { return is_some_opt(self.a) }
  public fn copy_local(empty: bool): bool {
    self.a = some(0)
    self.b = some(99)
    self.xs[3] = some(99)
    if empty { self.a = none() }
    let saved = pass(self.a)
    self.b = saved
    self.xs[3] = self.b
    self.a = self.xs[3]
    return is_some_opt(self.a)
  }
  public fn local_value(): int {
    let saved: option[int] = some(0)
    return unwrap(pass(saved))
  }
  public fn missing(): int {
    self.calls = 17
    return unwrap(self.a)
  }
  public fn clear(): bool {
    self.a = none()
    self.a = self.a
    self.xs[7] = self.xs[8]
    return is_some_opt(self.a) || is_some_opt(self.xs[7])
  }
}
|}

let option_values = {|
program OptionValues {
  struct Row { value: option[string] }
  state {
    text: option[string]
    flag: option[bool]
    owner: option[address]
    nested: option[option[int]]
    row: Row
    items: list[option[int]]
  }
  private fn echo(value: option[string]): option[string] { return value }
  public fn roundtrip(value: string): string {
    self.text = some(value)
    let saved = echo(self.text)
    self.row.value = saved
    return unwrap(self.row.value)
  }
  public fn boolean(value: bool): bool {
    self.flag = some(value)
    return unwrap(self.flag)
  }
  public fn address_value(value: address): address {
    self.owner = some(value)
    let saved = self.owner
    return unwrap(saved)
  }
  public fn owner_same(): bool {
    self.owner = some(caller)
    return unwrap(self.owner) == caller
  }
  public view fn owner_diff(value: address): bool {
    let saved = some(caller)
    return unwrap(saved) != value
  }
  public view fn bytes_same(value: bytes): bool {
    let saved = some(value)
    return unwrap(saved) == value
  }
  public view fn digest_same(value: bytes32): bool {
    let saved = some(value)
    return unwrap(saved) == value
  }
  public view fn bytes_diff(left: bytes, right: bytes): bool {
    return unwrap(some(left)) != right
  }
  public fn inner_empty(): bool {
    self.nested = some(none())
    return is_some_opt(self.nested) && !is_some_opt(unwrap(self.nested))
  }
  public fn inner_value(): int {
    self.nested = some(some(7))
    return unwrap(unwrap(self.nested))
  }
  public fn list_value(): int {
    self.items.push(none())
    self.items.push(some(7))
    let total = 0
    for item in self.items { if is_some_opt(item) { total += unwrap(item) } }
    return total
  }
  public view fn supplied(value: option[string]): bool { return is_some_opt(value) }
}
|}

let option_checks () =
  let cases = [
    option_source, "copy_empty", [], "bool:false";
    option_source, "pick", [], "int:11";
    option_source, "copy_local", [VM.VBool true], "bool:false";
    option_source, "copy_local", [VM.VBool false], "bool:true";
    option_source, "local_value", [], "int:0";
    option_source, "clear", [], "bool:false";
    option_values, "boolean", [VM.VBool false], "bool:false";
    option_values, "boolean", [VM.VBool true], "bool:true";
    option_values, "owner_same", [], "bool:true";
    option_values, "owner_diff", [VM.VAddr ("oct" ^ String.make 44 '2')], "bool:true";
    option_values, "bytes_same", [VM.VBytes ""], "bool:true";
    option_values, "bytes_same", [VM.VBytes "\x00\xff"], "bool:true";
    option_values, "digest_same", [VM.VBytes32 (String.make 32 '\x01')], "bool:true";
    option_values, "bytes_diff", [VM.VBytes "one"; VM.VBytes "two"], "bool:true";
    option_values, "bytes_diff", [VM.VBytes "one"; VM.VBytes "one"], "bool:false";
    option_values, "inner_empty", [], "bool:true";
    option_values, "inner_value", [], "int:7";
    option_values, "list_value", [], "int:7";
  ] in
  List.iter (fun (source, method_name, args, expected) ->
    let direct = execute ~args method_name method_name source in
    let detached = execute_octb ~args method_name method_name source in
    result method_name expected direct;
    same_runtime method_name direct detached) cases;
  let picked = execute "option key" "pick" option_source in
  storage_value "option key" "calls" "1" picked;
  execute ~args:[VM.VBool true] "option cleared" "copy_local" option_source
  |> storage_count "option cleared" 0;
  List.iter (fun mark ->
    let storage = ["a", "12"; "@aml/option/a/present", mark] in
    let out = attempt ~storage "option mark" "present" option_source in
    if out.stop <> Local.Reverted then
      fail "option mark" ("invalid presence accepted mark = " ^ mark);
    if out.storage <> List.sort compare storage then
      fail "option mark" "refusal changed storage") [""; "false"; "1"; "yes"];
  let missing = attempt "option missing" "missing" option_source in
  if missing.stop <> Local.Reverted || missing.storage <> [] then
    fail "option missing" "refusal did not preserve storage";
  let valid = "oct" ^ String.make 44 '1' in
  execute ~args:[VM.VString valid] "option address" "address_value" option_values
  |> result "option address" ("text:" ^ valid);
  List.iter (fun text ->
    let args = [VM.VString text] in
    let direct = execute ~args "option text" "roundtrip" option_values in
    let detached = execute_octb ~args "option text OCTB" "roundtrip" option_values in
    if direct.result <> VM.VString text then fail "option text" "payload changed";
    same_runtime "option text" direct detached)
    ([""; "0"; "1"; "true"; "a#b/c"; "\x00\xff"]
      @ List.init 64 (fun size -> String.init size (fun index -> Char.chr ((size + index * 31) mod 256))));
  List.iter (fun raw ->
    let out = attempt ~args:[VM.VString raw] "option input" "supplied" option_values in
    if out.stop <> Local.Reverted then fail "option input" "invalid tag accepted")
    [""; "00"; "01"; "2"; "true"];
  List.iter (fun (expr, reason) ->
    let source = "program Wrong { public fn run() { let value = " ^ expr ^ " } }" in
    refuse "option type" reason source)
    ["unwrap(1)", "unwrap requires option";
     "is_some_opt(true)", "is_some_opt requires option";
     "unwrap()", "expected expression";
     "none(1)", "expected )"]

let foreach_source = {|
contract Total {
  state { xs: list[int] }
  public fn total(): int {
    self.xs.push(10)
    self.xs.push(20)
    self.xs.push(30)
    let sum = 0
    for item in self.xs { sum += item }
    return sum
  }
}
|}

let checkpoint_source = {|
contract Atomic {
  state { a: int b: int }
  public fn nested(): int {
    checkpoint()
    self.a = 1
    checkpoint()
    self.b = 2
    commit()
    rollback()
    return self.a * 10 + self.b
  }
}
|}

let bool_source = {|
contract Flag {
  state { paused: bool }
  public fn set(v: bool): bool {
    self.paused = v
    return self.paused
  }
  public view fn get(): bool { return self.paused }
}
|}

let delete_source = {|
contract Delete {
  state { xs: list[string] }
  public fn run(): string {
    self.xs.push("a")
    self.xs.push("b")
    self.xs.push("c")
    self.xs.delete(1)
    let out = to_string(self.xs.length) + ":"
    for item in self.xs { out = out + "[" + item + "]" }
    return out
  }
}
|}

let single_key_source = {|
contract SingleKey {
  state { calls: int values: map[int]int }
  private fn next(): int {
    self.calls += 1
    return self.calls
  }
  public fn run(): int {
    self.values[next()] += 10
    return self.calls
  }
}
|}

let map_source = {|
contract Keys {
  state { values: map[string]map[string]int }
  public fn run(): int {
    self.values["a:b"]["c"] = 111
    self.values["a"]["b:c"] = 222
    return self.values["a:b"]["c"]
  }
}
|}

let list_namespace_source = {|
contract ListNamespace {
  state { xs: list[int] xs_len: int }
  public fn run(): int {
    self.xs.push(7)
    self.xs.push(8)
    self.xs_len = 99
    return self.xs.length
  }
}
|}

let guard_source = {|
contract GuardNamespace {
  state { _lock: string }
  public fn arm(): bool {
    self._lock = "1"
    return true
  }
  public nonreentrant fn run(): int { return 1 }
}
|}

let tuple_source = {|
contract Tuple {
  private fn pair(a: string, b: int): (string, int) { return (a, b) }
  public view fn run(a: string, b: int): int {
    let (text, number) = pair(a, b)
    return number + 1
  }
}
|}

let empty_pop_source = {|
contract EmptyPop {
  state { values: list[string] }
  public fn run() { self.values.pop() }
}
|}

let legacy_value_source = {|
contract LegacyValue {
  state { owner: address }
  public fn same(): bool {
    self.owner = caller
    return caller == self.owner
  }
  public fn differs(): bool {
    self.owner = caller
    return caller != self.owner
  }
  public fn reject(): bool {
    require(1 == 2, "denied")
    return true
  }
}
|}

let schema_source = {|
program StateSchema {
  state {
    amount: int
    enabled: bool
    label: string
    payload: bytes
    digest: bytes32
    count64: u64
    count128: u128
    count256: u256
    owner: address
  }
  public view fn amount_value(): int { return self.amount }
  public view fn enabled_value(): bool { return self.enabled }
  public view fn label_value(): string { return self.label }
  public view fn payload_value(): bytes { return self.payload }
  public view fn digest_value(): bytes32 { return self.digest }
  public view fn count64_value(): u64 { return self.count64 }
  public view fn count128_value(): u128 { return self.count128 }
  public view fn count256_value(): u256 { return self.count256 }
  public view fn owner_value(): address { return self.owner }
  public view fn add_one(): int { return self.amount + 1 }
}
|}

let plain_source = {|
program Plain {
  public view fn value(): int { return 1 }
}
|}

let schema_cases = [
  "amount_value", "int:0";
  "enabled_value", "bool:false";
  "label_value", "text:";
  "payload_value", "bytes:";
  "digest_value", "bytes32:" ^ String.make 64 '0';
  "count64_value", "u64:0";
  "count128_value", "u128:0";
  "count256_value", "u256:0";
  "owner_value", "addr:";
  "add_one", "int:1";
]

let schema_checks () =
  let artifact = compile "state schema image" schema_source in
  let image =
    match Octra_vm.Bytecode.decode_image artifact.octb with
    | Ok image -> image
    | Error reason -> fail "state schema image" reason
  in
  let expected =
    Input.storage_kinds artifact.ast
    |> List.sort (fun (left, _) (right, _) -> String.compare left right)
  in
  begin
    match image.state with
    | Some actual when actual = expected -> ()
    | Some _ | None -> fail "state schema image" "schema differs"
  end;
  let legacy = compile "legacy octb" checkpoint_source in
  if not (String.equal legacy.octb (Octra_vm.Bytecode.encode legacy.code)) then
    fail "legacy octb" "encoding differs";
  let plain = compile "plain octb" plain_source in
  if not (String.equal plain.octb (Octra_vm.Bytecode.encode plain.code)) then
    fail "plain octb" "encoding differs";
  let malformed =
    Octra_vm.Bytecode.encode
      [|VM.LDI (0, VM.VString (Octra_vm.Bytecode.state_prefix ^ "AA==")); VM.STOP|]
  in
  begin
    match Octra_vm.Bytecode.decode_image malformed with
    | Error reason when includes reason "state schema is invalid" -> ()
    | Error reason -> fail "state schema malformed" reason
    | Ok _ -> fail "state schema malformed" "image accepted"
  end;
  let repeated =
    Octra_vm.Bytecode.encode
      ~state:["left", VM.StorageInt]
      [|VM.LDI
          (0, VM.VString
            (Octra_vm.Bytecode.state_encode ["right", VM.StorageBool]));
        VM.STOP|]
  in
  match Octra_vm.Bytecode.decode_image repeated with
  | Error reason when includes reason "state schema is repeated" -> ()
  | Error reason -> fail "state schema repeated" reason
  | Ok _ -> fail "state schema repeated" "image accepted"

let run () =
  option_checks ();
  execute "foreach" "total" foreach_source
  |> result "foreach" "int:60";
  let nested = execute "checkpoint" "nested" checkpoint_source in
  result "checkpoint" "int:0" nested;
  storage_count "checkpoint" 0 nested;
  execute ~args:[VM.VBool true] "bool set" "set" bool_source
  |> result "bool set" "bool:true";
  execute "bool default" "get" bool_source
  |> result "bool default" "bool:false";
  execute "list delete" "run" delete_source
  |> result "list delete" "text:2:[a][c]";
  execute "single key" "run" single_key_source
  |> result "single key" "int:1";
  let map = execute "map namespace" "run" map_source in
  result "map namespace" "int:111" map;
  storage_count "map namespace" 2 map;
  execute "list namespace" "run" list_namespace_source
  |> result "list namespace" "int:2";
  let armed = execute "guard arm" "arm" guard_source in
  execute ~storage:armed.storage "guard namespace" "run" guard_source
  |> result "guard namespace" "int:1";
  execute
    ~args:[VM.VString "abc"; VM.VInt (Z.of_int 5)]
    "tuple"
    "run"
    tuple_source
  |> result "tuple" "int:6";
  let same_source = execute "legacy same source" "same" legacy_value_source in
  let same_octb = execute_octb "legacy same OCTB" "same" legacy_value_source in
  result "legacy same source" "bool:true" same_source;
  result "legacy same OCTB" "bool:true" same_octb;
  same_runtime "legacy same" same_source same_octb;
  let differs_source =
    execute "legacy differs source" "differs" legacy_value_source
  in
  let differs_octb =
    execute_octb "legacy differs OCTB" "differs" legacy_value_source
  in
  result "legacy differs source" "bool:false" differs_source;
  result "legacy differs OCTB" "bool:false" differs_octb;
  same_runtime "legacy differs" differs_source differs_octb;
  let rejected = attempt "legacy require" "reject" legacy_value_source in
  if rejected.stop <> Local.Reverted then
    fail "legacy require" "call returned";
  if not
      (includes
        (Aml_cli.stop_reason rejected)
        "error = Require message = text:denied")
  then fail "legacy require" "reason differs";
  List.iter
    (fun (method_name, expected) ->
      let source = execute "state schema source" method_name schema_source in
      let octb = execute_octb "state schema OCTB" method_name schema_source in
      result ("state schema source " ^ method_name) expected source;
      result ("state schema OCTB " ^ method_name) expected octb;
      if source.result <> octb.result then
        fail ("state schema parity " ^ method_name) "result differs")
    schema_cases;
  execute_octb
    ~storage:["amount", "41"]
    "state schema stored"
    "add_one"
    schema_source
  |> result "state schema stored" "int:42";
  schema_checks ();
  reverts "empty pop" "run" empty_pop_source