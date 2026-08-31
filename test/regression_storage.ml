(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

open Regression_support

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
  List.iter
    (fun (method_name, expected) ->
      execute_octb "state schema" method_name schema_source
      |> result ("state schema " ^ method_name) expected)
    schema_cases;
  execute_octb
    ~storage:["amount", "41"]
    "state schema stored"
    "add_one"
    schema_source
  |> result "state schema stored" "int:42";
  schema_checks ();
  reverts "empty pop" "run" empty_pop_source