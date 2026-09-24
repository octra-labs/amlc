(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

open Regression_support

let wrong_return = {|
program WrongReturn {
  pure fn value(): u64 { return "abc" }
}
|}

let missing_return = {|
contract MissingReturn {
  public fn value(): address { let number = 1 }
}
|}

let wrong_local = {|
contract WrongLocal {
  public fn value(): int {
    let enabled: bool = 7
    return 1
  }
}
|}

let wrong_call = {|
contract WrongCall {
  private fn add(value: int): int { return value + 1 }
  public fn value(): int { return add("7") }
}
|}

let wrong_state = {|
contract WrongState {
  state { enabled: bool }
  public fn set(): bool {
    self.enabled = 1
    return self.enabled
  }
}
|}

let cyclic_const = {|
contract CyclicConst {
  const left = right + 1
  const right = left + 1
  pure fn value(): int { return left }
}
|}

let wrong_operator = {|
contract WrongOperator {
  pure fn value(): int { return true - 1 }
}
|}

let opaque_zero = {|
contract OpaqueZero {
  public view fn present(): bool {
    let key = fhe_load_pk(caller)
    return key != 0
  }
}
|}

let uint_name = {|
program UIntName {
  public pure fn keep(value: uint): uint { return value }
}
|}

let u256_name = {|
program UIntName {
  public pure fn keep(value: u256): u256 { return value }
}
|}

let strict_type_names = {|
program StrictTypeNames {
  struct sint { value: int }
  struct vec { value: int }
  struct seq { value: int }
}
|}

let split_calls = {|
program Parts {
  public view fn size(text: string, sep: string): int {
    return split(text, sep)
  }
  public view fn piece(text: string, sep: string, index: int): string {
    let count = split(text, sep)
    return to_string(mget(100 + index))
  }
  public view fn text(text: string, sep: string): string {
    return join(split(text, sep), "|")
  }
}
|}

let split_list = {|
program Parts {
  public view fn parts(text: string): list[string] {
    return split(text, ",")
  }
}
|}

let split_math = {|
program Parts {
  public view fn size(text: string): int {
    let count: int = split(text, ",")
    require(count > 0, "parts missing")
    return count * 2
  }
}
|}

let split_checks () =
  let compiled = compile "split count" split_calls in
  let digest = Digestif.SHA256.(digest_string compiled.octb |> to_hex) in
  if digest <> "bc4bf8f49e3785c207ccdfe6897198781b7ccc5257ed0f5e54506c5a23bc7ce4" then
    fail "split" "instruction image changed";
  refuse "split list" "return type differs expected = list actual = int" split_list;
  let arithmetic = execute ~args:[VM.VString "a,,b"]
    "split arithmetic" "size" split_math in
  result "split arithmetic" "int:6" arithmetic;
  let image = match Octra_vm.Bytecode.decode_image compiled.octb with
    | Ok value -> value
    | Error reason -> fail "split" reason in
  let storage = ["saved", "value"] in
  let run ?(limit = 100000) code method_name args =
    let config = Local.config ~view:true ~strict_values:true ~storage
      ~limit ~method_name ~args () in
    match Local.run ~trace:false config code with
    | Error reason -> fail "split" (Local.error_text reason)
    | Ok out -> out in
  let check method_name args expected =
    let direct = run compiled.code method_name args in
    let detached = run image.code method_name args in
    same_runtime "split" direct detached;
    if direct.stop <> Local.Returned || direct.result <> expected
      || direct.storage <> storage || direct.events <> [] || direct.closes <> [] then
      fail "split" ("result = " ^ Local.value_text direct.result) in
  let pieces text sep =
    let size = String.length text in
    let width = String.length sep in
    let rec seek from at acc =
      if at + width > size then
        List.rev (String.sub text from (size - from) :: acc)
      else if String.sub text at width = sep then
        seek (at + width) (at + width)
          (String.sub text from (at - from) :: acc)
      else seek from (at + 1) acc in
    seek 0 0 [] in
  let rec words left =
    if left = 0 then [""]
    else words (left - 1) |> List.concat_map (fun word ->
      List.map (fun letter -> word ^ letter) ["a"; ":"; ","]) in
  let texts = List.init 5 words |> List.concat in
  List.iter (fun text ->
    List.iter (fun sep ->
      let parts = pieces text sep in
      let args = [VM.VString text; VM.VString sep] in
      check "size" args (VM.VInt (Z.of_int (List.length parts)));
      check "text" args (VM.VString (String.concat "|" parts));
      List.iteri (fun index part ->
        check "piece" (args @ [VM.VInt (Z.of_int index)]) (VM.VString part)) parts)
      [","; "::"; "a"; "aa"; ":::"])
    (texts @ ["left\000right\000"; "\255,\254,,"; "aaaaa"]);
  List.iter (fun (sep, limit) ->
    let args = [VM.VString "a,b"; VM.VString sep] in
    let direct = run ~limit compiled.code "size" args in
    let detached = run ~limit image.code "size" args in
    same_runtime "split limit" direct detached;
    if direct.stop <> Local.Reverted || direct.effort > limit
      || direct.storage <> storage || direct.events <> [] || direct.closes <> [] then
      fail "split limit" "refusal differs") ["", 1000; ",", 10]

let address_calls = {|
program AddressText {
  state { count: int }
  private pure fn accept(value: address): address { return value }
  public fn cast(text: string): address {
    self.count = self.count + 1
    return accept(to_address(text))
  }
  public view fn same(value: address): address { return to_address(value) }
  public fn discard(text: string): bool {
    self.count = self.count + 1
    to_address(text)
    return true
  }
  public view fn piece(text: string): address {
    return to_address(substr(text, 1, len(text) - 2))
  }
}
|}

let address_checks () =
  let valid = "oct" ^ String.make 44 '1' in
  let storage = ["count", "7"] in
  let check method_name text accepted =
    let args = [VM.VString text] in
    let direct = attempt ~args ~storage "address" method_name address_calls in
    let detached = attempt_octb ~args ~storage "address" method_name address_calls in
    same_runtime "address" direct detached;
    if accepted then begin
      let expected = if method_name = "discard" then VM.VBool true else VM.VString valid in
      if direct.stop <> Local.Returned || direct.result <> expected then
        fail "address" "checked conversion differs";
      let expected = if method_name = "cast" || method_name = "discard" then "8" else "7" in
      storage_value "address" "count" expected direct
    end else if direct.stop <> Local.Reverted || direct.storage <> storage then
      fail "address" "invalid text preserved a write"
  in
  check "cast" valid true;
  check "discard" valid true;
  check "same" valid true;
  check "piece" ("[" ^ valid ^ "]") true;
  List.iter (fun text -> check "cast" text false; check "discard" text false)
    [""; "oct"; "wrong"; valid ^ " "; " " ^ valid; "oct" ^ String.make 44 '0'];
  refuse "address implicit" "return type differs expected = address actual = string"
    "program Text { fn cast(text: string): address { return text } }";
  List.iter (fun expr ->
    refuse "address input" "address input type differs"
      ("program Text { fn cast(): address { return " ^ expr ^ " } }"))
    ["to_address(1)"; "to_address(true)"; "to_address([1])"];
  List.iter (fun expr ->
    refuse "address arity" "to_address requires one argument"
      ("program Text { fn cast(): address { return " ^ expr ^ " } }"))
    ["to_address()"; "to_address(\"\", \"\")"]

let run () =
  address_checks ();
  split_checks ();
  refuse "return type" "return type differs" wrong_return;
  refuse "missing return" "function return is not total" missing_return;
  refuse "local type" "local initializer type differs" wrong_local;
  refuse "call type" "function argument type differs" wrong_call;
  refuse "state type" "state assignment type differs" wrong_state;
  refuse "cyclic const" "constant dependency is cyclic" cyclic_const;
  refuse "operator type" "arithmetic operand type differs" wrong_operator;
  ignore (compile "opaque zero" opaque_zero);
  let uint = compile "uint name" uint_name in
  let u256 = compile "u256 name" u256_name in
  if not (String.equal uint.octb u256.octb) then
    fail "uint name" "OCTB differs";
  let names =
    Octra_vm.Oct_parse.parse strict_type_names
    |> fun value -> value.Octra_vm.Oct_lang.structs
    |> List.map (fun value -> value.Octra_vm.Oct_lang.sd_name)
  in
  if names <> ["sint"; "vec"; "seq"] then
    fail "strict type names" "names differ"