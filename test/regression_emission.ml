(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

module Mach = Octra_vm.C_mach
module Octb = Octra_vm.C_octb
module Emit = Octra_vm.C_emit
module Nat = Octra_vm.C_nat
module Term = Octra_vm.C_term
module Type = Octra_vm.C_type
module Local = Octra_vm.Local_vm
module Vm = Octra_vm.Contract_vm
module Bytecode = Octra_vm.Bytecode
module Dump = Aml_dump
module Input = Octra_vm.Aml_input

let fail name = failwith ("emission " ^ name)

let nat name value =
  match Nat.of_int value with
  | Some found -> found
  | None -> fail name

let compile name source =
  match Octb.compile source with
  | Ok value -> value
  | Error error -> failwith (name ^ " reason = " ^ Octb.text error)

let expect name wanted (artifact : Octb.t) =
  if artifact.Octb.emission <> wanted then fail name

let int name wanted artifact =
  match artifact.Octb.result with
  | Some (Emit.Int found) when Z.equal wanted found -> ()
  | _ -> fail name

let local ?(trace = false) name artifact method_name args =
  let image =
    match Octra_vm.Bytecode.decode_image artifact.Octb.octb with
    | Ok value -> value
    | Error _ -> fail name
  in
  let config =
    Local.config
      ~view:true
      ~byte_result:Vm.Bytes_result
      ~method_name
      ~args
      ()
  in
  match Local.run ~trace config image.code with
  | Ok value -> value
  | Error _ -> fail name

let local_code name code method_name args =
  let config =
    Local.config
      ~view:true
      ~byte_result:Vm.Bytes_result
      ~method_name
      ~args
      ()
  in
  match Local.run ~trace:false config code with
  | Ok value -> value
  | Error _ -> fail name

let returned name outcome =
  match outcome.Local.stop with
  | Local.Returned -> ()
  | Local.Reverted | Local.Step_cap | Local.Host_operation _ -> fail name

let refused name outcome =
  match outcome.Local.stop with
  | Local.Reverted -> ()
  | Local.Returned | Local.Step_cap | Local.Host_operation _ -> fail name

let native name artifact =
  match Bytecode.decode_image artifact.Octb.octb with
  | Ok image -> image.code
  | Error _ -> fail name

let decoded name artifact =
  match Octb.decode artifact.Octb.octb with
  | Ok image -> image
  | Error _ -> fail name

let decoded_raw name raw =
  match Octb.decode raw with
  | Ok image -> image
  | Error _ -> fail name

let output name wanted artifact =
  match (decoded name artifact).Octb.output with
  | Some found when Type.equal wanted found -> ()
  | Some _ | None -> fail name

let body_at name code =
  let rec find pc =
    if pc = Array.length code then fail name
    else if code.(pc) = Vm.NOP then pc + 1
    else find (pc + 1)
  in
  find 7

let replace code at value =
  let out = Array.copy code in
  out.(at) <- value;
  out

let replace_first code select value =
  let out = Array.copy code in
  let rec find at =
    if at = Array.length out then fail "operation mutation"
    else if select out.(at) then out.(at) <- value
    else find (at + 1)
  in
  find 0;
  out

let includes text part =
  let text_len = String.length text in
  let part_len = String.length part in
  let rec seek index =
    index + part_len <= text_len
    && (String.equal (String.sub text index part_len) part
        || seek (index + 1))
  in
  part_len = 0 || seek 0

let compile_refused name part source =
  match Octb.compile source with
  | Error error when includes (Octb.text error) part -> ()
  | Error error -> failwith (name ^ " reason = " ^ Octb.text error)
  | Ok _ -> fail name

let claimed name code =
  let raw = Bytecode.encode code in
  match Amlc_cli.octb_form raw with
  | Amlc_cli.Claimed _ -> raw
  | Amlc_cli.Typed _ | Amlc_cli.Generic -> fail name

let trailing_claim name artifact =
  match Amlc_cli.octb_form (artifact.Octb.octb ^ String.make 1 '\000') with
  | Amlc_cli.Claimed (Octb.Trailing_data 1) -> ()
  | Amlc_cli.Claimed _ | Amlc_cli.Typed _ | Amlc_cli.Generic -> fail name

let exact_claim name artifact =
  let raw =
    Bytecode.encode ~state:[("unused", Vm.StorageInt)]
      (native name artifact)
  in
  match Amlc_cli.octb_form raw with
  | Amlc_cli.Claimed Octb.Exact_image -> ()
  | Amlc_cli.Claimed _ | Amlc_cli.Typed _ | Amlc_cli.Generic -> fail name

let result_refused name code =
  match Octb.decode (claimed name code) with
  | Error Octb.Result_header -> ()
  | Error _ | Ok _ -> fail name

let opcode_refused name code =
  match Octb.decode (claimed name code) with
  | Error (Octb.Opcode _) -> ()
  | Error _ | Ok _ -> fail name

let register_refused name code =
  match Octb.decode (claimed name code) with
  | Error (Octb.Register_ref _) -> ()
  | Error _ | Ok _ -> fail name

let reject_empty () =
  let item = Term.bind Nat.zero Type.Zero Type.Int in
  let state = Term.bind Nat.one Type.One Type.Int in
  let body = Mach.Push (Emit.Int Z.zero, Mach.Done) in
  let code =
    Mach.Empty (Mach.SAtom,
      Mach.Push (Emit.Int (Z.of_int 9),
        Mach.Iter (Nat.zero, item, state, body, Mach.Done)))
  in
  if Option.is_some (Mach.replay code) then fail "empty erased binder"

let reject_choice () =
  let left = Term.bind Nat.zero Type.Zero Type.Int in
  let right = Term.bind Nat.one Type.Many Type.Int in
  let yes = Mach.Push (Emit.Int Z.one, Mach.Done) in
  let no = Mach.Push (Emit.Int (Z.of_int 2), Mach.Done) in
  let code =
    Mach.Push (Emit.Int (Z.of_int 3),
      Mach.Right
        (Mach.Choice (left, yes, right, no, Mach.SAtom, Mach.Done)))
  in
  if Option.is_some (Mach.replay code) then fail "choice erased binder"

let pool_checks () =
  let code =
    Array.init 32768 (fun index -> Vm.LDI (0, Vm.VInt (Z.of_int index)))
  in
  let raw = Bytecode.encode code in
  begin
    match Bytecode.decode_image raw with
    | Ok image when image.code = code && Array.length image.consts = 32768 -> ()
    | Ok _ | Error _ -> fail "constant pool capacity"
  end;
  let over =
    Array.init 32769 (fun index -> Vm.LDI (0, Vm.VInt (Z.of_int index)))
  in
  try
    ignore (Bytecode.encode over);
    fail "constant pool overflow"
  with
  | Invalid_argument reason
      when String.equal reason "constant count exceeds capacity" -> ()

let machine_limit_checks () =
  let rec deep depth =
    if depth = 0 then Term.Unit
    else
      let item = Term.bind (nat "machine limit item" (depth * 2))
        Type.Many Type.Unit in
      let state = Term.bind (nat "machine limit state" (depth * 2 + 1))
        Type.Many Type.Unit in
      Term.Vfold (
        Term.Vec (Type.Unit, [Term.Unit; Term.Unit]),
        Term.Unit,
        Term.fold item state (deep (depth - 1)))
  in
  let rec fork depth term =
    if depth = 0 then term
    else
      let next = fork (depth - 1) term in
      Term.If (Term.Bool true, next, next)
  in
  if Option.is_none (Mach.lower (fork 3 (deep 3))) then
    fail "machine finite emission";
  if Option.is_some (Mach.lower (fork 10 (deep 16))) then
    fail "machine emission limit"

let literal = {|
program Literal {
  term 42
}
|}

let branch = {|
program Branch {
  term if 4 < 5 then 42 else 0
}
|}

let choice = {|
program Choice {
  data Choice tag 1 = Yes(int) | No(int)
  term case make Choice Yes(42) as Choice of {
    Yes many value: int => value + 1 |
    No many value: int => value - 1
  }
}
|}

let choice_right = {|
program ChoiceRight {
  data Choice tag 1 = Yes(int) | No(int)
  term case make Choice No(42) as Choice of {
    Yes many value: int => value + 1 |
    No many value: int => value - 1
  }
}
|}

let option_some = {|
program OptionSome {
  data Option tag 1 = None(unit) | Some(int)
  term case make Option Some(42) as Option of {
    None many value: unit => 0 |
    Some many value: int => value
  }
}
|}

let folded = {|
program Folded {
  term fold vec[int](3, 5, 8) from 0 with
    many item: int, once state: int => item + state
}
|}

let empty = {|
program Empty {
  term fold vec[int]() from 9 with
    many item: int, once state: int => item + state
}
|}

let open_int = {|
program OpenInt {
  input many x: int
  input once y: int
  term let once z: int = y + 1 in
    x + z
}
|}

let open_bool = {|
program OpenBool {
  input many flag: bool
  term if flag then 11 else 3
}
|}

let open_bytes = {|
program OpenBytes {
  input many left: bytes[2]
  input once right: bytes[1]
  term cat(left, right)
}
|}

let order_lt = {|
program OrderLt {
  input many left: int
  input many right: int
  term left < right
}
|}

let order_le = {|
program OrderLe {
  input many left: int
  input many right: int
  term left <= right
}
|}

let order_gt = {|
program OrderGt {
  input many left: int
  input many right: int
  term left > right
}
|}

let order_ge = {|
program OrderGe {
  input many left: int
  input many right: int
  term left >= right
}
|}

let expansion () =
  let values = String.concat "," (List.init 500 (fun _ -> "1")) in
  "program Expansion { input many x: int term fold vec[int]("
  ^ values
  ^ ") from x with many outer: int, once state: int => fold vec[int]("
  ^ values
  ^ ") from state with many inner: int, once sum: int => sum + inner + outer }"

let has pred code = Array.exists pred code

let order_checks () =
  let lt = compile "order lt" order_lt in
  let le = compile "order le" order_le in
  let gt = compile "order gt" order_gt in
  let ge = compile "order ge" order_ge in
  let less = function Octb.Less _ -> true | _ -> false in
  let greater = function Octb.Greater _ -> true | _ -> false in
  let same = function Octb.Same _ -> true | _ -> false in
  if not (has less lt.code) || has greater lt.code || has same lt.code then
    fail "order lt code";
  if not (has greater le.code) || not (has same le.code) then
    fail "order le code";
  if not (has greater gt.code) || has less gt.code || has same gt.code then
    fail "order gt code";
  if not (has less ge.code) || not (has same ge.code) then
    fail "order ge code";
  let args = [Vm.VInt (Z.of_int 5); Vm.VInt (Z.of_int 5)] in
  let check name artifact wanted effort steps =
    let out = local name artifact "main" args in
    returned name out;
    begin
      match out.result with
      | Vm.VBool found when found = wanted -> ()
      | _ -> fail name
    end;
    if out.effort <> effort || out.steps <> steps then fail (name ^ " cost")
  in
  output "order lt output" Type.Bool lt;
  output "order le output" Type.Bool le;
  output "order gt output" Type.Bool gt;
  output "order ge output" Type.Bool ge;
  check "order lt" lt false 43 21;
  check "order le" le true 45 22;
  check "order gt" gt false 43 21;
  check "order ge" ge true 45 22

let decoder_checks int_artifact bool_artifact =
  let int_code = native "decode int" int_artifact in
  let count = Array.length int_code in
  let no_result =
    Array.append (Array.sub int_code 0 (count - 3)) [|Vm.STOP|]
  in
  result_refused "result absent" no_result;
  result_refused "result bypass"
    (replace int_code (body_at "result bypass" int_code) Vm.STOP);
  opcode_refused "host operation"
    (replace int_code (body_at "host operation" int_code) (Vm.SLOAD (0, "x")));
  let bool_code = native "decode bool" bool_artifact in
  let target =
    match bool_code.(Array.length bool_code - 2) with
    | Vm.JDEST value -> value
    | _ -> fail "result jump target"
  in
  result_refused "result jump"
    (replace bool_code (body_at "result jump" bool_code) (Vm.JMP target));
  refused "int result type"
    (local_code "int result type"
      (replace int_code (count - 4) (Vm.LDI (0, Vm.VBool true)))
      "main" [Vm.VInt Z.zero; Vm.VInt Z.zero]);
  let bool_count = Array.length bool_code in
  refused "bool result type"
    (local_code "bool result type"
      (replace bool_code (bool_count - 5) (Vm.LDI (0, Vm.VInt Z.one)))
      "main" [Vm.VInt Z.zero; Vm.VInt Z.zero]);
  let head = [
    Vm.JDEST 100;
    Vm.MLOAD (61, 1000);
    Vm.LDI (62, Vm.VString "main");
    Vm.EQ (63, 61, 62);
    Vm.JIF (63, 200);
    Vm.REVERT;
    Vm.JDEST 200;
  ] in
  let inputs =
    List.init 61 (fun index ->
      let reg = index + 1 in
      [
        Vm.MLOAD (reg, 1001 + index);
        Vm.LDI (61, Vm.VInt Z.zero);
        Vm.SUB (reg, reg, 61);
      ])
    |> List.concat
  in
  let tail = [
    Vm.NOP;
    Vm.LDI (61, Vm.VInt Z.zero);
    Vm.SUB (0, 0, 61);
    Vm.STOP;
  ] in
  register_refused "input count"
    (Array.of_list (head @ inputs @ tail))

let open_checks () =
  let int_artifact = compile "open int" open_int in
  let bool_artifact = compile "open bool" open_bool in
  let bytes_artifact = compile "open bytes" open_bytes in
  List.iter
    (fun artifact ->
      expect "open lowered" Mach.Lowered artifact;
      if Option.is_some artifact.Octb.result then fail "open result")
    [int_artifact; bool_artifact; bytes_artifact];
  trailing_claim "open trailing claim" int_artifact;
  exact_claim "open exact claim" int_artifact;
  let image =
    decoded "open decode" int_artifact
  in
  if not (String.equal (Dump.emission image) "lowered") then
    fail "open raw emission";
  if Array.length image.inputs <> 2
      || not (Type.equal image.inputs.(0) Type.Int)
      || not (Type.equal image.inputs.(1) Type.Int) then
    fail "open types";
  output "open int output" Type.Int int_artifact;
  output "open bytes output"
    (Type.Bytes (nat "open bytes length" 3)) bytes_artifact;
  decoder_checks int_artifact (compile "open order" order_lt);
  let int_out =
    local ~trace:true "open int" int_artifact "main"
      [Vm.VInt (Z.of_int 5); Vm.VInt (Z.of_int 7)]
  in
  returned "open int" int_out;
  begin
    match int_out.result with
    | Vm.VInt value when Z.equal value (Z.of_int 13) -> ()
    | _ -> fail "open int value"
  end;
  if int_out.effort <> 49 || int_out.steps <> 23 then fail "open int cost";
  let values =
    match Input.core_octb image.inputs ["int:5"; "int:7"] with
    | Ok values -> values
    | Error _ -> fail "open input values"
  in
  begin
    match Aml_cli.open_match image.code values int_out with
    | Ok () -> ()
    | Error _ -> fail "open machine match"
  end;
  let changed_result =
    replace_first image.code
      (function Octb.Plus _ -> true | _ -> false)
      (Octb.Minus (0, 1, 2))
  in
  begin
    match Aml_cli.open_match changed_result values int_out with
    | Error _ -> ()
    | Ok () -> fail "open result mutation"
  end;
  let changed_cost = Array.append [|Octb.Noop|] image.code in
  begin
    match Aml_cli.open_match changed_cost values int_out with
    | Error _ -> ()
    | Ok () -> fail "open cost mutation"
  end;
  refused "open int type"
    (local "open int type" int_artifact "main"
      [Vm.VBool true; Vm.VInt (Z.of_int 7)]);
  refused "open bool type"
    (local "open bool type" bool_artifact "main" [Vm.VInt Z.one]);
  refused "open method"
    (local "open method" int_artifact "other"
      [Vm.VInt (Z.of_int 5); Vm.VInt (Z.of_int 7)]);
  let bool_out = local "open bool" bool_artifact "main" [Vm.VBool true] in
  returned "open bool" bool_out;
  begin
    match bool_out.result with
    | Vm.VInt value when Z.equal value (Z.of_int 11) -> ()
    | _ -> fail "open bool value"
  end;
  let bytes_out =
    local "open bytes" bytes_artifact "main"
      [Vm.VBytes "\001\002"; Vm.VBytes "\003"]
  in
  returned "open bytes" bytes_out;
  begin
    match bytes_out.result with
    | Vm.VBytes value when String.equal value "\001\002\003" -> ()
    | _ -> fail "open bytes value"
  end;
  refused "open bytes type"
    (local "open bytes type" bytes_artifact "main"
      [Vm.VString "\001\002"; Vm.VBytes "\003"]);
  let bytes_code = native "open bytes result type" bytes_artifact in
  refused "open bytes result type"
    (local_code "open bytes result type"
      (replace bytes_code
        (Array.length bytes_code - 12)
        (Vm.LDI (0, Vm.VString "\001\002\003")))
      "main" [Vm.VBytes "\001\002"; Vm.VBytes "\003"])

let emission_checks literal specialized =
  if String.equal literal.Octb.octb specialized.Octb.octb then
    fail "provenance bytes";
  let lowered = decoded "lowered decode" literal in
  let specialized = decoded "specialized decode" specialized in
  if not (String.equal (Octb.image_emission lowered) "lowered") then
    fail "lowered provenance";
  if not (String.equal (Octb.image_emission specialized) "specialized") then
    fail "specialized provenance";
  if not (String.equal (Octb.image_veil lowered) "none")
      || not (String.equal (Octb.image_veil specialized) "none") then
    fail "plain veil status";
  let prior =
    Bytecode.encode ~emission:Bytecode.Lowered (native "prior veil" literal)
    |> decoded_raw "prior veil"
  in
  if not (String.equal (Octb.image_emission prior) "lowered")
      || not (String.equal (Octb.image_veil prior) "unknown")
      || prior.code <> lowered.code then
    fail "prior veil status";
  let raw =
    match Octb.encode literal.code with
    | Ok value -> value
    | Error _ -> fail "opaque encode"
  in
  if String.equal raw literal.octb then fail "opaque bytes";
  if not
      (String.equal (Octb.image_emission (decoded_raw "opaque decode" raw))
        "opaque")
  then fail "opaque provenance";
  if not
      (String.equal (Octb.image_veil (decoded_raw "opaque veil" raw)) "unknown")
  then fail "opaque veil status";
  let invalid =
    Bytecode.encode
      [|
        Vm.LDI (0, Vm.VString (Bytecode.emission_prefix ^ "invalid"));
        Vm.STOP;
      |]
  in
  begin
    match Bytecode.decode_image invalid with
    | Error reason when includes reason "AML emission is invalid" -> ()
    | Ok _ | Error _ -> fail "invalid provenance"
  end;
  begin
    match Amlc_cli.octb_form invalid with
    | Amlc_cli.Claimed Octb.Emission_invalid -> ()
    | Amlc_cli.Claimed _ | Amlc_cli.Typed _ | Amlc_cli.Generic ->
      fail "invalid provenance route"
  end;
  let repeated =
    Bytecode.encode ~emission:Bytecode.Lowered
      [|
        Vm.LDI (0, Vm.VString (Bytecode.emission_encode Bytecode.Specialized));
        Vm.STOP;
      |]
  in
  begin
    match Bytecode.decode_image repeated with
    | Error reason when includes reason "AML emission is repeated" -> ()
    | Ok _ | Error _ -> fail "repeated provenance"
  end;
  begin
    match Amlc_cli.octb_form repeated with
    | Amlc_cli.Claimed Octb.Emission_repeated -> ()
    | Amlc_cli.Claimed _ | Amlc_cli.Typed _ | Amlc_cli.Generic ->
      fail "repeated provenance route"
  end;
  let invalid_veil =
    Bytecode.encode
      [|
        Vm.LDI (0, Vm.VString (Bytecode.veil_prefix ^ "invalid"));
        Vm.STOP;
      |]
  in
  begin
    match Amlc_cli.octb_form invalid_veil with
    | Amlc_cli.Claimed Octb.Veil_invalid -> ()
    | Amlc_cli.Claimed _ | Amlc_cli.Typed _ | Amlc_cli.Generic ->
      fail "invalid veil route"
  end;
  begin
    let invalid : Bytecode.veil = { count = Z.zero; depth = Z.one } in
    try
      ignore (Bytecode.veil_encode invalid);
      fail "invalid veil encode"
    with Invalid_argument _ -> ()
  end;
  let excessive : Bytecode.veil = {
    count = Z.of_int (Nat.max + 1);
    depth = Z.zero;
  } in
  let excessive_veil = Bytecode.encode ~veil:excessive [|Vm.STOP|] in
  begin
    match Amlc_cli.octb_form excessive_veil with
    | Amlc_cli.Claimed Octb.Veil_invalid -> ()
    | Amlc_cli.Claimed _ | Amlc_cli.Typed _ | Amlc_cli.Generic ->
      fail "excessive veil route"
  end;
  let first : Bytecode.veil = { count = Z.one; depth = Z.one } in
  let second : Bytecode.veil = { count = Z.of_int 2; depth = Z.one } in
  let repeated_veil =
    Bytecode.encode ~veil:first
      [|
        Vm.LDI (0, Vm.VString (Bytecode.veil_encode second));
        Vm.STOP;
      |]
  in
  match Amlc_cli.octb_form repeated_veil with
  | Amlc_cli.Claimed Octb.Veil_repeated -> ()
  | Amlc_cli.Claimed _ | Amlc_cli.Typed _ | Amlc_cli.Generic ->
    fail "repeated veil route"

let run () =
  pool_checks ();
  machine_limit_checks ();
  reject_empty ();
  reject_choice ();
  open_checks ();
  compile_refused "open expansion" "fuel limit = 1000000 needed ="
    (expansion ());
  order_checks ();
  let literal = compile "literal" literal in
  let branch = compile "branch" branch in
  let folded = compile "folded" folded in
  let empty = compile "empty" empty in
  let choice = compile "choice" choice in
  let choice_right = compile "choice right" choice_right in
  let option_some = compile "option some" option_some in
  expect "literal" Mach.Lowered literal;
  expect "branch" Mach.Lowered branch;
  expect "folded" Mach.Lowered folded;
  expect "empty" Mach.Lowered empty;
  expect "choice" Mach.Lowered choice;
  expect "choice right" Mach.Lowered choice_right;
  expect "option some" Mach.Specialized option_some;
  int "folded result" (Z.of_int 16) folded;
  int "empty result" (Z.of_int 9) empty;
  int "choice result" (Z.of_int 43) choice;
  int "choice right result" (Z.of_int 41) choice_right;
  emission_checks literal option_some;
  if not
      (String.equal (Dump.emission (decoded "lowered dump" literal)) "lowered")
  then fail "lowered dump emission";
  if not
      (String.equal
        (Dump.emission (decoded "specialized dump" option_some))
        "specialized")
  then fail "specialized dump emission";
  if not (String.equal (Mach.emission_text Mach.Lowered) "lowered") then
    fail "lowered text";
  if not
      (String.equal (Mach.emission_text Mach.Specialized) "specialized")
  then fail "specialized text"