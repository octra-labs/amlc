(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

open Regression_support

let read_int = {|
program ReadInt {
  state { total: int }
  form expect [] (many value: int) ->[many] int marks {read[7]:total} =
    read[7](value)
  public view fn check(value: int): int {
    return use expect[](value) as many out: int in out
  }
}
|}

let read_bool = {|
program ReadBool {
  state { enabled: bool }
  form expect [] (many value: bool) ->[many] bool marks {read[8]:enabled} =
    read[8](value)
  public view fn check(value: bool): bool {
    return use expect[](value) as many out: bool in out
  }
}
|}

let read_pure = {|
program ReadPure {
  state { total: int }
  form expect [] (many value: int) ->[many] int marks {read[7]:total} =
    read[7](value)
  public pure fn check(value: int): int {
    return use expect[](value) as many out: int in out
  }
}
|}

let read_direct = {|
program ReadDirect {
  state { total: int }
  form expect [] (many value: int) ->[many] int marks {read[7]:total} =
    read[7](value)
  public view fn check(value: int): int { return expect(value) }
}
|}

let read_absent = {|
program ReadAbsent {
  state { total: int }
  form expect [] (many value: int) ->[many] int marks {read[7]:missing} =
    read[7](value)
  public view fn check(value: int): int {
    return use expect[](value) as many out: int in out
  }
}
|}

let read_type = {|
program ReadType {
  state { total: bool }
  form expect [] (many value: int) ->[many] int marks {read[7]:total} =
    read[7](value)
  public view fn check(value: int): int {
    return use expect[](value) as many out: int in out
  }
}
|}

let read_unproved = {|
program ReadUnproved {
  state { total: int }
  form expect [] (many value: int) ->[many] int marks {read[8]:total} =
    read[7](value)
  public view fn check(value: int): int {
    return use expect[](value) as many out: int in out
  }
}
|}

let read_repeated = {|
program ReadRepeated {
  state { total: int }
  form expect [] (many value: int) ->[many] int
    marks {read[7]:total, read[7]:total} = read[7](value)
  public view fn check(value: int): int {
    return use expect[](value) as many out: int in out
  }
}
|}

let read_outside = {|
program ReadOutside {
  state { total: int }
  public view fn check(value: int): int { return read[7](value) }
}
|}

let fault = {|
program Fault {
  error Denied(403, "denied")
  form deny [] (many value: int) ->[many] int marks {fail[9]:Denied} =
    fail[9](value)
  public fn reject(value: int): int {
    return use deny[](value) as many out: int in out
  }
}
|}

let fault_pure = {|
program FaultPure {
  error Denied(403, "denied")
  form deny [] (many value: int) ->[many] int marks {fail[9]:Denied} =
    fail[9](value)
  public pure fn reject(value: int): int {
    return use deny[](value) as many out: int in out
  }
}
|}

let fault_direct = {|
program FaultDirect {
  error Denied(403, "denied")
  form deny [] (many value: int) ->[many] int marks {fail[9]:Denied} =
    fail[9](value)
  public fn reject(value: int): int { return deny(value) }
}
|}

let fault_absent = {|
program FaultAbsent {
  error Denied(403, "denied")
  form deny [] (many value: int) ->[many] int marks {fail[9]:Missing} =
    fail[9](value)
  public fn reject(value: int): int {
    return use deny[](value) as many out: int in out
  }
}
|}

let fault_unproved = {|
program FaultUnproved {
  error Denied(403, "denied")
  form deny [] (many value: int) ->[many] int marks {fail[8]:Denied} =
    fail[9](value)
  public fn reject(value: int): int {
    return use deny[](value) as many out: int in out
  }
}
|}

let fault_repeated = {|
program FaultRepeated {
  error Denied(403, "denied")
  form deny [] (many value: int) ->[many] int
    marks {fail[9]:Denied, fail[9]:Denied} = fail[9](value)
  public fn reject(value: int): int {
    return use deny[](value) as many out: int in out
  }
}
|}

let fault_outside = {|
program FaultOutside {
  error Denied(403, "denied")
  public fn reject(value: int): int { return fail[9](value) }
}
|}

let effect_names = {|
program EffectNames {
  private pure fn read(value: int): int { return value + 1 }
  private pure fn fail(value: int): int { return value + 2 }
  public pure fn run(value: int): int { return read(value) + fail(value) }
}
|}

let point_ops = {|
program PointOps {
  public fn identity(): bytes {
    return pedersen_identity()
  }
  public fn add(left: bytes, right: bytes): bytes {
    return pedersen_add(left, right)
  }
  public fn sub(left: bytes, right: bytes): bytes {
    return pedersen_sub(left, right)
  }
}
|}

let witness name compiled =
  match Octra_vm.Bytecode.decode_image compiled.Source.octb with
  | Ok { proof = Some proof; state; _ } ->
    let image = Octra_vm.Bytecode.encode ?state compiled.code in
    begin
      match Octra_vm.Aml_call.verify ~image compiled.code proof with
      | Ok () -> proof, image
      | Error error -> fail name (Octra_vm.Aml_call.text error)
    end
  | Ok _ | Error _ -> fail name "proof is absent"

let differs name proof image code =
  match Octra_vm.Aml_call.verify ~image code proof with
  | Error (Octra_vm.Aml_call.Differs _) -> ()
  | Error error -> fail name (Octra_vm.Aml_call.text error)
  | Ok () -> fail name "changed operation accepted"

let cost name effort steps outcome =
  if outcome.Local.effort <> effort || outcome.steps <> steps then
    fail name
      (Printf.sprintf "effort = %d steps = %d"
        outcome.effort outcome.steps)

let read_checks () =
  let compiled = compile "read compile" read_int in
  if not
      (Array.exists
        (function VM.SLOAD (_, "total") -> true | _ -> false)
        compiled.code)
  then fail "read compile" "state operation is absent";
  let proof, image = witness "read compile" compiled in
  compiled.code
  |> Array.map
    (function
      | VM.SLOAD (reg, "total") -> VM.SLOAD (reg, "other")
      | op -> op)
  |> differs "read mutation" proof image;
  let args = [VM.VInt (Z.of_int 5)] in
  let storage = ["total", "5"] in
  let source = execute ~args ~storage "read source" "check" read_int in
  let octb = execute_octb ~args ~storage "read OCTB" "check" read_int in
  result "read source" "int:5" source;
  storage_value "read source" "total" "5" source;
  same_runtime "read" source octb;
  cost "read cost" 66 23 source;
  let bool_args = [VM.VBool true] in
  let bool_storage = ["enabled", "true"] in
  let bool_source =
    execute ~args:bool_args ~storage:bool_storage
      "read bool source" "check" read_bool
  in
  let bool_octb =
    execute_octb ~args:bool_args ~storage:bool_storage
      "read bool OCTB" "check" read_bool
  in
  result "read bool source" "bool:true" bool_source;
  same_runtime "read bool" bool_source bool_octb;
  cost "read bool cost" 68 23 bool_source;
  let wrong_args = [VM.VInt (Z.of_int 6)] in
  let wrong_source =
    attempt ~args:wrong_args ~storage "read mismatch source" "check" read_int
  in
  let wrong_octb =
    attempt_octb ~args:wrong_args ~storage "read mismatch OCTB" "check" read_int
  in
  if wrong_source.stop <> Local.Reverted then
    fail "read mismatch source" "value accepted";
  same_runtime "read mismatch" wrong_source wrong_octb;
  refuse "read pure"
    "pure function form marks are not empty = expect" read_pure;
  refuse "read direct" "form requires explicit use = expect" read_direct;
  refuse "read absent"
    "effect target is absent target = state:missing" read_absent;
  refuse "read type"
    "effect site type differs atom = read<7> expected = bool actual = int"
    read_type;
  refuse "read unproved" "function marks exceeded" read_unproved;
  refuse "read repeated" "effect atom is repeated atom = read<7>"
    read_repeated;
  refuse "read outside" "effect atoms are available only in form bodies"
    read_outside

let fault_checks () =
  let compiled = compile "fault compile" fault in
  if not
      (Array.exists
        (function VM.EMIT ("Error:Denied", [_; _; _]) -> true | _ -> false)
        compiled.code)
      || not (Array.exists (fun op -> op = VM.REVERT) compiled.code)
  then fail "fault compile" "fault operation is absent";
  let proof, image = witness "fault compile" compiled in
  compiled.code
  |> Array.map
    (function
      | VM.EMIT ("Error:Denied", regs) -> VM.EMIT ("Error:Changed", regs)
      | op -> op)
  |> differs "fault mutation" proof image;
  let args = [VM.VInt (Z.of_int 9)] in
  let source = attempt ~args "fault source" "reject" fault in
  let octb = attempt_octb ~args "fault OCTB" "reject" fault in
  if source.stop <> Local.Reverted then fail "fault source" "fault returned";
  begin
    match source.events with
    | [event]
        when String.equal event.VM.event "Error:Denied"
          && event.values = [
            VM.VInt (Z.of_int 403);
            VM.VString "denied";
            VM.VInt (Z.of_int 9);
          ] -> ()
    | _ -> fail "fault source" "error event differs"
  end;
  if not
      (String.equal (Aml_cli.stop_reason source)
        "execution stopped stop = reverted error = Denied code = 403 message = text:denied effort = 63 steps = 18")
  then fail "fault source" "error reason differs";
  same_runtime "fault" source octb;
  cost "fault cost" 63 18 source;
  refuse "fault pure"
    "pure function form marks are not empty = deny" fault_pure;
  refuse "fault direct" "form requires explicit use = deny" fault_direct;
  refuse "fault absent"
    "effect target is absent target = error:Missing" fault_absent;
  refuse "fault unproved" "function marks exceeded" fault_unproved;
  refuse "fault repeated" "effect atom is repeated atom = fail<9>"
    fault_repeated;
  refuse "fault outside" "effect atoms are available only in form bodies"
    fault_outside

let name_checks () =
  let args = [VM.VInt (Z.of_int 5)] in
  let source = execute ~args "effect names source" "run" effect_names in
  let octb = execute_octb ~args "effect names OCTB" "run" effect_names in
  result "effect names source" "int:13" source;
  same_runtime "effect names" source octb

let point_checks () =
  let compiled = compile "point compile" point_ops in
  if not
      (Array.exists
        (function VM.FHE_PEDERSEN_ADD _ -> true | _ -> false)
        compiled.code)
  then fail "point compile" "addition operation is absent";
  if not
      (Array.exists
        (function VM.FHE_PEDERSEN_SUB _ -> true | _ -> false)
        compiled.code)
  then fail "point compile" "subtraction operation is absent";
  if not
      (Array.exists
        (function VM.FHE_PEDERSEN_IDENTITY _ -> true | _ -> false)
        compiled.code)
  then fail "point compile" "identity operation is absent";
  if Octra_vm.Bytecode.op_tag (VM.FHE_PEDERSEN_ADD (0, 1, 2)) <> 0x5D
      || Octra_vm.Bytecode.op_tag (VM.FHE_PEDERSEN_SUB (0, 1, 2)) <> 0x5E
      || Octra_vm.Bytecode.op_tag (VM.FHE_PEDERSEN_IDENTITY 0) <> 0x5F
  then fail "point wire" "operation tag differs";
  let point_code = [|
    VM.FHE_PEDERSEN_IDENTITY 0;
    VM.FHE_PEDERSEN_ADD (1, 2, 3);
    VM.FHE_PEDERSEN_SUB (4, 5, 6);
  |] in
  if Octra_vm.Assembler.parse (Octra_vm.Assembler.emit point_code) <> point_code
  then fail "point assembler" "instruction round trip differs";
  begin
    match Octra_vm.Bytecode.decode_image compiled.octb with
    | Ok image when image.code = compiled.code -> ()
    | Ok _ | Error _ -> fail "point wire" "detached code differs"
  end;
  let args = [VM.VBytes (String.make 32 '\001'); VM.VBytes (String.make 32 '\002')] in
  let added = attempt ~args "point add" "add" point_ops in
  let subtracted = attempt ~args "point sub" "sub" point_ops in
  let identity = attempt "point identity" "identity" point_ops in
  begin
    match added.stop, subtracted.stop, identity.stop with
    | Local.Host_operation (_, "fhe"),
      Local.Host_operation (_, "fhe"),
      Local.Host_operation (_, "fhe") -> ()
    | _ -> fail "point host" "operation class differs"
  end

let state_checks () =
  let reference = String.concat "" (List.init 4 (fun _ -> "0123456789abcdef")) in
  let key = "814eeb04a0e39472f275b72b6bce0f161932bb06f44cb76a455d0ca884612ad6" in
  let forms = [reference; String.uppercase_ascii reference;
    " \t" ^ reference ^ "\r\n"; "\012" ^ reference ^ "\t"] in
  List.iter (fun raw ->
    if Octra_vm.Contract_vm_host.state_path_key raw <> Some key then
      fail "state path" "key differs") forms;
  let invalid = [""; String.make 63 'a'; String.make 65 'a';
    "0x" ^ reference; String.make 64 'g'; String.make 64 '\000';
    "\194\160" ^ reference; reference ^ "\194\160";
    String.sub reference 0 31 ^ " " ^ String.sub reference 32 32] in
  List.iter (fun raw ->
    if Octra_vm.Contract_vm_host.state_path_key raw <> None then
      fail "state path" "invalid reference accepted") invalid;
  let source = {|
program StateRead {
  public view fn class_of(reference: string): string {
    return circle_state_class(reference)
  }
  public view fn expires(reference: string): int {
    return circle_state_expire_after(reference)
  }
  public view fn is_mutable(reference: string): bool {
    return circle_state_mutable(reference)
  }
}
|} in
  let storage = List.sort compare [
    "state_descriptor:" ^ key ^ ":state_class", "balance_cell";
    "state_descriptor:" ^ key ^ ":mutable_state", "true";
    "state_policy:" ^ key ^ ":expire_after_epoch", "42";
  ] in
  let methods = ["class_of", "text:balance_cell";
    "expires", "int:42"; "is_mutable", "bool:true"] in
  List.iter (fun raw ->
    let args = [VM.VString raw] in
    List.iter (fun (method_name, expected) ->
      let direct = execute ~args ~storage "state source" method_name source in
      let detached = execute_octb ~args ~storage "state OCTB" method_name source in
      result "state source" expected direct;
      same_runtime "state path" direct detached;
      if direct.storage <> storage || direct.events <> [] || direct.closes <> [] then
        fail "state path" "read changed state") methods) forms;
  List.iter (fun raw ->
    let args = [VM.VString raw] in
    let direct = attempt ~args ~storage "state invalid" "class_of" source in
    let detached = attempt_octb ~args ~storage "state invalid" "class_of" source in
    if direct.stop <> Local.Reverted then fail "state invalid" "reference accepted";
    if direct.storage <> storage || direct.events <> [] || direct.closes <> [] then
      fail "state invalid" "refusal changed state";
    same_runtime "state invalid" direct detached) invalid

let member_reads = {|
program MemberRead {
  public view fn size(reference: string): int {
    return circle_object_member_count(reference)
  }
  public view fn contains(reference: string, member: string): bool {
    return circle_object_has_member(reference, member)
  }
  public view fn at(reference: string, index: int): string {
    return circle_object_member_ref_at(reference, index)
  }
}
|}

let member_checks () =
  let storage = List.sort compare [
    "object_member:group:a:state_ref", "invalid";
    "object_member:group:b:state_ref", " \t" ^ String.make 64 'B' ^ "\n";
    "object_member:group:c:state_ref", "";
    "object_member:group:d:status", "active";
    "object_member:group::state_ref", String.make 64 'a';
    "object_member:other:x:state_ref", String.make 64 'a';
    "object_member:nested:a:state_ref", String.make 64 'a';
    "object_member:nested:a:b:state_ref", String.make 64 'a';
  ] in
  let cases = [
    "size", [VM.VString "group"], "int:3";
    "size", [VM.VString "absent"], "int:0";
    "contains", [VM.VString "group"; VM.VString "a"], "bool:false";
    "contains", [VM.VString "group"; VM.VString "b"], "bool:true";
    "contains", [VM.VString "group"; VM.VString "d"], "bool:false";
    "contains", [VM.VString "group"; VM.VString ""], "bool:true";
    "at", [VM.VString "group"; VM.VInt Z.zero], "text:a";
    "at", [VM.VString "group"; VM.VInt Z.one], "text:b";
    "at", [VM.VString "group"; VM.VInt (Z.of_int 3)], "text:";
    "at", [VM.VString "group"; VM.VInt Z.minus_one], "text:";
    "at", [VM.VString "nested"; VM.VInt Z.zero], "text:a:b";
    "at", [VM.VString "nested"; VM.VInt Z.one], "text:a";
  ] in
  List.iter (fun (method_name, args, expected) ->
    let direct = execute ~args ~storage "member source" method_name member_reads in
    let detached = execute_octb ~args ~storage "member OCTB" method_name member_reads in
    result "member source" expected direct;
    same_runtime "member" direct detached;
    if direct.storage <> storage || direct.events <> [] || direct.closes <> [] then
      fail "member" "read changed state") cases

let member_costs () =
  let storage = List.init 100 (fun index ->
    "object_member:group:" ^ string_of_int index ^ ":state_ref", "invalid") in
  let execute limit code =
    let config = Local.config ~limit ~storage ~view:true ~method_name:"read" ~args:[] () in
    match Local.run_at ~trace:true config ~entry:0 code with
    | Ok value -> value
    | Error reason -> fail "member cost" (Local.error_text reason) in
  List.iter (fun read ->
    let code = [|VM.LDI (0, VM.VString "group"); VM.LDI (2, VM.VInt Z.zero);
      read; VM.STOP|] in
    let limited = execute 100 code in
    if limited.stop <> Local.Reverted || limited.effort > 100 then
      fail "member cost" "scan exceeded budget";
    let enough = execute 1000 code in
    if enough.stop <> Local.Returned || enough.effort <> 553 then
      fail "member cost" "scan charge differs";
    if not (List.exists (fun frame -> frame.Local.op = read
      && frame.effort_after - frame.effort_before = 550) enough.frames) then
      fail "member cost" "scan frame differs")
    [VM.OBJECT_MEMBER_COUNT (1, 0); VM.OBJECT_MEMBER_REF_AT (1, 0, 2)];
  let code = [|VM.LDI (0, VM.VString "group"); VM.LDI (2, VM.VString "0");
    VM.OBJECT_HAS_MEMBER (1, 0, 2); VM.STOP|] in
  let output = execute 100 code in
  if output.stop <> Local.Returned || output.effort <> 33 then
    fail "member cost" "presence charged a scan"

let member_edits () =
  let storage = ["object_member:group:z:state_ref", String.make 64 'a'] in
  let key = "object_member:group:a:state_ref" in
  let program = [|
    VM.LDI (0, VM.VString "group"); VM.OBJECT_MEMBER_COUNT (1, 0);
    VM.LDI (2, VM.VString (String.make 64 'b')); VM.SSTORE (key, 2);
    VM.OBJECT_MEMBER_COUNT (3, 0); VM.LDI (4, VM.VInt Z.zero);
    VM.OBJECT_MEMBER_REF_AT (5, 0, 4); VM.SDEL key;
    VM.OBJECT_MEMBER_COUNT (6, 0); VM.OBJECT_MEMBER_REF_AT (7, 0, 4);
    VM.STOP;
  |] in
  let config = Local.config ~storage ~method_name:"write" ~args:[] () in
  let execute code = match Local.run_at ~trace:true config ~entry:0 code with
    | Ok value -> value
    | Error reason -> fail "member edits" (Local.error_text reason) in
  let output = execute program in
  if output.stop <> Local.Returned || output.storage <> storage
      || output.regs.(1) <> VM.VInt Z.one || output.regs.(3) <> VM.VInt (Z.of_int 2)
      || output.regs.(5) <> VM.VString "a" || output.regs.(6) <> VM.VInt Z.one
      || output.regs.(7) <> VM.VString "z" then
    fail "member edits" "reads did not follow storage changes";
  let refused = Array.append (Array.sub program 0 7) [|VM.REVERT|] |> execute in
  if refused.stop <> Local.Reverted || refused.storage <> storage then
    fail "member edits" "refusal did not preserve storage";
  let limited = Local.config ~storage ~limit:220 ~method_name:"write" ~args:[] () in
  let stopped = Local.config ~storage ~step_cap:4 ~method_name:"write" ~args:[] () in
  let unavailable = Array.append (Array.sub program 0 7) [|VM.BALANCE (0, 0)|] in
  List.iter (fun (config, code, reason) ->
    match Local.run_at ~trace:true config ~entry:0 code with
    | Ok output when output.stop = reason && output.storage = storage
        && output.closes = [] -> ()
    | Ok _ | Error _ -> fail "member edits" "interrupted writes became visible")
    [limited, program, Local.Reverted;
     stopped, program, Local.Step_cap;
     config, unavailable, Local.Host_operation (7, "balance")]

let signature_checks () =
  let source = {|
program Verify {
  public view fn check(key: bytes, message: bytes, signature: bytes): bool {
    return ed25519_ok(key, message, signature)
  }
}
|} in
  let hex text =
    if String.length text mod 2 <> 0 then fail "signature" "odd hex length";
    String.init (String.length text / 2) (fun index ->
      Char.chr (int_of_string ("0x" ^ String.sub text (2 * index) 2))) in
  let key = hex "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a" in
  let signature = hex
    ("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155"
     ^ "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b") in
  let changed text = String.mapi (fun i ch ->
    if i = 0 then Char.chr (Char.code ch lxor 1) else ch) text in
  let cases = [
    key, "", signature, true;
    key, "changed", signature, false;
    changed key, "", signature, false;
    key, "", changed signature, false;
    key, "", String.make 64 '\000', false;
    key, "", String.sub signature 0 32 ^ String.make 32 '\255', false;
    String.make 32 '\000', "", signature, false;
    String.make 32 '\255', "", signature, false;
    "\001" ^ String.make 31 '\000', "", signature, false;
    String.make 31 '\000', "", signature, false;
    key, "", String.sub signature 0 63, false;
  ] in
  List.iteri (fun index (key, message, signature, expected) ->
    List.iteri (fun encoding encode ->
      let args = List.map (fun value -> VM.VBytes value)
        [encode key; message; encode signature] in
      List.iter (fun output ->
        if output.Local.result <> VM.VBool expected then
          fail "signature" (Printf.sprintf "verification differs case = %d encoding = %d result = %s"
            index encoding (Local.value_text output.result));
        if output.storage <> [] || output.events <> [] || output.closes <> [] then
          fail "signature" "verification changed state";
        if output.effort < 2000 then fail "signature" "verification effort missing")
        [execute ~args "signature" "check" source;
         execute_octb ~args "signature" "check" source])
      [Fun.id; (fun value -> Base64.encode_exn value)]) cases;
  let compiled = compile "signature" source in
  let config = Local.config ~limit:1999 ~method_name:"check"
    ~args:[VM.VBytes key; VM.VBytes ""; VM.VBytes signature] () in
  match Local.run ~trace:false config compiled.code with
  | Ok output when output.stop = Local.Reverted && output.effort <= 1999 -> ()
  | Ok _ | Error _ -> fail "signature" "effort limit did not refuse"

let run () =
  read_checks ();
  fault_checks ();
  name_checks ();
  point_checks ();
  state_checks ();
  member_checks ();
  member_costs ();
  member_edits ();
  signature_checks ()