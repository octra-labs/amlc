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

let run () =
  read_checks ();
  fault_checks ();
  name_checks ()