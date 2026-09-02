(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

module Input = Octra_vm.Aml_input
module Source = Octra_vm.Aml_source
module VM = Octra_vm.Contract_vm
module Local = Octra_vm.Local_vm
module Octb = Octra_vm.C_octb

let fail name detail = failwith (name ^ " " ^ detail)

let includes text part =
  let text_len = String.length text in
  let part_len = String.length part in
  let rec seek index =
    index + part_len <= text_len
    && (String.equal (String.sub text index part_len) part
        || seek (index + 1))
  in
  part_len = 0 || seek 0

let compile name source =
  match Source.compile source with
  | Ok value -> value
  | Error reason -> fail name ("compile reason = " ^ reason)

let refuse name part source =
  match Source.compile source with
  | Error reason when includes reason part -> ()
  | Error reason -> fail name ("unexpected reason = " ^ reason)
  | Ok _ -> fail name "source accepted"

let attempt ?(args = []) ?(storage = []) ?(value = Z.zero) name method_name source =
  let compiled = compile name source in
  let config =
    Local.config
      ~method_name
      ~args
      ~storage
      ~value
      ~storage_kinds:(Input.storage_kinds compiled.ast)
      ()
  in
  match Local.run ~trace:false config compiled.code with
  | Error error -> fail name ("runner reason = " ^ Local.error_text error)
  | Ok outcome -> outcome

let attempt_octb ?(args = []) ?(storage = []) ?(value = Z.zero) name method_name source =
  let compiled = compile name source in
  let image =
    match Octra_vm.Bytecode.decode_image compiled.octb with
    | Ok image -> image
    | Error reason -> fail name ("decode reason = " ^ reason)
  in
  let storage_kinds = Option.value ~default:[] image.state in
  let config = Local.config ~method_name ~args ~storage ~value ~storage_kinds () in
  match Local.run ~trace:false config image.code with
  | Error error -> fail name ("runner reason = " ^ Local.error_text error)
  | Ok outcome -> outcome

let execute ?args ?storage ?value name method_name source =
  let outcome = attempt ?args ?storage ?value name method_name source in
  if outcome.stop = Local.Returned then outcome
  else fail name ("stop = " ^ Local.stop_text outcome.stop)

let execute_octb ?args ?storage ?value name method_name source =
  let outcome = attempt_octb ?args ?storage ?value name method_name source in
  if outcome.stop = Local.Returned then outcome
  else fail name ("stop = " ^ Local.stop_text outcome.stop)

let reverts name method_name source =
  let outcome = attempt name method_name source in
  if outcome.stop <> Local.Reverted then
    fail name ("stop = " ^ Local.stop_text outcome.stop)

let result name expected outcome =
  let actual = Local.value_text outcome.Local.result in
  if not (String.equal expected actual) then
    fail name ("result expected = " ^ expected ^ " actual = " ^ actual)

let storage_count name expected outcome =
  let actual = List.length outcome.Local.storage in
  if expected <> actual then
    fail name
      (Printf.sprintf "storage expected = %d actual = %d" expected actual)

let storage_value name key expected outcome =
  match List.assoc_opt key outcome.Local.storage with
  | Some actual when String.equal expected actual -> ()
  | Some actual ->
    fail name ("storage value expected = " ^ expected ^ " actual = " ^ actual)
  | None -> fail name ("storage key is absent key = " ^ key)

let same_runtime name left right =
  if left.Local.result <> right.Local.result
      || left.stop <> right.stop
      || left.effort <> right.effort
      || left.steps <> right.steps
      || left.storage <> right.storage
      || left.events <> right.events
  then fail name "detached execution differs"

let core_error name source =
  match Octra_vm.C_parse.parse source with
  | Error error -> Octra_vm.C_parse.text error
  | Ok parsed ->
    begin
      match Octra_vm.C_parse.check parsed with
      | Error error -> Octra_vm.C_parse.text error
      | Ok _ -> fail name "core source accepted"
    end

let core_refuse name part source =
  let reason = core_error name source in
  if not (includes reason part) then
    fail name ("unexpected reason = " ^ reason)

let core_result name expected source =
  match Octra_vm.C_octb.compile source with
  | Error error -> fail name ("compile reason = " ^ Octra_vm.C_octb.text error)
  | Ok artifact ->
    begin
      match artifact.result with
      | Some actual when Octra_vm.C_mach.equal expected actual -> ()
      | Some _ | None -> fail name "result differs"
    end

let core_input name expected input source =
  match Octra_vm.C_parse.parse source with
  | Error error -> fail name ("parse reason = " ^ Octra_vm.C_parse.text error)
  | Ok parsed ->
    begin
      match Octra_vm.C_parse.compile parsed with
      | Error error -> fail name ("check reason = " ^ Octra_vm.C_parse.text error)
      | Ok (program, _) ->
        begin
          match program.inputs with
          | [bind] ->
            begin
              match Octra_vm.C_eval.run_in [bind, input] program.term with
              | Error error ->
                  fail name ("run reason = " ^ Octra_vm.C_eval.text error)
              | Ok out when Octra_vm.C_eval.equal expected out.value -> ()
              | Ok _ -> fail name "result differs"
            end
          | binds ->
              fail name (Printf.sprintf "input count = %d" (List.length binds))
        end
    end

let core_veil name source plain =
  let compile source =
    match Octra_vm.C_octb.compile source with
    | Ok value -> value
    | Error error -> fail name ("compile reason = " ^ Octra_vm.C_octb.text error)
  in
  let veiled = compile source in
  let bare = compile plain in
  if veiled.veils <> 1 then fail name "veil count differs";
  if not (Z.equal (Octra_vm.C_nat.to_z veiled.veil_depth) (Z.of_int 2)) then
    fail name "veil depth differs";
  if bare.veils <> 0
      || not (Octra_vm.C_nat.equal bare.veil_depth Octra_vm.C_nat.zero)
  then fail name "plain veil metadata differs";
  if String.equal veiled.octb bare.octb then fail name "veil metadata is absent";
  let decode label (artifact : Octb.t) =
    match Octb.decode artifact.Octb.octb with
    | Ok value -> value
    | Error error ->
      fail name (label ^ " reason = " ^ Octb.decode_text error)
  in
  let marked = decode "veil decode" veiled in
  let plain = decode "plain decode" bare in
  if marked.code <> plain.code then fail name "veil instruction stream differs";
  if not (String.equal (Octb.image_veil marked) "static")
      || not (String.equal (Octb.image_veils marked) "1")
      || not (String.equal (Octb.image_veil_depth marked) "2") then
    fail name "veil artifact metadata differs";
  if not (String.equal (Octb.image_veil plain) "none")
      || not (String.equal (Octb.image_veils plain) "0")
      || not (String.equal (Octb.image_veil_depth plain) "0") then
    fail name "plain artifact metadata differs"

let core_equal name left right =
  let compile source =
    match Octra_vm.C_octb.compile source with
    | Ok value -> value.octb
    | Error error -> fail name ("compile reason = " ^ Octra_vm.C_octb.text error)
  in
  let check source =
    match Octra_vm.C_parse.parse source with
    | Error error -> fail name ("parse reason = " ^ Octra_vm.C_parse.text error)
    | Ok parsed ->
      begin
        match Octra_vm.C_parse.compile parsed with
        | Ok (_, info) -> info
        | Error error ->
          fail name ("check reason = " ^ Octra_vm.C_parse.text error)
      end
  in
  let left_info = check left in
  let right_info = check right in
  if not (Octra_vm.C_eff.equal left_info.eff right_info.eff) then
    fail name "effects differ";
  if not (Octra_vm.C_limit.equal left_info.res right_info.res) then
    fail name "resources differ";
  if not (String.equal (compile left) (compile right)) then
    fail name "OCTB differs"