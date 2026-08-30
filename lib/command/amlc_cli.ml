(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

open Aml_cli

type compile_req = {
  epoch : Z.t option;
  output : string option;
  feed : string option;
}

let compile_req = { epoch = None; output = None; feed = None }

let rec compile_args req = function
  | [] -> req
  | "--epoch" :: raw :: rest ->
    let epoch = epoch "compile" raw in
    compile_args { req with epoch = one "compile" "epoch" req.epoch epoch } rest
  | "--out" :: path :: rest ->
    compile_args
      { req with output = one "compile" "output path" req.output path }
      rest
  | "--feed" :: path :: rest ->
    compile_args { req with feed = one "compile" "feed path" req.feed path }
      rest
  | _ -> fail "compile" "option is invalid"

type run_req = {
  root : string option;
  at : Z.t option;
  feed : string option;
}

let run_req = { root = None; at = None; feed = None }

let rec run_args req = function
  | [] -> req
  | "--root" :: name :: rest ->
    run_args { req with root = one "run" "root name" req.root name } rest
  | "--epoch" :: raw :: rest ->
    let epoch = epoch "run" raw in
    run_args { req with at = one "run" "epoch" req.at epoch } rest
  | "--feed" :: path :: rest ->
    run_args { req with feed = one "run" "feed path" req.feed path } rest
  | _ -> fail "run" "option is invalid"

let stat command path =
  try Unix.stat path
  with Unix.Unix_error (error, _, _) -> fail command (Unix.error_message error)

let manifest command path =
  match (stat command path).st_kind with
  | Unix.S_DIR -> Filename.concat path "project.amlp"
  | Unix.S_REG -> path
  | _ -> fail command "project path is invalid"

let aml path = String.equal (Filename.extension path) ".aml"

type source_form =
  | Program_source
  | Contract_source

let source_offset raw line col =
  let rec walk index row =
    if index = String.length raw || row = line then index + max 0 (col - 1)
    else if raw.[index] = '\n' then walk (index + 1) (row + 1)
    else walk (index + 1) row
  in
  min (String.length raw) (walk 0 1)

let program_mark raw =
  match Octra_vm.C_lex.scan raw with
  | Error _ -> false
  | Ok items ->
    Array.exists
      (fun (item : Octra_vm.C_lex.item) ->
        match item.tok with
        | Octra_vm.C_lex.Size
        | Octra_vm.C_lex.Measure
        | Octra_vm.C_lex.Law
        | Octra_vm.C_lex.Input
        | Octra_vm.C_lex.Term
        | Octra_vm.C_lex.Form
        | Octra_vm.C_lex.Kind
        | Octra_vm.C_lex.Marks
        | Octra_vm.C_lex.Under
        | Octra_vm.C_lex.Permit
        | Octra_vm.C_lex.Shape -> true
        | _ -> false)
      items

let source_form path =
  let raw = source path in
  match Octra_vm.C_parse.parse raw, Contract_cli.probe_source raw with
  | Ok _, _ -> Program_source
  | Error _, Contract_cli.Accept -> Contract_source
  | Error current, Contract_cli.Refuse (line, col) ->
    if program_mark raw then Program_source
    else if source_offset raw line col > current.span.first.off then
      Contract_source
    else Program_source

let choose command wanted names =
  let present name = List.exists (String.equal name) names in
  match wanted, names with
  | Some name, _ when present name -> name
  | Some _, _ -> fail command "root name is absent"
  | None, [name] -> name
  | None, _ when present "main" -> "main"
  | None, [] -> fail command "project has no roots"
  | None, _ -> fail command "root is required for a multi-root project"

let origin command wanted folio =
  let origins = project_origins command folio in
  let name =
    choose command wanted
      (List.map (fun (value : Folio.origin) -> value.root.name) origins)
  in
  match
    List.find_opt
      (fun (value : Folio.origin) -> String.equal value.root.name name)
      origins
  with
  | Some value -> value
  | None -> fail command "root name is absent"

let run_part command input (folio : Folio.t) wanted =
  let origin = origin command wanted folio in
  let result = run_octb command origin.part.octb in
  let expected = project_result command origin in
  if not (Octra_vm.C_mach.equal result expected) then
    fail command "VM result differs from the checked root";
  Printf.printf
    "status = pass command = %s input = %s root = %s result = %s vm = AML storage = memory\n"
    command input origin.root.name (lit_text result)

let compile path args =
  let info = stat "compile" path in
  if info.st_kind = Unix.S_REG && aml path then
    match source_form path with
    | Contract_source -> Contract_cli.compile_as "compile" path args
    | Program_source ->
        let req = compile_args compile_req args in
        if Option.is_some req.epoch then
          fail "compile" "epoch does not apply to source";
        let output = Option.value
          ~default:(Filename.chop_extension path ^ ".octb") req.output in
        Aml_cli.build_as "compile" path output req.feed
  else
    begin
    let req = compile_args compile_req args in
    if Option.is_some req.feed then fail "compile" "feed does not apply to project";
    let manifest = manifest "compile" path in
    let epoch = Option.value ~default:Z.zero req.epoch in
    let output =
      Option.value
        ~default:(Filename.concat (Filename.dirname manifest) "build")
        req.output
    in
    project_build_as "compile" manifest (Z.to_string epoch) output
    end

type input_req = {
  epoch : Z.t option;
  feed : string option;
}

let input_req = { epoch = None; feed = None }

let rec input_args command req = function
  | [] -> req
  | "--epoch" :: raw :: rest ->
    let epoch = epoch command raw in
    input_args command { req with epoch = one command "epoch" req.epoch epoch }
      rest
  | "--feed" :: path :: rest ->
    input_args command { req with feed = one command "feed path" req.feed path }
      rest
  | _ -> fail command "option is invalid"

let check path args =
  let info = stat "check" path in
  if info.st_kind = Unix.S_DIR || String.equal (Filename.extension path) ".amlp"
  then
    let req = input_args "check" input_req args in
    let () =
      if Option.is_some req.feed then fail "check" "feed does not apply to project"
    in
    let epoch = Option.value ~default:Z.zero req.epoch in
    project_check_as "check" (manifest "check" path) (Z.to_string epoch)
  else if info.st_kind = Unix.S_REG && aml path then
    match source_form path with
    | Contract_source -> Contract_cli.check_as "check" path args
    | Program_source ->
        let req = input_args "check" input_req args in
        if Option.is_some req.epoch then
          fail "check" "epoch does not apply to source";
        Aml_cli.check path req.feed
  else if info.st_kind = Unix.S_REG
      && String.equal (Filename.extension path) ".cf1" then
    begin
      let req = input_args "check" input_req args in
      if Option.is_some req.epoch || Option.is_some req.feed then
        fail "check" "options do not apply to CF1";
      let raw, folio = folio "check" path in
      Printf.printf
        "status = pass command = check input = folio roots = %d bytes = %d sha256 = %s\n"
        (List.length folio.parts) (String.length raw) (sha raw)
    end
  else if info.st_kind = Unix.S_REG then
    begin
      let raw = source path in
      match Octra_vm.C_octb.decode raw with
      | Ok image ->
        let req = input_args "check" input_req args in
        if Option.is_some req.epoch || Option.is_some req.feed then
          fail "check" "options do not apply to OCTB";
        Printf.printf
          "status = pass command = check input = octb instructions = %d bytes = %d sha256 = %s\n"
          (Array.length image.code) (String.length raw) (sha raw)
      | Error _ -> Contract_cli.check_octb_as "check" path args
    end
  else fail "check" "input path is invalid"

let run path args =
  let info = stat "run" path in
  if info.st_kind = Unix.S_DIR || String.equal (Filename.extension path) ".amlp"
  then
    let req = run_args run_req args in
    let () =
      if Option.is_some req.feed then fail "run" "feed does not apply to project"
    in
    let _, folio =
      project_make "run" (manifest "run" path) (Option.value ~default:Z.zero req.at)
    in
    run_part "run" "project" folio req.root
  else if info.st_kind = Unix.S_REG && aml path then
    match source_form path with
    | Contract_source -> Contract_cli.run_as "run" path args
    | Program_source ->
        let req = run_args run_req args in
        if Option.is_some req.root || Option.is_some req.at then
          fail "run" "project options do not apply to source";
        Aml_cli.run path req.feed
  else if info.st_kind = Unix.S_REG
      && String.equal (Filename.extension path) ".cf1" then
    begin
      let req = run_args run_req args in
      if Option.is_some req.at || Option.is_some req.feed then
        fail "run" "options do not apply to CF1";
      let _, folio = folio "run" path in
      run_part "run" "folio" folio req.root
    end
  else if info.st_kind = Unix.S_REG then
    begin
      let raw = source path in
      match Octra_vm.C_octb.decode raw with
      | Ok _ ->
        let req = run_args run_req args in
        if Option.is_some req.root || Option.is_some req.at
            || Option.is_some req.feed then
          fail "run" "project options do not apply to OCTB";
        let result = run_octb "run" raw in
        Printf.printf
          "status = pass command = run input = octb result = %s vm = AML storage = memory\n"
          (lit_text result)
      | Error _ -> Contract_cli.run_octb_as "run" path args
    end
  else fail "run" "input path is invalid"

let test_folio command (folio : Folio.t) =
  List.iter
    (fun (origin : Folio.origin) ->
      let result = run_octb command origin.part.octb in
      let expected = project_result command origin in
      if not (Octra_vm.C_mach.equal result expected) then
        fail command "VM result differs from the checked root")
    (project_origins command folio)

let test path args =
  let info = stat "test" path in
  if info.st_kind = Unix.S_DIR || String.equal (Filename.extension path) ".amlp"
  then
    let req = input_args "test" input_req args in
    let () =
      if Option.is_some req.feed then fail "test" "feed does not apply to project"
    in
    let epoch = Option.value ~default:Z.zero req.epoch in
    project_test_as "test" (manifest "test" path) (Z.to_string epoch)
  else if info.st_kind = Unix.S_REG && aml path then
    match source_form path with
    | Contract_source -> Contract_cli.test_as "test" path args
    | Program_source ->
        let req = input_args "test" input_req args in
        if Option.is_some req.epoch then
          fail "test" "epoch does not apply to source";
        Aml_cli.test path req.feed
  else if info.st_kind = Unix.S_REG
      && String.equal (Filename.extension path) ".cf1" then
    begin
      let req = input_args "test" input_req args in
      if Option.is_some req.epoch || Option.is_some req.feed then
        fail "test" "options do not apply to CF1";
      let raw, checked = folio "test" path in
      test_folio "test" checked;
      Printf.printf
        "status = pass command = test input = folio roots = %d bytes = %d sha256 = %s\n"
        (List.length checked.parts) (String.length raw) (sha raw)
    end
  else if info.st_kind = Unix.S_REG then
    begin
      let raw = source path in
      match Octra_vm.C_octb.decode raw with
      | Ok _ ->
        let req = input_args "test" input_req args in
        if Option.is_some req.epoch || Option.is_some req.feed then
          fail "test" "options do not apply to OCTB";
        let left = run_octb "test" raw in
        let right = run_octb "test" raw in
        if not (Octra_vm.C_mach.equal left right) then
          fail "test" "repeated execution differs";
        Printf.printf
          "status = pass command = test input = octb repeats = 2 result = %s sha256 = %s\n"
          (lit_text left) (sha raw)
      | Error _ -> Contract_cli.test_octb_as "test" path args
    end
  else fail "test" "input path is invalid"

type debug_req = {
  name : string option;
  args : string list;
}

let rec debug_args req = function
  | [] -> { req with args = List.rev req.args }
  | "--root" :: name :: rest ->
    debug_args
      { req with name = one "debug" "root name" req.name name }
      rest
  | value :: rest -> debug_args { req with args = value :: req.args } rest

let debug path args =
  let info = stat "debug" path in
  if info.st_kind = Unix.S_DIR || String.equal (Filename.extension path) ".amlp"
  then
    let req = debug_args { name = None; args = [] } args in
    let manifest = manifest "debug" path in
    let input = project_input "debug" manifest in
    let name =
      choose "debug" req.name
        (List.map (fun (root : Proj.root) -> root.name)
          (Proj.roots input.image.project))
    in
    let root =
      match
        List.find_opt
          (fun (root : Proj.root) -> String.equal root.name name)
          (Proj.roots input.image.project)
      with
      | Some value -> value
      | None -> fail "debug" "root name is absent"
    in
    let source =
      match List.assoc_opt root.path input.files with
      | Some value -> value
      | None -> fail "debug" "root source is absent"
    in
    Aml_cli.debug_with source (root_input "debug" root) req.args
  else if info.st_kind = Unix.S_REG then
    if aml path then
      match source_form path with
      | Contract_source -> Contract_cli.debug_as "debug" path args
      | Program_source ->
          let req = debug_args { name = None; args = [] } args in
          if Option.is_some req.name then
            fail "debug" "root does not apply to source";
          Aml_cli.debug path req.args
    else
      let req = debug_args { name = None; args = [] } args in
      if Option.is_some req.name then fail "debug" "root does not apply to OCTB";
      let raw = source path in
      begin
        match Octra_vm.C_octb.decode raw with
        | Ok _ -> Aml_cli.debug_octb path req.args
        | Error _ -> Contract_cli.debug_octb_as "debug" path req.args
      end
  else fail "debug" "input path is invalid"

let dump path args =
  let format =
    match Aml_dump.select args with
    | Ok value -> value
    | Error reason -> fail "dump" reason
  in
  let raw = source path in
  match Octra_vm.C_octb.decode raw with
  | Ok _ -> Aml_cli.dump format path
  | Error _ -> Contract_cli.dump_as "dump" format path

let feed path args =
  if not (aml path) then fail "feed" "source path is invalid";
  if source_form path = Contract_source then
    fail "feed" "source has no fixture inputs";
  let values, output =
    match args with
    | [values] -> values, Filename.chop_extension path ^ ".af1"
    | [values; "--out"; output] -> values, output
    | _ -> fail "feed" "option is invalid"
  in
  Aml_cli.feed path values output

let usage () =
  Printf.eprintf
    "usage = amlc version | feed SOURCE VALUES [--out AF1] | check SOURCE [OPTIONS] | compile SOURCE [OPTIONS] | test SOURCE [OPTIONS] | run SOURCE [--method NAME] [--arg VALUE] [OPTIONS] | debug SOURCE [--method NAME] [--arg VALUE] [OPTIONS] | check PROJECT [--epoch N] | compile PROJECT [--epoch N] [--out PATH] | test PROJECT [--epoch N] | run PROJECT [--root NAME] [--epoch N] | debug PROJECT [--root NAME] [OPTIONS] | dump OCTB [--format text|events|dot]\n";
  exit 2

let main argv =
  try
    match Array.to_list argv with
    | [_; "version"] | [_; "--version"] -> version ()
    | _ :: ("feed" | "-feed") :: path :: args -> feed path args
    | _ :: ("compile" | "-compile") :: path :: args -> compile path args
    | _ :: ("check" | "-check") :: path :: args -> check path args
    | _ :: ("test" | "-test") :: path :: args -> test path args
    | _ :: ("run" | "-run") :: path :: args -> run path args
    | _ :: ("debug" | "-debug") :: path :: args -> debug path args
    | _ :: ("dump" | "-dump") :: path :: args -> dump path args
    | _ -> usage ()
  with
  | Stack_overflow -> fail "amlc" "stack capacity exceeded"
  | Out_of_memory -> fail "amlc" "memory capacity exceeded"
  | Invalid_argument reason -> fail "amlc" reason
  | Failure reason -> fail "amlc" reason