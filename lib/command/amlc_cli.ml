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
  method_name : string option;
  values : string list;
}

let run_req = {
  root = None;
  at = None;
  feed = None;
  method_name = None;
  values = [];
}

let rec runtime_args command req = function
  | [] -> { req with values = List.rev req.values }
  | "--root" :: name :: rest ->
    runtime_args command
      { req with root = one command "root name" req.root name } rest
  | "--epoch" :: raw :: rest ->
    let epoch = epoch command raw in
    runtime_args command { req with at = one command "epoch" req.at epoch } rest
  | "--feed" :: path :: rest ->
    runtime_args command
      { req with feed = one command "feed path" req.feed path } rest
  | "--method" :: name :: rest ->
    runtime_args command
      { req with
        method_name = one command "method name" req.method_name name }
      rest
  | "--arg" :: value :: rest ->
    runtime_args command { req with values = value :: req.values } rest
  | _ -> fail command "option is invalid"

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

let source_form_raw raw =
  match Octra_vm.C_parse.parse raw, Contract_cli.probe_source raw with
  | Ok _, Contract_cli.Refuse _ -> Program_source
  | Error _, Contract_cli.Accept -> Contract_source
  | Ok _, Contract_cli.Accept -> fail "source" "source grammar is ambiguous"
  | Error current, Contract_cli.Refuse (line, col) ->
    if source_offset raw line col > current.span.first.off then
      Contract_source
    else Program_source

let source_form path = source_form_raw (source path)

type octb_form =
  | Typed of Octra_vm.C_octb.image
  | Claimed of Octra_vm.C_octb.decode_error
  | Generic

let octb_form raw =
  match Octra_vm.C_octb.decode raw with
  | Ok image -> Typed image
  | Error error ->
    if Octra_vm.C_octb.claims_aml raw || Octra_vm.C_octb.claims_open raw then
      Claimed error
    else Generic

let typed_octb command raw =
  match octb_form raw with
  | Typed image -> Some image
  | Claimed error -> fail command (Octra_vm.C_octb.decode_text error)
  | Generic -> None

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

let run_part command input (folio : Folio.t) wanted method_name values =
  let origin = origin command wanted folio in
  let artifact = project_artifact command origin in
  match artifact.result with
  | Some expected ->
    if Option.is_some method_name || values <> [] then
      fail command "runtime arguments do not apply to a closed program";
    let result = run_octb command origin.part.octb in
    if not (Octra_vm.C_mach.equal result expected) then
      fail command "VM result differs from the checked root";
    Printf.printf
      "status = pass command = %s input = %s root = %s emission = %s result = %s vm = AML storage = memory veil = %s\n"
      command input origin.root.name (emission artifact) (lit_text result)
      (veil artifact)
  | None ->
    let method_name, result, outcome =
      Aml_cli.open_source command origin.src.body artifact method_name values
    in
    Printf.printf
      "status = pass command = %s input = %s root = %s emission = %s method = %s result = %s effort = %d steps = %d vm = AML storage = memory veil = %s\n"
      command input origin.root.name (emission artifact) method_name
      (lit_text result) outcome.effort outcome.steps (veil artifact)

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
      let lowered, specialized = emission_counts "check" folio in
      Printf.printf
        "status = pass command = check input = folio roots = %d lowered = %d specialized = %d bytes = %d sha256 = %s\n"
        (List.length folio.parts) lowered specialized (String.length raw)
        (sha raw)
    end
  else if info.st_kind = Unix.S_REG then
    begin
      let raw = source path in
      match typed_octb "check" raw with
      | Some image ->
        let req = input_args "check" input_req args in
        if Option.is_some req.epoch || Option.is_some req.feed then
          fail "check" "options do not apply to OCTB";
        let emission = Octra_vm.C_octb.image_emission image in
        let output =
          Option.fold ~none:"none" ~some:Octra_vm.C_type.text image.output
        in
        Printf.printf
          "status = pass command = check input = octb emission = %s inputs = %d output = %s instructions = %d bytes = %d sha256 = %s veil = %s veils = %s veil_depth = %s\n"
          emission (Array.length image.inputs) output
          (Array.length image.code) (String.length raw) (sha raw)
          (Octra_vm.C_octb.image_veil image)
          (Octra_vm.C_octb.image_veils image)
          (Octra_vm.C_octb.image_veil_depth image)
      | None -> Contract_cli.check_octb_as "check" path args
    end
  else fail "check" "input path is invalid"

let run path args =
  let info = stat "run" path in
  if info.st_kind = Unix.S_DIR || String.equal (Filename.extension path) ".amlp"
  then
    let req = runtime_args "run" run_req args in
    let () =
      if Option.is_some req.feed then fail "run" "feed does not apply to project"
    in
    let _, folio =
      project_make "run" (manifest "run" path) (Option.value ~default:Z.zero req.at)
    in
    run_part "run" "project" folio req.root req.method_name req.values
  else if info.st_kind = Unix.S_REG && aml path then
    match source_form path with
    | Contract_source -> Contract_cli.run_as "run" path args
    | Program_source ->
        let req = runtime_args "run" run_req args in
        if Option.is_some req.root || Option.is_some req.at then
          fail "run" "project options do not apply to source";
        Aml_cli.run path req.feed req.method_name req.values
  else if info.st_kind = Unix.S_REG
      && String.equal (Filename.extension path) ".cf1" then
    begin
      let req = runtime_args "run" run_req args in
      if Option.is_some req.at || Option.is_some req.feed then
        fail "run" "options do not apply to CF1";
      let _, folio = folio "run" path in
      run_part "run" "folio" folio req.root req.method_name req.values
    end
  else if info.st_kind = Unix.S_REG then
    begin
      let raw = source path in
      match typed_octb "run" raw with
      | Some image ->
        let req = runtime_args "run" run_req args in
        if Option.is_some req.root || Option.is_some req.at
            || Option.is_some req.feed then
          fail "run" "project options do not apply to OCTB";
        if Array.length image.inputs = 0 then begin
          if Option.is_some req.method_name || req.values <> [] then
            fail "run" "runtime arguments do not apply to a closed program";
          let result = run_octb "run" raw in
          Printf.printf
            "status = pass command = run input = octb emission = %s result = %s vm = AML storage = memory veil = %s\n"
            (Octra_vm.C_octb.image_emission image) (lit_text result)
            (Octra_vm.C_octb.image_veil image)
        end else
          run_open_octb "run" raw req.method_name req.values
      | None -> Contract_cli.run_octb_as "run" path args
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

let test_part command input (folio : Folio.t) wanted method_name values =
  let origin = origin command wanted folio in
  let artifact = project_artifact command origin in
  match artifact.result with
  | Some expected ->
    if Option.is_some method_name || values <> [] then
      fail command "runtime arguments do not apply to a closed program";
    let left = run_octb command origin.part.octb in
    let right = run_octb command origin.part.octb in
    if not (Octra_vm.C_mach.equal left right)
        || not (Octra_vm.C_mach.equal left expected) then
      fail command "repeated execution differs";
    Printf.printf
      "status = pass command = %s input = %s root = %s emission = %s repeats = 2 result = %s sha256 = %s veil = %s\n"
      command input origin.root.name (emission artifact) (lit_text left)
      (sha origin.part.octb) (veil artifact)
  | None ->
    let left_method, left_result, left =
      Aml_cli.open_source command origin.src.body artifact method_name values
    in
    let right_method, right_result, right =
      Aml_cli.open_source command origin.src.body artifact method_name values
    in
    if not (String.equal left_method right_method)
        || not (Octra_vm.C_mach.equal left_result right_result)
        || left.effort <> right.effort || left.steps <> right.steps
        || left.storage <> right.storage || left.events <> right.events then
      fail command "repeated execution differs";
    Printf.printf
      "status = pass command = %s input = %s root = %s emission = %s repeats = 2 method = %s result = %s effort = %d steps = %d sha256 = %s veil = %s\n"
      command input origin.root.name (emission artifact) left_method
      (lit_text left_result) left.effort left.steps (sha origin.part.octb)
      (veil artifact)

let test path args =
  let info = stat "test" path in
  if info.st_kind = Unix.S_DIR || String.equal (Filename.extension path) ".amlp"
  then
    let req = runtime_args "test" run_req args in
    if Option.is_some req.feed then fail "test" "feed does not apply to project";
    let epoch = Option.value ~default:Z.zero req.at in
    let manifest = manifest "test" path in
    if Option.is_some req.root || Option.is_some req.method_name
        || req.values <> [] then
      let checked, _ =
        project_repeated "test" manifest (Z.to_string epoch)
      in
      test_part "test" "project" checked req.root req.method_name req.values
    else
      project_test_as "test" manifest (Z.to_string epoch)
  else if info.st_kind = Unix.S_REG && aml path then
    match source_form path with
    | Contract_source -> Contract_cli.test_as "test" path args
    | Program_source ->
        let req = runtime_args "test" run_req args in
        if Option.is_some req.root || Option.is_some req.at then
          fail "test" "project options do not apply to source";
        Aml_cli.test path req.feed req.method_name req.values
  else if info.st_kind = Unix.S_REG
      && String.equal (Filename.extension path) ".cf1" then
    begin
      let req = runtime_args "test" run_req args in
      if Option.is_some req.at || Option.is_some req.feed then
        fail "test" "options do not apply to CF1";
      let raw, checked = folio "test" path in
      if Option.is_some req.root || Option.is_some req.method_name
          || req.values <> [] then
        test_part "test" "folio" checked req.root req.method_name req.values
      else begin
        test_folio "test" checked;
        let lowered, specialized = emission_counts "test" checked in
        Printf.printf
          "status = pass command = test input = folio roots = %d lowered = %d specialized = %d bytes = %d sha256 = %s\n"
          (List.length checked.parts) lowered specialized (String.length raw)
          (sha raw)
      end
    end
  else if info.st_kind = Unix.S_REG then
    begin
      let raw = source path in
      match typed_octb "test" raw with
      | Some image ->
        let req = runtime_args "test" run_req args in
        if Option.is_some req.root || Option.is_some req.at
            || Option.is_some req.feed then
          fail "test" "project options do not apply to OCTB";
        if Array.length image.inputs = 0 then begin
          if Option.is_some req.method_name || req.values <> [] then
            fail "test" "runtime arguments do not apply to a closed program";
          let left = run_octb "test" raw in
          let right = run_octb "test" raw in
          if not (Octra_vm.C_mach.equal left right) then
            fail "test" "repeated execution differs";
          Printf.printf
            "status = pass command = test input = octb emission = %s repeats = 2 result = %s sha256 = %s veil = %s\n"
            (Octra_vm.C_octb.image_emission image) (lit_text left) (sha raw)
            (Octra_vm.C_octb.image_veil image)
        end else
          Aml_cli.test_open_octb "test" raw req.method_name req.values
      | None -> Contract_cli.test_octb_as "test" path args
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
        match typed_octb "debug" raw with
        | Some _ -> Aml_cli.debug_octb path req.args
        | None -> Contract_cli.debug_octb_as "debug" path req.args
      end
  else fail "debug" "input path is invalid"

let dump path args =
  let format =
    match Aml_dump.select args with
    | Ok value -> value
    | Error reason -> fail "dump" reason
  in
  let raw = source path in
  match typed_octb "dump" raw with
  | Some _ -> Aml_cli.dump format path
  | None -> Contract_cli.dump_as "dump" format path

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
    "usage = amlc version | feed SOURCE VALUES [--out AF1] | check SOURCE [OPTIONS] | compile SOURCE [OPTIONS] | test SOURCE [--method NAME] [--arg VALUE] [OPTIONS] | run SOURCE [--method NAME] [--arg VALUE] [OPTIONS] | debug SOURCE [--method NAME] [--arg VALUE] [OPTIONS] | check PROJECT [--epoch N] | compile PROJECT [--epoch N] [--out PATH] | test PROJECT [--root NAME] [--method NAME] [--arg VALUE] [--epoch N] | run PROJECT [--root NAME] [--method NAME] [--arg VALUE] [--epoch N] | debug PROJECT [--root NAME] [OPTIONS] | dump OCTB [--format text|events|dot]\n";
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