(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

let prefix root path =
  let mark = root ^ Filename.dir_sep in
  String.equal path root
  || (String.length path > String.length mark
      && String.equal (String.sub path 0 (String.length mark)) mark)

let artifact_result path =
  let main = Unix.realpath path in
  let root = Filename.dirname main |> Unix.realpath in
  let name = Filename.basename main in
  let resolver request =
    if not (Filename.is_relative request) then None
    else
      try
        let path = Filename.concat root request |> Unix.realpath in
        if prefix root path then Some (Aml_cli.source path) else None
      with Unix.Unix_error _ | Sys_error _ -> None
  in
  Octra_vm.Aml_source.compile_multi resolver name

let artifact command path =
  match artifact_result path with
  | Ok value -> value
  | Error reason -> Aml_cli.fail command reason

type probe =
  | Accept
  | Refuse of int * int

let probe_source source =
  try
    ignore (Octra_vm.Oct_parse.syntax source);
    Accept
  with
  | Octra_vm.Oct_lex.LexError (_, line, col) -> Refuse (line, col)
  | Octra_vm.Oct_parse.ParseError (_, line) -> Refuse (line, 1)

let accepts_source source =
  match probe_source source with
  | Accept -> true
  | Refuse _ -> false

let image_result raw =
  match Octra_vm.Bytecode.decode_image raw with
  | Error reason -> Error reason
  | Ok image ->
    begin
      match Octra_vm.Contract_vm.Verifier.verify image.code with
      | Ok () -> Ok image
      | Error _ -> Error "OCTB verification refused"
    end

let image command raw =
  match image_result raw with
  | Ok value -> value
  | Error reason -> Aml_cli.fail command reason

let declaration value =
  Octra_vm.Oct_lang.declaration_to_string value

let check_as command path args =
  if args <> [] then Aml_cli.fail command "option is invalid";
  let value = artifact command path in
  Printf.printf
    "status = pass command = %s program = %s declaration = %s instructions = %d bytes = %d sha256 = %s\n"
    command
    value.name
    (declaration value.declaration)
    (Array.length value.code)
    (String.length value.octb)
    (Aml_cli.sha value.octb)

let rec compile_args command output = function
  | [] -> output
  | "--out" :: path :: rest ->
    compile_args command
      (Aml_cli.one command "output path" output path)
      rest
  | _ -> Aml_cli.fail command "option is invalid"

let output_path source output =
  match output with
  | Some path -> path
  | None -> Filename.remove_extension source ^ ".octb"

let compile_as command path args =
  let output = output_path path (compile_args command None args) in
  if String.equal path output || String.equal path (output ^ ".next") then
    Aml_cli.fail command "source and output paths overlap";
  let value = artifact command path in
  begin
    try Aml_cli.write output value.octb
    with Sys_error reason -> Aml_cli.fail command reason
  end;
  Printf.printf
    "status = pass command = %s program = %s instructions = %d bytes = %d sha256 = %s output = %s\n"
    command
    value.name
    (Array.length value.code)
    (String.length value.octb)
    (Aml_cli.sha value.octb)
    output

let test_as command path args =
  if args <> [] then Aml_cli.fail command "option is invalid";
  let compile () = artifact command path in
  let left = compile () in
  let right = compile () in
  if not (String.equal left.octb right.octb) then
    Aml_cli.fail command "repeated compilation differs";
  begin
    match Octra_vm.Bytecode.decode left.octb with
    | Error reason -> Aml_cli.fail command reason
    | Ok code ->
      begin
        match Octra_vm.Contract_vm.Verifier.verify code with
        | Ok () -> ()
        | Error _ -> Aml_cli.fail command "verification differs"
      end
  end;
  Printf.printf
    "status = pass command = %s program = %s repeats = 2 instructions = %d bytes = %d sha256 = %s\n"
    command
    left.name
    (Array.length left.code)
    (String.length left.octb)
    (Aml_cli.sha left.octb)

type exec_options = {
  method_name : string option;
  values : string list;
  storage : (string * string) list;
  limit : int;
  step_cap : int;
  epoch : int;
  view : bool;
}

let exec_defaults = {
  method_name = None;
  values = [];
  storage = [];
  limit = 1_000_000;
  step_cap = 100_000;
  epoch = 0;
  view = false;
}

let positive command name value =
  match int_of_string_opt value with
  | Some parsed when parsed > 0 && String.equal value (string_of_int parsed) ->
    parsed
  | Some _ | None -> Aml_cli.fail command (name ^ " is invalid")

let natural command name value =
  match int_of_string_opt value with
  | Some parsed when parsed >= 0 && String.equal value (string_of_int parsed) ->
    parsed
  | Some _ | None -> Aml_cli.fail command (name ^ " is invalid")

let storage_row command value =
  match String.index_opt value '=' with
  | Some index when index > 0 ->
    String.sub value 0 index,
    String.sub value (index + 1) (String.length value - index - 1)
  | Some _ | None -> Aml_cli.fail command "storage row is invalid"

let rec exec_args command options = function
  | [] -> {
      options with
      values = List.rev options.values;
      storage = List.rev options.storage;
    }
  | "--method" :: name :: rest ->
    begin
      match options.method_name with
      | Some _ -> Aml_cli.fail command "method is repeated"
      | None -> exec_args command { options with method_name = Some name } rest
    end
  | "--arg" :: value :: rest ->
    exec_args command { options with values = value :: options.values } rest
  | "--set" :: value :: rest ->
    exec_args command
      { options with storage = storage_row command value :: options.storage }
      rest
  | "--limit" :: value :: rest ->
    exec_args command
      { options with limit = positive command "effort limit" value }
      rest
  | "--step-cap" :: value :: rest ->
    exec_args command
      { options with step_cap = positive command "step cap" value }
      rest
  | "--epoch" :: value :: rest ->
    exec_args command
      { options with epoch = natural command "epoch" value }
      rest
  | "--view" :: rest -> exec_args command { options with view = true } rest
  | _ -> Aml_cli.fail command "option is invalid"

let public_methods artifact =
  artifact.Octra_vm.Aml_source.ast.Octra_vm.Oct_lang.funcs
  |> List.filter (fun fn ->
    match fn.Octra_vm.Oct_lang.fn_vis with
    | Octra_vm.Oct_lang.Public -> true
    | Octra_vm.Oct_lang.Private | Octra_vm.Oct_lang.Internal -> false)

let selected_method command artifact = function
  | Some name -> name
  | None ->
    begin
      match public_methods artifact with
      | [fn] -> fn.Octra_vm.Oct_lang.fn_name
      | [] -> Aml_cli.fail command "public method is absent"
      | _ -> Aml_cli.fail command "method is required"
    end

let local_args command artifact method_name values =
  match
    Octra_vm.Aml_input.parse artifact.Octra_vm.Aml_source.ast
      method_name values
  with
  | Ok parsed -> parsed
  | Error error ->
    Aml_cli.fail command (Octra_vm.Aml_input.error_text error)

let nibble = function
  | '0' .. '9' as value -> Some (Char.code value - Char.code '0')
  | 'a' .. 'f' as value -> Some (Char.code value - Char.code 'a' + 10)
  | 'A' .. 'F' as value -> Some (Char.code value - Char.code 'A' + 10)
  | _ -> None

let raw_bytes value =
  let size = String.length value in
  if size mod 2 <> 0 then None
  else
    let out = Bytes.create (size / 2) in
    let rec loop index =
      if index = Bytes.length out then Some (Bytes.to_string out)
      else
        match nibble value.[index * 2], nibble value.[index * 2 + 1] with
        | Some high, Some low ->
          Bytes.set out index (Char.chr ((high lsl 4) lor low));
          loop (index + 1)
        | None, _ | _, None -> None
    in
    loop 0

let raw_natural maximum make value =
  match Octra_vm.Aml_input.integer value with
  | Some value when Z.sign value >= 0 && Z.leq value maximum -> Some (make value)
  | Some _ | None -> None

let raw_value command index value =
  let bad () =
    Aml_cli.fail command
      (Printf.sprintf "OCTB argument is invalid index = %d" index)
  in
  match String.index_opt value ':' with
  | None -> bad ()
  | Some at ->
    let tag = String.sub value 0 at in
    let body = String.sub value (at + 1) (String.length value - at - 1) in
    begin
      match tag with
      | "int" ->
        begin
          match Octra_vm.Aml_input.integer body with
          | Some value -> Octra_vm.Contract_vm.VInt value
          | None -> bad ()
        end
      | "bool" when String.equal body "true" -> Octra_vm.Contract_vm.VBool true
      | "bool" when String.equal body "false" -> Octra_vm.Contract_vm.VBool false
      | "text" -> Octra_vm.Contract_vm.VString body
      | "bytes" ->
        begin
          match raw_bytes body with
          | Some value -> Octra_vm.Contract_vm.VBytes value
          | None -> bad ()
        end
      | "bytes32" ->
        begin
          match raw_bytes body with
          | Some value when String.length value = 32 ->
            Octra_vm.Contract_vm.VBytes32 value
          | Some _ | None -> bad ()
        end
      | "u64" ->
        begin
          match raw_natural Octra_vm.Contract_vm.max_u64
              (fun value -> Octra_vm.Contract_vm.VU64 value) body with
          | Some value -> value
          | None -> bad ()
        end
      | "u128" ->
        begin
          match raw_natural Octra_vm.Contract_vm.max_u128
              (fun value -> Octra_vm.Contract_vm.VU128 value) body with
          | Some value -> value
          | None -> bad ()
        end
      | "u256" ->
        begin
          match raw_natural Octra_vm.Contract_vm.max_u256
              (fun value -> Octra_vm.Contract_vm.VU256 value) body with
          | Some value -> value
          | None -> bad ()
        end
      | "addr" -> Octra_vm.Contract_vm.VAddr body
      | _ -> bad ()
    end

let frame_text frame =
  Printf.printf
    "event = frame index = %d pc = %d next_pc = %d effort_before = %d effort_after = %d op = %s r0 = %s\n"
    frame.Octra_vm.Local_vm.index
    frame.pc
    frame.next_pc
    frame.effort_before
    frame.effort_after
    (String.trim (Octra_vm.Assembler.emit [|frame.op|]))
    (Octra_vm.Local_vm.value_text frame.result)

let storage_diff before after =
  let left = Hashtbl.of_seq (List.to_seq before) in
  let right = Hashtbl.of_seq (List.to_seq after) in
  let changed =
    List.filter_map
      (fun (key, value) ->
        match Hashtbl.find_opt left key with
        | Some prior when String.equal prior value -> None
        | Some _ | None -> Some ("set", key, value))
      after
  in
  let removed =
    List.filter_map
      (fun (key, _) ->
        if Hashtbl.mem right key then None else Some ("delete", key, ""))
      before
  in
  List.sort
    (fun (_, left, _) (_, right, _) -> String.compare left right)
    (changed @ removed)

let storage_text (action, key, value) =
  Printf.printf "event = storage action = %s key = %S value = %S\n"
    action key value

let execute command trace program options method_name args storage_kinds code =
  let config =
    Octra_vm.Local_vm.config
      ~storage:options.storage
      ~storage_kinds
      ~limit:options.limit
      ~step_cap:options.step_cap
      ~epoch:options.epoch
      ~view:options.view
      ~method_name
      ~args
      ()
  in
  let outcome =
    match Octra_vm.Local_vm.run ~trace config code with
    | Ok outcome -> outcome
    | Error error ->
      Aml_cli.fail command (Octra_vm.Local_vm.error_text error)
  in
  let writes = storage_diff options.storage outcome.storage in
  if trace then begin
    List.iter frame_text outcome.frames;
    List.iter storage_text writes;
    flush stdout
  end;
  match outcome.stop with
  | Octra_vm.Local_vm.Returned ->
    Printf.printf
      "status = pass command = %s program = %s method = %s result = %s effort = %d steps = %d storage = %d writes = %d events = %d\n"
      command
      program
      method_name
      (Octra_vm.Local_vm.value_text outcome.result)
      outcome.effort
      outcome.steps
      (List.length outcome.storage)
      (List.length writes)
      (List.length outcome.events)
  | Octra_vm.Local_vm.Reverted
  | Octra_vm.Local_vm.Step_cap
  | Octra_vm.Local_vm.Host_operation _ ->
    Aml_cli.fail command
      (Printf.sprintf "execution stopped stop = %s effort = %d steps = %d"
        (Octra_vm.Local_vm.stop_text outcome.stop)
        outcome.effort
        outcome.steps)

let local command trace path args =
  let artifact = artifact command path in
  let options = exec_args command exec_defaults args in
  let method_name = selected_method command artifact options.method_name in
  let args = local_args command artifact method_name options.values in
  execute command trace artifact.name options method_name args
    (Octra_vm.Aml_input.storage_kinds artifact.ast) artifact.code

let local_octb_as command trace path args =
  let options = exec_args command exec_defaults args in
  let method_name =
    match options.method_name with
    | Some value -> value
    | None -> Aml_cli.fail command "method is required for contract OCTB"
  in
  let values = List.mapi (raw_value command) options.values in
  let code = (image command (Aml_cli.source path)).code in
  execute command trace (Filename.basename path) options method_name values [] code

let run_octb_as command path args = local_octb_as command false path args
let debug_octb_as command path args = local_octb_as command true path args

let check_octb_as command path args =
  if args <> [] then Aml_cli.fail command "option is invalid";
  let raw = Aml_cli.source path in
  let image = image command raw in
  Printf.printf
    "status = pass command = %s input = octb instructions = %d bytes = %d sha256 = %s\n"
    command (Array.length image.code) (String.length raw) (Aml_cli.sha raw)

let test_octb_as command path args =
  if args <> [] then Aml_cli.fail command "option is invalid";
  let raw = Aml_cli.source path in
  let left = image command raw in
  let right = image command raw in
  if left.code <> right.code then
    Aml_cli.fail command "repeated OCTB verification differs";
  Printf.printf
    "status = pass command = %s input = octb repeats = 2 instructions = %d sha256 = %s\n"
    command (Array.length left.code) (Aml_cli.sha raw)

let run_as command path args = local command false path args
let debug_as command path args = local command true path args

let op_text op =
  String.trim (Octra_vm.Assembler.emit [|op|])

let dump_line value = Printf.printf "%s\n" value

let dump_emit format = Printf.ksprintf dump_line format

let const_text = function
  | Octra_vm.Bytecode.CInt value ->
    if String.length value <= 48 then "int:" ^ value
    else
      Printf.sprintf "int:%s... digits = %d sha256 = %s"
        (String.sub value 0 32) (String.length value) (Aml_cli.sha value)
  | Octra_vm.Bytecode.CBool value -> "bool:" ^ string_of_bool value
  | Octra_vm.Bytecode.CStr value ->
    if String.length value <= 48 then "text:\"" ^ String.escaped value ^ "\""
    else
      Printf.sprintf "text:chars=%d sha256=%s"
        (String.length value) (Aml_cli.sha value)
  | Octra_vm.Bytecode.CBytes value ->
    Printf.sprintf "bytes:size=%d sha256=%s"
      (String.length value) (Aml_cli.sha value)
  | Octra_vm.Bytecode.CAddr value -> "addr:" ^ value

let next code pc kind =
  if pc + 1 < Array.length code then [pc, pc + 1, kind] else []

let op_edges code pc =
  match code.(pc) with
  | Octra_vm.Contract_vm.JMP target -> [pc, target, "jump"]
  | Octra_vm.Contract_vm.JIF (_, target) ->
    (pc, target, "true") :: next code pc "false"
  | Octra_vm.Contract_vm.CALL_INT (_, target) ->
    (pc, target, "call") :: next code pc "resume"
  | Octra_vm.Contract_vm.STOP | Octra_vm.Contract_vm.REVERT -> []
  | _ -> next code pc "next"

let dump_edges code =
  Array.to_list (Array.mapi (fun pc _ -> op_edges code pc) code)
  |> List.concat
  |> List.filter (fun (_, target, _) ->
    target >= 0 && target < Array.length code)

let dump_text raw (image : Octra_vm.Bytecode.image) code edges =
  let digest = Aml_cli.sha raw in
  dump_emit
    "image = octb version = 1 vm = AML bytes = %d instructions = %d sha256 = %s"
    (String.length raw) (Array.length code) digest;
  dump_emit "section = .head file = 0x%08x size = 12 entries = 1" 0;
  dump_emit "section = .const file = 0x%08x size = %d entries = %d" 12
    (image.Octra_vm.Bytecode.text_at - 12) (Array.length image.consts);
  dump_emit "section = .text file = 0x%08x size = %d entries = %d"
    image.text_at (String.length raw - image.text_at) (Array.length code);
  Array.iter
    (fun (row : Octra_vm.Bytecode.const_cell) ->
      dump_emit
        "constant = c%04d file = 0x%08x size = %d type = %d value = %s"
        row.id row.at row.size row.tag (const_text row.value))
    image.consts;
  Array.iteri
    (fun pc op ->
      let cell = image.Octra_vm.Bytecode.cells.(pc) in
      dump_emit
        "instruction = p%04d address = 0x%08x file = 0x%08x size = %d op = %s"
        pc pc cell.at cell.size (String.escaped (op_text op)))
    code;
  List.iter
    (fun (source, target, kind) ->
      dump_emit "xref = code source = p%04d target = p%04d type = %s"
        source target kind)
    edges;
  dump_emit
    "status = pass command = dump instructions = %d edges = %d bytes = %d sha256 = %s"
    (Array.length code) (List.length edges) (String.length raw) digest

let dump_events raw (image : Octra_vm.Bytecode.image) code edges =
  let digest = Aml_cli.sha raw in
  dump_emit
    "event = image format = OCTB version = 1 vm = AML bytes = %d instructions = %d sha256 = %s"
    (String.length raw) (Array.length code) digest;
  Array.iter
    (fun (row : Octra_vm.Bytecode.const_cell) ->
      dump_emit
        "event = constant name = c%04d file = %d size = %d type = %d value = %s"
        row.id row.at row.size row.tag (const_text row.value))
    image.consts;
  Array.iteri
    (fun pc op ->
      let cell = image.Octra_vm.Bytecode.cells.(pc) in
      dump_emit "event = instruction pc = %d file = %d size = %d op = %s"
        pc cell.at cell.size (String.escaped (op_text op)))
    code;
  List.iter
    (fun (source, target, kind) ->
      dump_emit "event = edge source = p%04d target = p%04d type = %s"
        source target kind)
    edges;
  dump_emit
    "status = pass command = dump instructions = %d edges = %d bytes = %d sha256 = %s"
    (Array.length code) (List.length edges) (String.length raw) digest

let dot_escape value =
  let out = Buffer.create (String.length value) in
  String.iter
    (function
      | '\\' -> Buffer.add_string out "\\\\"
      | '"' -> Buffer.add_string out "\\\""
      | '\n' -> Buffer.add_string out "\\n"
      | char -> Buffer.add_char out char)
    value;
  Buffer.contents out

let dump_dot raw code edges =
  dump_line "digraph octb {";
  dump_emit "  graph [label = \"OCTB/1 %s\", labelloc = t];" (Aml_cli.sha raw);
  dump_line "  node [shape = box, fontname = monospace];";
  dump_line "  edge [fontname = monospace];";
  Array.iteri
    (fun pc op ->
      dump_emit "  \"p%04d\" [label = \"pc = %04d op = %s\"];"
        pc pc (dot_escape (op_text op)))
    code;
  List.iter
    (fun (source, target, kind) ->
      dump_emit "  \"p%04d\" -> \"p%04d\" [label = \"%s\"];"
        source target kind)
    edges;
  dump_line "}"

let dump_as command format path =
  let raw = Aml_cli.source path in
  let image = image command raw in
  let code = Octra_vm.Vm_program.fix image.code in
  let edges = dump_edges code in
  match format with
  | Aml_dump.Text -> dump_text raw image code edges
  | Aml_dump.Events -> dump_events raw image code edges
  | Aml_dump.Dot -> dump_dot raw code edges