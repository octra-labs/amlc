(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

module Parse = Octra_vm.C_parse
module Emit = Octra_vm.C_emit
module Feed = Octra_vm.C_feed
module Octb = Octra_vm.C_octb
module Live = Octra_vm.C_live
module Path = Octra_vm.C_path
module Dbg = Octra_vm.C_dbg
module Proj = Octra_vm.C_proj
module Pfile = Octra_vm.C_pfile
module Folio = Octra_vm.C_folio
module Rval = Octra_vm.C_rval
module VM = Octra_vm.C_vm
module Eval = Octra_vm.C_eval
module Input = Octra_vm.Aml_input
module Local = Octra_vm.Local_vm

let read path = In_channel.with_open_bin path In_channel.input_all

let discard path =
  try Unix.unlink path with Unix.Unix_error _ -> ()

let discard_dir path =
  try
    Sys.readdir path
    |> Array.iter (fun name ->
      let child = Filename.concat path name in
      match (Unix.lstat child).st_kind with
      | Unix.S_REG | Unix.S_LNK -> discard child
      | _ -> ());
    Unix.rmdir path
  with Unix.Unix_error _ | Sys_error _ -> ()

let write path data =
  if String.equal path "" then raise (Sys_error "output path is empty");
  let next = path ^ ".next" in
  try
    Out_channel.with_open_bin next (fun channel -> output_string channel data);
    Unix.rename next path
  with
  | Sys_error reason ->
    discard next;
    raise (Sys_error reason)
  | Unix.Unix_error (error, _, _) ->
    discard next;
    raise (Sys_error (path ^ ": " ^ Unix.error_message error))

let hex value =
  String.concat "" (List.init (String.length value) (fun index ->
    Printf.sprintf "%02x" (Char.code value.[index])))

let lit_text = function
  | Emit.Bool value -> "bool:" ^ string_of_bool value
  | Emit.Int value ->
    let text = Octra_vm.C_eval.int_text value in
    if Z.numbits value <= 256 then "int:" ^ text else text
  | Emit.Bytes value -> "bytes:" ^ hex value
  | Emit.Data value ->
    "data[" ^ Octra_vm.C_type.text (Rval.typ value) ^ "]:"
    ^ Octra_vm.C_eval.value_text (Rval.value value)

let lit_shape = function
  | Emit.Bool _ -> "bool"
  | Emit.Int _ -> "int"
  | Emit.Bytes value -> "bytes[" ^ string_of_int (String.length value) ^ "]"
  | Emit.Data value -> Octra_vm.C_type.text (Rval.typ value)

let slot_text (value : Live.slot) =
  Octra_vm.C_nat.text value.id ^ ":" ^ Octra_vm.C_type.mul_text value.mul ^ ":"
  ^ if value.live then "live" else "spent"

let slots_text values =
  "[" ^ String.concat "," (List.map slot_text values) ^ "]"

let sha value = Digestif.SHA256.(to_hex (digest_string value))

let fail command reason =
  Printf.eprintf "status = fail command = %s reason = %s\n" command reason;
  exit 1

let version () =
  Printf.printf
    "language = AML compiler = amlc release = preview octb = 1\n"

let source path =
  try read path with Sys_error reason -> fail "read" reason

let compile command source feed =
  let result =
    match feed with
    | None -> Octb.compile source
    | Some feed -> Octb.compile_feed source feed
  in
  match result with
  | Ok value -> value
  | Error error -> fail command (Octb.text error)

let emission (artifact : Octb.t) =
  Octra_vm.C_mach.emission_text artifact.Octb.emission

let veil (artifact : Octb.t) = Octb.veil_text artifact.veils

let checked_result command artifact =
  match artifact.Octb.result with
  | Some value -> value
  | None -> fail command "runtime arguments are required"

let feed_specs command source =
  let parsed =
    match Parse.parse source with
    | Ok value -> value
    | Error error -> fail command (Parse.text error)
  in
  let binds =
    match Parse.binds parsed with
    | Ok value -> value
    | Error error -> fail command (Octra_vm.C_decl.text error)
  in
  match Feed.specs binds with
  | Ok value -> value
  | Error error -> fail command (Feed.text error)

let feed_file command path =
  match Feed.decode (source path) with
  | Ok value -> value
  | Error error -> fail command (Feed.text error)

let feed_opt command = function
  | None -> None
  | Some path -> Some (feed_file command path)

let decode command raw =
  match Octb.decode raw with
  | Ok value -> value
  | Error error -> fail command (Octb.decode_text error)

let native_image command raw =
  match Octra_vm.Bytecode.decode_image raw with
  | Error reason -> fail command reason
  | Ok image ->
    begin
      match Octra_vm.Contract_vm.Verifier.verify image.code with
      | Ok () -> image
      | Error _ -> fail command "OCTB verification refused"
    end

let state () = VM.make ~activate:(Some Z.zero) ()

let same_native expected actual =
  match expected, actual with
  | Emit.Bool left, Octra_vm.Contract_vm.VBool right -> Bool.equal left right
  | Emit.Int left, Octra_vm.Contract_vm.VInt right -> Z.equal left right
  | Emit.Bytes left, Octra_vm.Contract_vm.VBytes right ->
    String.equal left right
  | Emit.Data left, Octra_vm.Contract_vm.VString right ->
    String.equal (Rval.encode left) right
  | _ -> false

let run_octb command raw =
  let image = decode command raw in
  if Array.length image.inputs <> 0 then
    fail command "runtime arguments are required";
  let native = native_image command raw in
  let config =
    Local.config
      ~view:true
      ~byte_result:Octra_vm.Contract_vm.Bytes_result
      ~limit:1_000_000
      ~step_cap:1_000_000
      ~method_name:"main"
      ~args:[]
      ()
  in
  let outcome =
    match Local.run_at ~trace:false config ~entry:0 native.code with
    | Ok value -> value
    | Error error -> fail command (Local.error_text error)
  in
  begin
    match outcome.stop with
    | Local.Returned -> ()
    | Local.Reverted | Local.Step_cap | Local.Host_operation _ ->
      fail command
        (Printf.sprintf "execution stopped stop = %s effort = %d steps = %d"
          (Local.stop_text outcome.stop) outcome.effort outcome.steps)
  end;
  let machine = state () in
  begin
    match VM.run machine image.code with
    | Ok () -> ()
    | Error error -> fail command (VM.text error)
  end;
  let result = VM.result machine in
  if not (same_native result outcome.result)
      || not (Z.equal (VM.work machine) (Z.of_int outcome.effort))
      || VM.steps machine <> outcome.steps
      || outcome.storage <> [] || outcome.events <> [] then
    fail command "production VM differs from the checked machine";
  result

let core_values command inputs values =
  match Input.core inputs values with
  | Ok parsed -> parsed
  | Error error -> fail command (Input.error_text error)

let octb_values command inputs values =
  match Input.core_octb inputs values with
  | Ok parsed -> parsed
  | Error error -> fail command (Input.error_text error)

let local_run ?(trace = false) command raw method_name values =
  let image = native_image command raw in
  let config =
    Local.config
      ~view:true
      ~byte_result:Octra_vm.Contract_vm.Bytes_result
      ~method_name
      ~args:(List.map (fun (value : Input.core_value) -> value.vm) values)
      ()
  in
  match Local.run ~trace config image.code with
  | Error error -> fail command (Local.error_text error)
  | Ok outcome ->
    begin
      match outcome.stop with
      | Local.Returned -> outcome
      | Local.Reverted | Local.Step_cap | Local.Host_operation _ ->
        fail command
          (Printf.sprintf "execution stopped stop = %s effort = %d steps = %d"
            (Local.stop_text outcome.stop) outcome.effort outcome.steps)
    end

let open_frame outcome =
  List.find_opt
    (fun (frame : Local.frame) ->
      match frame.op with
      | Octra_vm.Contract_vm.NOP -> true
      | _ -> false)
    outcome.Local.frames

let open_match code values outcome =
  match open_frame outcome with
  | None -> Error "open VM separator is absent"
  | Some frame ->
    let inputs = List.map (fun (value : Input.core_value) -> value.lit) values in
    begin
      match VM.make_in ~activate:(Some Z.zero) inputs with
      | Error error -> Error (VM.text error)
      | Ok machine ->
        begin
          match VM.run machine code with
          | Error error -> Error (VM.text error)
          | Ok () ->
            let steps = outcome.steps - frame.index - 1 in
            let work = outcome.effort - frame.effort_after in
            if steps >= 0 && work >= 0
                && same_native (VM.result machine) outcome.result
                && VM.steps machine = steps
                && Z.equal (VM.work machine) (Z.of_int work)
                && outcome.storage = [] && outcome.events = [] then Ok ()
            else Error "production VM differs from the open checked machine"
        end
    end

let open_machine command code values outcome =
  match open_match code values outcome with
  | Ok () -> ()
  | Error reason -> fail command reason

let core_result command typ = function
  | Octra_vm.Contract_vm.VInt value when Octra_vm.C_type.equal typ Octra_vm.C_type.Int ->
    Emit.Int value, Eval.Int value
  | Octra_vm.Contract_vm.VBool value
      when Octra_vm.C_type.equal typ Octra_vm.C_type.Bool ->
    Emit.Bool value, Eval.Bool value
  | Octra_vm.Contract_vm.VBytes value ->
    begin
      match typ with
      | Octra_vm.C_type.Bytes len
          when Octra_vm.C_nat.to_int len = String.length value ->
        Emit.Bytes value, Eval.Bytes value
      | _ -> fail command "VM result type differs from program type"
    end
  | _ -> fail command "VM result type differs from program type"

let main_method command = function
  | None -> "main"
  | Some name when String.equal name "main" -> name
  | Some _ -> fail command "method is absent"

let check path feed_path =
  let raw = source path in
  let parsed =
    match Parse.parse raw with
    | Ok value -> value
    | Error error -> fail "check" (Parse.text error)
  in
  let lowered, info =
    match Parse.compile parsed with
    | Ok value -> value
    | Error error -> fail "check" (Parse.text error)
  in
  begin
    match feed_opt "check" feed_path with
    | None -> ()
    | Some feed ->
      begin
        match Feed.attach lowered.Octra_vm.C_low.inputs feed with
        | Ok _ -> ()
        | Error error -> fail "check" (Feed.text error)
      end
  end;
  Printf.printf
    "status = pass command = check program = %s type = %s effects = %s veil = %s veils = %d veil_depth = %s\n"
    (Octra_vm.C_syn.name_text (Parse.name parsed))
    (Octra_vm.C_type.text info.Octra_vm.C_check.typ)
    (Octra_vm.C_eff.text info.eff)
    (Octb.veil_text (Parse.veil_count parsed))
    (Parse.veil_count parsed)
    (Octra_vm.C_nat.text (Parse.veil_depth parsed))

let build_as command input output feed_path =
  if String.equal input output || String.equal input (output ^ ".next") then
    fail command "source and output paths overlap";
  let artifact = compile command (source input) (feed_opt command feed_path) in
  begin
    try write output artifact.octb
    with Sys_error reason -> fail command reason
  end;
  Printf.printf
    "status = pass command = %s emission = %s bytes = %d sha256 = %s veil = %s veils = %d veil_depth = %s output = %s\n"
    command (emission artifact) (String.length artifact.octb)
    (sha artifact.octb) (veil artifact) artifact.veils
    (Octra_vm.C_nat.text artifact.veil_depth) output

let build input output feed_path = build_as "build" input output feed_path

let open_source command raw (artifact : Octb.t) method_name values =
  let method_name = main_method command method_name in
  let values = core_values command artifact.Octb.inputs values in
  let outcome = local_run ~trace:true command artifact.octb method_name values in
  let image = decode command artifact.octb in
  open_machine command image.code values outcome;
  let result, eval_result = core_result command artifact.typ outcome.result in
  let machine_inputs =
    List.map2
      (fun bind (value : Input.core_value) -> bind, value.lit)
      artifact.inputs values
  in
  begin
    match Octra_vm.C_mach.replay_in artifact.plan machine_inputs with
    | Some [expected] when Octra_vm.C_mach.equal expected result -> ()
    | Some _ | None -> fail command "VM result differs from the checked machine"
  end;
  let parsed =
    match Parse.parse raw with
    | Ok value -> value
    | Error error -> fail command (Parse.text error)
  in
  let lowered, _ =
    match Parse.compile parsed with
    | Ok value -> value
    | Error error -> fail command (Parse.text error)
  in
  let eval_inputs =
    List.map2
      (fun bind (value : Input.core_value) -> bind, value.value)
      lowered.Octra_vm.C_low.inputs values
  in
  begin
    match Eval.run_in eval_inputs lowered.term with
    | Ok out when Eval.equal out.value eval_result -> ()
    | Ok _ | Error _ -> fail command "VM result differs from the evaluator"
  end;
  method_name, result, outcome

let run path feed_path method_name values =
  let raw = source path in
  let artifact = compile "run" raw (feed_opt "run" feed_path) in
  match artifact.result with
  | Some expected ->
    if Option.is_some method_name || values <> [] then
      fail "run" "runtime arguments do not apply to a closed program";
    let result = run_octb "run" artifact.octb in
    if not (Octra_vm.C_mach.equal result expected) then
      fail "run" "VM result differs from the checked machine";
    Printf.printf
      "status = pass command = run emission = %s result = %s veil = %s\n"
      (emission artifact) (lit_text result) (veil artifact)
  | None ->
    if Option.is_some feed_path then
      fail "run" "feed and runtime arguments are mutually exclusive";
    let method_name, result, outcome =
      open_source "run" raw artifact method_name values
    in
    Printf.printf
      "status = pass command = run emission = %s method = %s result = %s effort = %d steps = %d veil = %s\n"
      (emission artifact) method_name (lit_text result) outcome.effort
      outcome.steps (veil artifact)

let open_octb command raw method_name values =
  let image = decode command raw in
  if Array.length image.inputs = 0 then
    fail command "runtime arguments do not apply to a closed program";
  let output =
    match image.output with
    | Some value -> value
    | None -> fail command "OCTB result type is absent"
  in
  let method_name = main_method command method_name in
  let values = octb_values command image.inputs values in
  let outcome = local_run ~trace:true command raw method_name values in
  open_machine command image.code values outcome;
  let result, _ = core_result command output outcome.result in
  image, method_name, result, outcome

let run_open_octb command raw method_name values =
  let image, method_name, result, outcome =
    open_octb command raw method_name values
  in
  Printf.printf
    "status = pass command = %s input = octb emission = %s method = %s result = %s effort = %d steps = %d vm = AML storage = memory veil = %s\n"
    command (Octb.image_emission image) method_name (lit_text result)
    outcome.effort outcome.steps (Octb.image_veil image)

let test_open_octb command raw method_name values =
  let left_image, left_method, left_result, left =
    open_octb command raw method_name values
  in
  let right_image, right_method, right_result, right =
    open_octb command raw method_name values
  in
  if left_image.emission <> right_image.emission
      || left_image.veil <> right_image.veil
      || not (String.equal left_method right_method)
      || not (Octra_vm.C_mach.equal left_result right_result)
      || left.effort <> right.effort || left.steps <> right.steps
      || left.storage <> right.storage || left.events <> right.events then
    fail command "repeated execution differs";
  Printf.printf
    "status = pass command = %s input = octb emission = %s repeats = 2 method = %s result = %s effort = %d steps = %d sha256 = %s veil = %s\n"
    command (Octb.image_emission left_image) left_method (lit_text left_result)
    left.effort left.steps (sha raw) (Octb.image_veil left_image)

let op_text = function
  | Octb.Load (dst, value) ->
      Printf.sprintf "ldi(r%d,%s)" dst (lit_text value)
  | Octb.Move (dst, src) -> Printf.sprintf "mov(r%d,r%d)" dst src
  | Octb.Plus (dst, left, right) ->
      Printf.sprintf "add(r%d,r%d,r%d)" dst left right
  | Octb.Times (dst, left, right) ->
      Printf.sprintf "mul(r%d,r%d,r%d)" dst left right
  | Octb.Quotient (dst, left, right) ->
      Printf.sprintf "div(r%d,r%d,r%d)" dst left right
  | Octb.Remainder (dst, left, right) ->
      Printf.sprintf "mod(r%d,r%d,r%d)" dst left right
  | Octb.Negate (dst, src) -> Printf.sprintf "neg(r%d,r%d)" dst src
  | Octb.Absolute (dst, src) -> Printf.sprintf "abs(r%d,r%d)" dst src
  | Octb.Same (dst, left, right) ->
      Printf.sprintf "eq(r%d,r%d,r%d)" dst left right
  | Octb.Less (dst, left, right) ->
      Printf.sprintf "lt(r%d,r%d,r%d)" dst left right
  | Octb.Greater (dst, left, right) ->
      Printf.sprintf "gt(r%d,r%d,r%d)" dst left right
  | Octb.Join (dst, left, right) ->
      Printf.sprintf "concat(r%d,r%d,r%d)" dst left right
  | Octb.Minus (dst, left, right) ->
      Printf.sprintf "sub(r%d,r%d,r%d)" dst left right
  | Octb.Size (dst, src) -> Printf.sprintf "strlen(r%d,r%d)" dst src
  | Octb.Slice (dst, src, first, count) ->
      Printf.sprintf "substr(r%d,r%d,r%d,r%d)" dst src first count
  | Octb.Jump at -> Printf.sprintf "jmp(%d)" at
  | Octb.Jump_if (reg, at) -> Printf.sprintf "jif(r%d,%d)" reg at
  | Octb.Mark at -> Printf.sprintf "jdest(%d)" at
  | Octb.Noop -> "nop"
  | Octb.Stop -> "stop"

let op_reg = function
  | Octb.Load (dst, _) | Octb.Move (dst, _)
  | Octb.Plus (dst, _, _) | Octb.Same (dst, _, _)
  | Octb.Less (dst, _, _) | Octb.Greater (dst, _, _)
  | Octb.Times (dst, _, _)
  | Octb.Quotient (dst, _, _) | Octb.Remainder (dst, _, _)
  | Octb.Negate (dst, _) | Octb.Absolute (dst, _)
  | Octb.Join (dst, _, _) | Octb.Minus (dst, _, _)
  | Octb.Size (dst, _) | Octb.Slice (dst, _, _, _) -> Some dst
  | Octb.Jump_if (reg, _) -> Some reg
  | Octb.Stop -> Some 0
  | Octb.Jump _ | Octb.Mark _ | Octb.Noop -> None

let reg_text machine = function
  | None -> "none"
  | Some reg -> lit_text (VM.value machine reg)

type debug_req = {
  feed : string option;
  cap : int option;
  points : Dbg.point list;
  expect : Emit.lit option;
  trace : string option;
  compare : string option;
  session : string option;
  resume : string option;
}

let debug_req = {
  feed = None;
  cap = None;
  points = [];
  expect = None;
  trace = None;
  compare = None;
  session = None;
  resume = None;
}

let one command name prior value =
  match prior with
  | None -> Some value
  | Some _ -> fail command (name ^ " is repeated")

let int command name raw =
  match int_of_string_opt raw with
  | Some value when String.equal (string_of_int value) raw -> value
  | _ -> fail command (name ^ " is invalid")

let natural command name raw =
  match Z.of_string raw with
  | value when Z.sign value >= 0 && String.equal (Z.to_string value) raw -> value
  | _ -> fail command (name ^ " is invalid")
  | exception Invalid_argument _ -> fail command (name ^ " is invalid")

let epoch command raw =
  let value = natural command "epoch" raw in
  if Folio.epoch_valid value then value
  else
    fail command
      (Printf.sprintf "epoch is invalid maximum = %s"
        (Z.to_string Folio.epoch_max))

let rec debug_args req = function
  | [] -> req
  | "--feed" :: path :: rest ->
    debug_args { req with feed = one "debug" "feed path" req.feed path } rest
  | "--cap" :: raw :: rest ->
    debug_args { req with cap = one "debug" "step cap" req.cap (int "debug" "step cap" raw) } rest
  | "--break-pc" :: raw :: rest ->
    debug_args { req with points = Dbg.Pc (int "debug" "program counter" raw) :: req.points } rest
  | "--break-line" :: raw :: rest ->
    debug_args { req with points = Dbg.Line (int "debug" "source line" raw) :: req.points } rest
  | "--expect" :: raw :: rest ->
    let value =
      match Dbg.lit raw with
      | Some value -> value
      | None -> fail "debug" (Dbg.text Dbg.Expect)
    in
    debug_args { req with expect = one "debug" "expected result" req.expect value } rest
  | "--trace" :: path :: rest ->
    debug_args { req with trace = one "debug" "trace path" req.trace path } rest
  | "--compare" :: path :: rest ->
    debug_args { req with compare = one "debug" "comparison path" req.compare path } rest
  | "--session" :: path :: rest ->
    debug_args { req with session = one "debug" "session path" req.session path } rest
  | "--resume" :: path :: rest ->
    debug_args { req with resume = one "debug" "resume path" req.resume path } rest
  | _ -> fail "debug" "option is invalid"

let distinct source req =
  let values =
    List.filter_map Fun.id [
      Some ("source", source);
      Option.map (fun path -> "feed", path) req.feed;
      Option.map (fun path -> "trace", path) req.trace;
      Option.map (fun path -> "comparison", path) req.compare;
      Option.map (fun path -> "session", path) req.session;
      Option.map (fun path -> "resume", path) req.resume;
    ]
  in
  let rec loop = function
    | [] -> ()
    | (name, path) :: rest ->
      begin
        match List.find_opt (fun (_, other) -> String.equal path other) rest with
        | Some (other, _) -> fail "debug" (name ^ " and " ^ other ^ " paths overlap")
        | None -> loop rest
      end
  in
  loop values

let trace_text rows =
  match List.rev rows with
  | [] -> ""
  | values -> String.concat "\n" values ^ "\n"

let debug_with path fixed args =
  let req = debug_args debug_req args in
  if Option.is_some fixed && Option.is_some req.feed then
    fail "debug" "project feed cannot be replaced";
  distinct path req;
  let raw = source path in
  let feed =
    match fixed with
    | Some value -> Some value
    | None -> feed_opt "debug" req.feed
  in
  let artifact = compile "debug" raw feed in
  if artifact.inputs <> [] then
    fail "debug" "runtime input debugging is unavailable";
  let proved =
    match feed with
    | None ->
      begin
        match Path.make raw with
        | Ok value -> value
        | Error error -> fail "debug" (Path.text error)
      end
    | Some feed ->
      begin
        match Path.make_feed raw feed with
        | Ok value -> value
        | Error error -> fail "debug" (Path.text error)
      end
  in
  let image = decode "debug" artifact.octb in
  let code = image.code in
  if Array.length code <> Array.length artifact.code
      || Array.length code <> Array.length proved.frames then
    fail "debug" "instruction metadata lengths differ";
  let production = run_octb "debug" artifact.octb in
  let source_hash =
    match feed with
    | None -> sha raw
    | Some feed -> sha (raw ^ "\000" ^ Feed.encode feed)
  in
  let code_hash = sha artifact.octb in
  let cfg, skip, session_path, prior_trace =
    match req.resume with
    | None ->
      let cap = Option.value ~default:(Array.length code) req.cap in
      let cfg =
        match Dbg.make ~cap ~points:req.points ~expect:req.expect with
        | Ok value -> value
        | Error error -> fail "debug" (Dbg.text error)
      in
      cfg, None, req.session, None
    | Some path ->
      if Option.is_some req.cap || req.points <> [] || Option.is_some req.expect
          || Option.is_some req.session then
        fail "debug" "resume configuration is ambiguous";
      let saved =
        match Dbg.decode (source path) with
        | Ok value -> value
        | Error error -> fail "debug" (Dbg.text error)
      in
      if not (String.equal (Dbg.source saved) source_hash
          && String.equal (Dbg.code saved) code_hash) then
        fail "debug" "session program differs";
      Dbg.config saved, Some (Dbg.seen saved), Some path,
      Some (Dbg.seen saved, Dbg.trace saved)
  in
  let point_valid = function
    | Dbg.Pc value -> value < Array.length code
    | Dbg.Line value ->
      Array.exists (fun frame -> frame.Path.span.first.line = value) proved.frames
  in
  if not (List.for_all point_valid (Dbg.points cfg)) then
    fail "debug" "breakpoint is outside the program";
  let machine = state () in
  let rec step count rows replayed =
    if VM.halted machine then `Done (rows, replayed)
    else if VM.pc machine >= Array.length code then
      fail "debug" "VM program counter is outside the program"
    else
      let pc = VM.pc machine in
      let op = artifact.code.(pc) in
      let frame = proved.frames.(pc) in
      let replayed =
        match prior_trace with
        | Some (seen, wanted) when seen = count ->
          if not (String.equal (sha (trace_text rows)) wanted) then
            fail "debug" "session trace differs";
          true
        | _ -> replayed
      in
      begin
        match Dbg.decide cfg ~skip ~seen:count ~pc ~line:frame.span.first.line with
        | Dbg.Limit -> fail "debug" "step cap reached"
        | Dbg.Pause ->
          let text = trace_text rows in
          begin
            match session_path with
            | None -> ()
            | Some path ->
              let saved =
                match Dbg.session ~source:source_hash ~code:code_hash ~cfg
                    ~seen:count ~trace:(sha text) with
                | Ok value -> value
                | Error error -> fail "debug" (Dbg.text error)
              in
              begin
                try write path (Dbg.encode saved)
                with Sys_error reason -> fail "debug" reason
              end
          end;
          Printf.printf
            "status = paused command = debug emission = %s pc = %d steps = %d veil = %s\n"
            (emission artifact) pc count (veil artifact);
          `Pause
        | Dbg.Step ->
          let running =
            match VM.step machine code.(pc) with
            | Ok value -> value
            | Error error -> fail "debug" (VM.text error)
          in
          let reg = Option.map (VM.value machine) (op_reg op) in
          let line = Printf.sprintf
              "event = step pc = %d op = %s line = %d col = %d last_line = %d last_col = %d value = %s shape = %s slots = %s effects = %s steps = %d work = %s fhe_depth = %s halted = %b"
              pc (op_text op) frame.span.first.line frame.span.first.col
              frame.span.last.line frame.span.last.col
              (reg_text machine (op_reg op))
              (Option.fold ~none:"none" ~some:lit_shape reg) (slots_text frame.slots)
              (Octra_vm.C_eff.text (Octra_vm.C_eff.of_list proved.eff))
              (count + 1) (Z.to_string (VM.work machine))
              (Z.to_string proved.depth)
              (not running)
          in
          Printf.printf "%s\n" line;
          let rows = line :: rows in
          if running then step (count + 1) rows replayed else `Done (rows, replayed)
      end
  in
  match step 0 [] false with
  | `Pause -> ()
  | `Done (rows, replayed) ->
    if Option.is_some prior_trace && not replayed then
      fail "debug" "session step is outside the execution path";
    let result = VM.result machine in
    if not (Octra_vm.C_mach.equal result production)
        || not (Octra_vm.C_mach.equal result (checked_result "debug" artifact)) then
      fail "debug" "VM result differs from the checked machine";
    if not (Dbg.check cfg result) then fail "debug" "result differs from expectation";
    let text = trace_text rows in
    begin
      match req.compare with
      | Some path when not (String.equal (source path) text) ->
        fail "debug" "trace differs from comparison"
      | _ -> ()
    end;
    begin
      match req.trace with
      | None -> ()
      | Some path ->
        begin
          try write path text with Sys_error reason -> fail "debug" reason
        end
    end;
    Printf.printf
      "status = pass command = debug emission = %s result = %s trace = %s veil = %s\n"
      (emission artifact) (lit_text result) (sha text) (veil artifact)

let debug path args = debug_with path None args

let debug_octb path args =
  let req = debug_args debug_req args in
  let line_point = function
    | Dbg.Line _ -> true
    | Dbg.Pc _ -> false
  in
  if Option.is_some req.feed || Option.is_some req.session
      || Option.is_some req.resume || List.exists line_point req.points then
    fail "debug" "source options do not apply to OCTB";
  distinct path req;
  let raw = source path in
  let image = decode "debug" raw in
  if Array.length image.inputs <> 0 then
    fail "debug" "runtime input debugging is unavailable";
  let production = run_octb "debug" raw in
  let code = image.code in
  let cap = Option.value ~default:(Array.length code) req.cap in
  let cfg =
    match Dbg.make ~cap ~points:req.points ~expect:req.expect with
    | Ok value -> value
    | Error error -> fail "debug" (Dbg.text error)
  in
  let point_valid = function
    | Dbg.Pc value -> value < Array.length code
    | Dbg.Line _ -> false
  in
  if not (List.for_all point_valid (Dbg.points cfg)) then
    fail "debug" "breakpoint is outside the program";
  let machine = state () in
  let rec step count rows =
    if VM.halted machine then `Done rows
    else if VM.pc machine >= Array.length code then
      fail "debug" "VM program counter is outside the program"
    else
      let pc = VM.pc machine in
      match Dbg.decide cfg ~skip:None ~seen:count ~pc ~line:0 with
      | Dbg.Limit -> fail "debug" "step cap reached"
      | Dbg.Pause ->
        Printf.printf
          "status = paused command = debug emission = %s pc = %d steps = %d veil = %s\n"
          (Octb.image_emission image) pc count (Octb.image_veil image);
        `Pause
      | Dbg.Step ->
        let op = code.(pc) in
        let running =
          match VM.step machine op with
          | Ok value -> value
          | Error error -> fail "debug" (VM.text error)
        in
        let reg = Option.map (VM.value machine) (op_reg op) in
        let row =
          Printf.sprintf
            "event = step pc = %d op = %s value = %s shape = %s steps = %d work = %s halted = %b"
            pc (op_text op) (reg_text machine (op_reg op))
            (Option.fold ~none:"none" ~some:lit_shape reg) (count + 1)
            (Z.to_string (VM.work machine)) (not running)
        in
        Printf.printf "%s\n" row;
        if running then step (count + 1) (row :: rows)
        else `Done (row :: rows)
  in
  match step 0 [] with
  | `Pause -> ()
  | `Done rows ->
    let result = VM.result machine in
    if not (Octra_vm.C_mach.equal result production) then
      fail "debug" "VM result differs from the production VM";
    if not (Dbg.check cfg result) then
      fail "debug" "result differs from expectation";
    let text = trace_text rows in
    begin
      match req.compare with
      | Some path when not (String.equal (source path) text) ->
        fail "debug" "trace differs from comparison"
      | Some _ | None -> ()
    end;
    begin
      match req.trace with
      | None -> ()
      | Some path ->
        begin
          try write path text with Sys_error reason -> fail "debug" reason
        end
    end;
    Printf.printf
      "status = pass command = debug emission = %s result = %s trace = %s veil = %s\n"
      (Octb.image_emission image) (lit_text result) (sha text)
      (Octb.image_veil image)

let feed input values output =
  if String.equal input output || String.equal values output
      || String.equal input (output ^ ".next")
      || String.equal values (output ^ ".next") then
    fail "feed" "input and output paths overlap";
  let raw = source input in
  let specs = feed_specs "feed" raw in
  let feed =
    match Feed.parse specs (source values) with
    | Ok value -> value
    | Error error -> fail "feed" (Feed.text error)
  in
  begin
    try write output (Feed.encode feed)
    with Sys_error reason -> fail "feed" reason
  end;
  Printf.printf "status = pass command = feed values = %d bytes = %d output = %s\n"
    (List.length (Feed.values feed)) (String.length (Feed.encode feed)) output

let inspect path =
  let raw = source path in
  let image = decode "inspect" raw in
  Array.iteri
    (fun pc op ->
      Printf.printf "event = instruction pc = %d op = %s\n"
        pc (Octb.op_text op))
    image.code;
  Printf.printf
    "status = pass command = inspect instructions = %d bytes = %d sha256 = %s\n"
    (Array.length image.code) (String.length raw) (sha raw)

let dump format path =
  let raw = source path in
  let image = decode "dump" raw in
  Aml_dump.write stdout ~format ~digest:(sha raw) raw image

let test path feed_path method_name values =
  let raw = source path in
  let feed = feed_opt "test" feed_path in
  let left = compile "test" raw feed in
  let right = compile "test" raw feed in
  if not (String.equal left.octb right.octb)
      || left.code <> right.code
      || left.emission <> right.emission
      || not (Octra_vm.C_smap.equal left.map right.map)
      || not (Live.equal left.live right.live)
      || left.veils <> right.veils
      || not (Octra_vm.C_nat.equal left.veil_depth right.veil_depth)
      || not (Option.equal Octra_vm.C_mach.equal left.result right.result) then
    fail "test" "repeated compilation differs";
  match left.result with
  | Some expected ->
    if Option.is_some method_name || values <> [] then
      fail "test" "runtime arguments do not apply to a closed program";
    let result = run_octb "test" left.octb in
    if not (Octra_vm.C_mach.equal result expected) then
      fail "test" "VM result differs from the checked machine";
    Printf.printf
      "status = pass command = test emission = %s repeats = 2 result = %s sha256 = %s veil = %s veils = %d veil_depth = %s\n"
      (emission left) (lit_text result) (sha left.octb) (veil left) left.veils
      (Octra_vm.C_nat.text left.veil_depth)
  | None ->
    if Option.is_some feed_path then
      fail "test" "feed and runtime arguments are mutually exclusive";
    let left_method, left_result, left_out =
      open_source "test" raw left method_name values
    in
    let right_method, right_result, right_out =
      open_source "test" raw right method_name values
    in
    if not (String.equal left_method right_method)
        || not (Octra_vm.C_mach.equal left_result right_result)
        || left_out.effort <> right_out.effort
        || left_out.steps <> right_out.steps
        || left_out.storage <> right_out.storage
        || left_out.events <> right_out.events then
      fail "test" "repeated execution differs";
    Printf.printf
      "status = pass command = test emission = %s repeats = 2 method = %s result = %s effort = %d steps = %d sha256 = %s veil = %s veils = %d veil_depth = %s\n"
      (emission left) left_method (lit_text left_result) left_out.effort
      left_out.steps (sha left.octb) (veil left) left.veils
      (Octra_vm.C_nat.text left.veil_depth)

type project_input = {
  image : Pfile.image;
  files : (string * string) list;
}

let inside base path =
  let prefix =
    if String.equal base Filename.dir_sep then base
    else base ^ Filename.dir_sep
  in
  let size = String.length prefix in
  String.length path > size && String.sub path 0 size = prefix

let project_file command base path =
  let full = Filename.concat base path in
  let exact =
    try Unix.realpath full
    with Unix.Unix_error (error, _, _) -> fail command (Unix.error_message error)
  in
  if not (inside base exact) then fail command "project source is outside its directory";
  exact

let project_input command manifest =
  let spec =
    match Pfile.parse (source manifest) with
    | Ok value -> value
    | Error error -> fail command (Pfile.text error)
  in
  let base =
    try Unix.realpath (Filename.dirname manifest)
    with Unix.Unix_error (error, _, _) -> fail command (Unix.error_message error)
  in
  let files =
    List.map (fun path -> path, project_file command base path) (Pfile.paths spec)
  in
  let bodies =
    List.map
      (fun (_, path) ->
        try read path with Sys_error reason -> fail command reason)
      files
  in
  let image =
    match Pfile.make spec bodies with
    | Ok value -> value
    | Error error -> fail command (Pfile.text error)
  in
  { image; files }

let project_make command manifest epoch =
  let input = project_input command manifest in
  let folio =
    match Folio.make input.image.rules ~epoch input.image.project with
    | Ok value -> value
    | Error error -> fail command (Folio.text error)
  in
  input, folio

let project_origins command folio =
  match Folio.origins folio with
  | Some values -> values
  | None -> fail command "project origin is invalid"

let project_artifact command (origin : Folio.origin) =
  let compiled =
    match origin.input with
    | None -> Octb.compile origin.src.body
    | Some input -> Octb.compile_feed origin.src.body input
  in
  match compiled with
  | Ok value -> value
  | Error error -> fail command (Octb.text error)

let emission_counts command folio =
  List.fold_left
    (fun (lowered, specialized) origin ->
      match (project_artifact command origin).emission with
      | Octra_vm.C_mach.Lowered -> lowered + 1, specialized
      | Octra_vm.C_mach.Specialized -> lowered, specialized + 1)
    (0, 0) (project_origins command folio)

let project_check_as command manifest raw_epoch =
  let epoch = epoch command raw_epoch in
  let _, folio = project_make command manifest epoch in
  let lowered, specialized = emission_counts command folio in
  Printf.printf
    "status = pass command = %s roots = %d lowered = %d specialized = %d epoch = %s\n"
    command (List.length folio.parts) lowered specialized (Z.to_string epoch)

let project_check manifest raw_epoch =
  project_check_as "project-check" manifest raw_epoch

let project_build_as command manifest raw_epoch output =
  let epoch = epoch command raw_epoch in
  let _, folio = project_make command manifest epoch in
  let lowered, specialized = emission_counts command folio in
  let raw =
    match Folio.file folio with
    | Some value -> value
    | None -> fail command "folio encoding failed"
  in
  let staged = output ^ ".next" in
  if Sys.file_exists output || Sys.file_exists staged then
    fail command "output path exists";
  begin
    try Unix.mkdir staged 0o755 with
    | Unix.Unix_error (error, _, _) -> fail command (Unix.error_message error)
  end;
  let result =
    try
      write (Filename.concat staged "project.cf1") raw;
      List.iter
        (fun (part : Folio.part) ->
          write (Filename.concat staged (part.name ^ ".octb")) part.octb)
        folio.parts;
      Unix.rename staged output;
      Ok ()
    with
    | Sys_error reason -> Error reason
    | Unix.Unix_error (error, _, _) ->
      Error (Unix.error_message error)
  in
  begin
    match result with
    | Ok () -> ()
    | Error reason ->
      discard_dir staged;
      fail command reason
  end;
  Printf.printf
    "status = pass command = %s roots = %d lowered = %d specialized = %d bytes = %d sha256 = %s output = %s\n"
    command (List.length folio.parts) lowered specialized (String.length raw)
    (sha raw) output

let project_build manifest raw_epoch output =
  project_build_as "project-build" manifest raw_epoch output

let folio command path =
  let raw = source path in
  match Folio.verify raw with
  | Ok value -> raw, value
  | Error error -> fail command (Folio.text error)

let root_input command (root : Proj.root) =
  if String.equal root.feed "" then None
  else
    match Feed.decode root.feed with
    | Ok value -> Some value
    | Error error -> fail command (Feed.text error)

let project_origin command folio name =
  match
    List.find_opt
      (fun (value : Folio.origin) -> String.equal value.root.name name)
      (project_origins command folio)
  with
  | Some value -> value
  | None -> fail command "root name is absent"

let project_result command (origin : Folio.origin) =
  checked_result command (project_artifact command origin)

let project_run path name =
  let _, folio = folio "project-run" path in
  let origin = project_origin "project-run" folio name in
  let result = run_octb "project-run" origin.part.octb in
  let artifact = project_artifact "project-run" origin in
  let expected = checked_result "project-run" artifact in
  if not (Octra_vm.C_mach.equal result expected) then
    fail "project-run" "VM result differs from the checked root";
  Printf.printf
    "status = pass command = project-run root = %s emission = %s result = %s veil = %s\n"
    name (emission artifact) (lit_text result) (veil artifact)

let project_inspect path =
  let raw, folio = folio "project-inspect" path in
  let origins = project_origins "project-inspect" folio in
  List.iter
    (fun (origin : Folio.origin) ->
      let inputs, feed_sha =
        match origin.input with
        | None -> 0, "none"
        | Some input ->
          List.length (Feed.values input), sha (Feed.encode input)
      in
      let artifact = project_artifact "project-inspect" origin in
      let result = checked_result "project-inspect" artifact in
      Printf.printf
        "event = root name = %s path = %s emission = %s source_bytes = %d inputs = %d bytes = %d instructions = %d slot_rows = %d source_sha256 = %s feed_sha256 = %s octb_sha256 = %s result = %s veil = %s\n"
        origin.root.name origin.root.path (emission artifact)
        (String.length origin.src.body) inputs
        (String.length origin.part.octb) (Array.length origin.spans)
        (Array.length origin.rows) (sha origin.src.body) feed_sha
        (sha origin.part.octb) (lit_text result) (veil artifact))
    origins;
  Printf.printf
    "status = pass command = project-inspect roots = %d epoch = %s bytes = %d sha256 = %s\n"
    (List.length folio.parts) (Z.to_string folio.epoch) (String.length raw)
    (sha raw)

let project_repeated command manifest raw_epoch =
  let epoch = natural command "epoch" raw_epoch in
  let _, left = project_make command manifest epoch in
  let _, right = project_make command manifest epoch in
  let left_raw =
    match Folio.file left with
    | Some value -> value
    | None -> fail command "left folio encoding failed"
  in
  let right_raw =
    match Folio.file right with
    | Some value -> value
    | None -> fail command "right folio encoding failed"
  in
  if not (String.equal left_raw right_raw) then
    fail command "repeated project compilation differs";
  match Folio.verify left_raw with
  | Error error -> fail command (Folio.text error)
  | Ok checked -> checked, left_raw

let project_test_as command manifest raw_epoch =
  let checked, left_raw = project_repeated command manifest raw_epoch in
  let origins = project_origins command checked in
  List.iter
    (fun (origin : Folio.origin) ->
      let result = run_octb command origin.part.octb in
      let expected = project_result command origin in
      if not (Octra_vm.C_mach.equal result expected) then
        fail command "VM result differs from the checked root")
    origins;
  let lowered, specialized = emission_counts command checked in
  Printf.printf
    "status = pass command = %s repeats = 2 roots = %d lowered = %d specialized = %d sha256 = %s\n"
    command (List.length checked.parts) lowered specialized (sha left_raw)

let project_test manifest raw_epoch =
  project_test_as "project-test" manifest raw_epoch

let project_debug manifest name args =
  let input = project_input "project-debug" manifest in
  let root =
    match
      List.find_opt
        (fun (value : Proj.root) -> String.equal value.name name)
        (Proj.roots input.image.project)
    with
    | Some value -> value
    | None -> fail "project-debug" "root name is absent"
  in
  let path =
    match List.assoc_opt root.path input.files with
    | Some value -> value
    | None -> fail "project-debug" "root source is absent"
  in
  debug_with path (root_input "project-debug" root) args

let usage () =
  Printf.eprintf
    "usage = aml version | check SOURCE [--feed AF1] | feed SOURCE VALUES AF1 | build SOURCE OCTB [--feed AF1] | run SOURCE [--feed AF1] | debug SOURCE [OPTIONS] | inspect OCTB | test SOURCE [--feed AF1] | project check FILE EPOCH | project build FILE EPOCH DIR | project run CF1 ROOT | project debug FILE ROOT [OPTIONS] | project inspect CF1 | project test FILE EPOCH\n";
  exit 2

let main argv =
  try
    match Array.to_list argv with
    | [_; "version"] | [_; "--version"] -> version ()
    | [_; "check"; path] -> check path None
    | [_; "check"; path; "--feed"; feed] -> check path (Some feed)
    | [_; "feed"; input; values; output] -> feed input values output
    | [_; "build"; input; output] -> build input output None
    | [_; "build"; input; output; "--feed"; feed] ->
      build input output (Some feed)
    | [_; "run"; path] -> run path None None []
    | [_; "run"; path; "--feed"; feed] -> run path (Some feed) None []
    | _ :: "debug" :: path :: args -> debug path args
    | [_; "inspect"; path] -> inspect path
    | [_; "test"; path] -> test path None None []
    | [_; "test"; path; "--feed"; feed] -> test path (Some feed) None []
    | [_; "project"; "check"; manifest; epoch] ->
      project_check manifest epoch
    | [_; "project"; "build"; manifest; epoch; output] ->
      project_build manifest epoch output
    | [_; "project"; "run"; path; name] -> project_run path name
    | _ :: "project" :: "debug" :: manifest :: name :: args ->
      project_debug manifest name args
    | [_; "project"; "inspect"; path] -> project_inspect path
    | [_; "project"; "test"; manifest; epoch] -> project_test manifest epoch
    | _ -> usage ()
  with
  | Stack_overflow -> fail "aml" "stack capacity exceeded"
  | Out_of_memory -> fail "aml" "memory capacity exceeded"
  | Invalid_argument reason -> fail "aml" reason
  | Failure reason -> fail "aml" reason