(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

module VM = Octra_vm.C_octb
module Rval = Octra_vm.C_rval
module Typ = Octra_vm.C_type
module Eval = Octra_vm.C_eval
module Pc = Set.Make (Int)
module Pc_map = Map.Make (Int)

type format = Text | Events | Dot

let select = function
  | [] | ["--format"; "text"] -> Ok Text
  | ["--format"; "events"] -> Ok Events
  | ["--format"; "dot"] -> Ok Dot
  | _ -> Error "option is invalid"

type flow = Next | Jump | Yes | No | Call | Resume

type edge = {
  src : int;
  dst : int;
  flow : flow;
  label : int option;
}

type block = {
  first : int;
  last : int;
}

type refs = {
  starts : Pc.t;
  ins : string list Pc_map.t;
  outs : string list Pc_map.t;
  calls : string list Pc_map.t;
  call_sites : int list Pc_map.t;
  resumes : int Pc_map.t;
}

type const_ref = {
  pc : int;
  id : int;
  use : string;
}

type data_row = {
  path : string;
  typ : Typ.t;
  form : string;
  value : Eval.value;
}

type owner = Main | Func of int

type analysis = {
  digest : string;
  raw : string;
  code : VM.op array;
  image : VM.image;
  symbols : (int * int) list;
  routines : int list;
  label_pcs : int Pc_map.t;
  symbols_at : int list Pc_map.t;
  entries_at : owner list Pc_map.t;
  parts : block list;
  graph : edge list;
  nexts : edge list Pc_map.t;
  links : refs;
  owners : owner list Pc_map.t;
  owned : block list Pc_map.t;
  const_refs : const_ref list;
  refs_at : const_ref Pc_map.t;
  uses : string list Pc_map.t;
}

let flow_text = function
  | Next -> "next"
  | Jump -> "jump"
  | Yes -> "true"
  | No -> "false"
  | Call -> "call"
  | Resume -> "resume"

let block_text pc = Printf.sprintf "b%04d" pc
let label_text id = Printf.sprintf "l%04d" id
let function_text id = Printf.sprintf "f%04d" id
let const_text id = Printf.sprintf "c%04d" id
let pc_text pc = Printf.sprintf "p%04d" pc
let offset_text value = Printf.sprintf "0x%08x" value

let owner_text = function
  | Main -> "main"
  | Func id -> function_text id

let owner_compare left right =
  match left, right with
  | Main, Main -> 0
  | Main, Func _ -> -1
  | Func _, Main -> 1
  | Func left, Func right -> Int.compare left right

let add_pc size pc values =
  if pc >= 0 && pc < size then Pc.add pc values else values

let cut = function
  | VM.Jump _ | VM.Jump_if _ | VM.Stop -> true
  | _ -> false

let labels code =
  let rec loop pc out =
    if pc = Array.length code then List.rev out
    else
      match code.(pc) with
      | VM.Mark id -> loop (pc + 1) ((id, pc) :: out)
      | _ -> loop (pc + 1) out
  in
  loop 0 []

let label_map values =
  List.fold_left
    (fun out (id, pc) -> Pc_map.add id pc out)
    Pc_map.empty values

let label_pc values id =
  match Pc_map.find_opt id values with
  | Some pc -> pc
  | None -> invalid_arg "verified jump label is absent"

let functions _ = []

let leaders code label_pcs =
  let size = Array.length code in
  let rec loop pc values =
    if pc = size then Pc.elements values
    else
      let op = code.(pc) in
      let values =
        match op with
        | VM.Mark _ -> add_pc size pc values
        | _ -> values
      in
      let values =
        match op with
        | VM.Jump id | VM.Jump_if (_, id) ->
          add_pc size (label_pc label_pcs id) values
        | _ -> values
      in
      let values = if cut op then add_pc size (pc + 1) values else values in
      loop (pc + 1) values
  in
  loop 0 (Pc.singleton 0)

let blocks code label_pcs =
  let size = Array.length code in
  let rec loop out = function
    | [] -> List.rev out
    | [first] -> List.rev ({ first; last = size - 1 } :: out)
    | first :: ((next :: _) as rest) ->
      loop ({ first; last = next - 1 } :: out) rest
  in
  loop [] (leaders code label_pcs)

let edges code label_pcs block =
  let next flow =
    if block.last + 1 < Array.length code then
      [{ src = block.first; dst = block.last + 1; flow; label = None }]
    else []
  in
  match code.(block.last) with
  | VM.Jump id ->
    [{ src = block.first; dst = label_pc label_pcs id;
       flow = Jump; label = Some id }]
  | VM.Jump_if (_, id) ->
    { src = block.first; dst = label_pc label_pcs id;
      flow = Yes; label = Some id } :: next No
  | VM.Stop -> []
  | _ -> next Next

let target starts pc =
  if Pc.mem pc starts then block_text pc
  else Printf.sprintf "pc:%d" pc

let list_text values = "[" ^ String.concat "," values ^ "]"

let push key value values =
  let prior = Option.value ~default:[] (Pc_map.find_opt key values) in
  Pc_map.add key (value :: prior) values

let refs values key =
  Option.value ~default:[] (Pc_map.find_opt key values) |> List.rev

let index blocks edges =
  let starts =
    List.fold_left (fun out block -> Pc.add block.first out) Pc.empty blocks
  in
  List.fold_left
    (fun out edge ->
      let ins =
        push edge.dst
          (flow_text edge.flow ^ ":" ^ block_text edge.src)
          out.ins
      in
      let outs =
        push edge.src
          (flow_text edge.flow ^ ":" ^ target starts edge.dst)
          out.outs
      in
      let calls =
        match edge.flow, edge.label with
        | Call, Some id -> push id (block_text edge.src) out.calls
        | _ -> out.calls
      in
      let call_sites =
        match edge.flow, edge.label with
        | Call, Some id -> push id edge.src out.call_sites
        | _ -> out.call_sites
      in
      let resumes =
        if edge.flow = Resume then Pc_map.add edge.src edge.dst out.resumes
        else out.resumes
      in
      { out with ins; outs; calls; call_sites; resumes })
    { starts; ins = Pc_map.empty; outs = Pc_map.empty; calls = Pc_map.empty;
      call_sites = Pc_map.empty; resumes = Pc_map.empty }
    edges

let incoming links block =
  let entry = if block.first = 0 then ["entry"] else [] in
  list_text (entry @ refs links.ins block.first)

let outgoing links block = list_text (refs links.outs block.first)
let callers links id = list_text (refs links.calls id)

let u16 raw at =
  Char.code raw.[at] lor (Char.code raw.[at + 1] lsl 8)

let const_refs raw code (cells : VM.code_cell array) =
  Array.to_list
    (Array.mapi
      (fun pc op ->
        let at = cells.(pc).at in
        match op with
        | VM.Load _ -> Some { pc; id = u16 raw (at + 2); use = "load" }
        | _ -> None)
      code)
  |> List.filter_map Fun.id

let edge_index graph =
  List.fold_left (fun out edge -> push edge.src edge out) Pc_map.empty graph

let outgoing_edges nexts pc =
  refs nexts pc |> List.filter (fun edge -> edge.flow <> Call)

let reachable nexts entry =
  let rec loop pending seen =
    match pending with
    | [] -> seen
    | pc :: rest when Pc.mem pc seen -> loop rest seen
    | pc :: rest ->
      let next = List.map (fun edge -> edge.dst) (outgoing_edges nexts pc) in
      loop (next @ rest) (Pc.add pc seen)
  in
  loop [entry] Pc.empty

let owner_entries label_pcs routines =
  (Main, 0) ::
  List.map (fun id -> Func id, label_pc label_pcs id) routines

let owner_index label_pcs routines nexts =
  List.fold_left
    (fun out (owner, entry) ->
      Pc.fold
        (fun pc map -> push pc owner map)
        (reachable nexts entry) out)
    Pc_map.empty (owner_entries label_pcs routines)
  |> Pc_map.map (List.sort_uniq owner_compare)

let owners values pc =
  Option.value ~default:[] (Pc_map.find_opt pc values)

let owner_list values pc =
  match owners values pc with
  | [] -> "[orphan]"
  | found -> list_text (List.map owner_text found)

let function_blocks value owner =
  let key = match owner with Main -> -1 | Func id -> id in
  refs value.owned key

let owned_index parts owner_map =
  List.fold_left
    (fun out block ->
      List.fold_left
        (fun map owner ->
          let key = match owner with Main -> -1 | Func id -> id in
          push key block map)
        out (owners owner_map block.first))
    Pc_map.empty parts

let terminal code block =
  match code.(block.last) with
  | VM.Stop -> true
  | _ -> false

let return_block code block =
  match code.(block.last) with
  | VM.Stop -> true
  | _ -> false

let block_list blocks = list_text (List.map (fun block -> block_text block.first) blocks)

let function_exits value owner =
  function_blocks value owner |> List.filter (terminal value.code)

let function_returns value owner =
  function_blocks value owner |> List.filter (return_block value.code)

let function_calls value owner =
  function_blocks value owner
  |> List.concat_map (fun block -> refs value.nexts block.first)
  |> List.filter_map (fun edge ->
    match edge.flow, edge.label with
    | Call, Some id -> Some (function_text id)
    | _ -> None)
  |> List.sort_uniq String.compare
  |> list_text

let call_resumes value id =
  refs value.links.call_sites id
  |> List.filter_map (fun site -> Pc_map.find_opt site value.links.resumes)
  |> List.sort_uniq Int.compare
  |> List.map block_text
  |> list_text

let rec iter_range pc last fn =
  if pc <= last then begin
    fn pc;
    iter_range (pc + 1) last fn
  end

let line out value =
  output_string out value;
  output_char out '\n'

let emit out format = Printf.ksprintf (line out) format

let hex raw at size =
  let shown = min size 12 in
  let parts =
    List.init shown (fun index ->
      Printf.sprintf "%02x" (Char.code raw.[at + index]))
  in
  String.concat "" parts ^ if shown < size then ".." else ""

let digest value = Digestif.SHA256.(to_hex (digest_string value))

let emission image =
  VM.image_emission image

let veil image = VM.image_veil image

let veils image = VM.image_veils image

let veil_depth image = VM.image_veil_depth image

let output image =
  Option.fold ~none:"none" ~some:Typ.text image.VM.output

let finite_text field value =
  if String.length value <= 72 then value, ""
  else
    String.sub value 0 48 ^ "...",
    Printf.sprintf " %s = %d sha256 = %s"
      field (String.length value) (digest value)

let int_text value =
  if String.length value <= 72 then value, ""
  else
    let digits =
      String.length value - if value.[0] = '-' then 1 else 0
    in
    String.sub value 0 48 ^ "...",
    Printf.sprintf " digits = %d sha256 = %s" digits (digest value)

let value_text = function
  | Eval.Int value -> int_text (Z.to_string value)
  | value -> finite_text "chars" (Eval.value_text value)

let bytes_text value =
  let shown = min 24 (String.length value) in
  let body =
    List.init shown (fun index -> Printf.sprintf "%02x" (Char.code value.[index]))
    |> String.concat ""
  in
  let tail = if shown < String.length value then "..." else "" in
  Printf.sprintf "hex:%s%s/%d" body tail (String.length value)

let data_rows item =
  let rec walk out = function
    | [] -> List.rev out
    | (path, typ, value) :: rest ->
      let form, children =
        match typ, value with
        | Typ.Unit, Eval.Unit -> "unit", []
        | Typ.Bool, Eval.Bool _ -> "bool", []
        | Typ.Int, Eval.Int _ -> "int", []
        | Typ.Bytes _, Eval.Bytes _ -> "bytes", []
        | Typ.Vec (_, elem), Eval.Vec values ->
          let children =
            Array.to_list
              (Array.mapi
                (fun index value ->
                  Printf.sprintf "%s[%d]" path index, elem, value)
                values)
          in
          "vec", children
        | Typ.Pair (left_ty, right_ty), Eval.Pair (left, right) ->
          "pair", [path ^ ".left", left_ty, left;
            path ^ ".right", right_ty, right]
        | Typ.Sum (left_ty, _), Eval.Inl value ->
          "left", [path ^ ".left", left_ty, value]
        | Typ.Sum (_, right_ty), Eval.Inr value ->
          "right", [path ^ ".right", right_ty, value]
        | _ -> "invalid", []
      in
      walk ({ path; typ; form; value } :: out) (children @ rest)
  in
  walk [] ["root", Rval.typ item, Rval.value item]

let constant_data = function
  | VM.CData value -> Some value
  | _ -> None

let constant_value value =
  match constant_data value with
  | Some item ->
    let body, facts = value_text (Rval.value item) in
    "data", "\"" ^ String.escaped body ^ "\"", facts
  | None ->
    match value with
  | VM.CInt value ->
    let body, facts = int_text value in
    "int", body, facts
  | VM.CBool value -> "bool", string_of_bool value, ""
  | VM.CData value ->
    let body, facts = value_text (Rval.value value) in
    "data", "\"" ^ String.escaped body ^ "\"", facts
  | VM.CText value -> "text", "\"" ^ String.escaped value ^ "\"", ""
  | VM.CBytes value -> "bytes", bytes_text value, ""

let write_data_text out id value =
  match constant_data value with
  | None -> ()
  | Some item ->
    List.iter
      (fun row ->
        let body, facts = value_text row.value in
        emit out "data = %s path = %s type = \"%s\" form = %s value = \"%s\"%s"
          (const_text id) row.path (String.escaped (Typ.text row.typ)) row.form
          (String.escaped body) facts)
      (data_rows item)

let write_data_event out id value =
  match constant_data value with
  | None -> ()
  | Some item ->
    List.iter
      (fun row ->
        let body, facts = value_text row.value in
        emit out
          "event = data constant = %s path = %s type = \"%s\" form = %s value = \"%s\"%s"
          (const_text id) row.path (String.escaped (Typ.text row.typ)) row.form
          (String.escaped body) facts)
      (data_rows item)

let const_ref_at value pc =
  Pc_map.find_opt pc value.refs_at

let const_users value id =
  list_text (refs value.uses id)

let resolved_op label_pcs reference = function
  | VM.Load (dst, _) ->
    begin
      match reference with
      | Some item -> Printf.sprintf "LDI r%d, %s" dst (const_text item.id)
      | None -> invalid_arg "verified constant reference is absent"
    end
  | VM.Jump id ->
    Printf.sprintf "JMP %s <%s>" (label_text id)
      (block_text (label_pc label_pcs id))
  | VM.Jump_if (reg, id) ->
    Printf.sprintf "JIF r%d, %s <%s>" reg (label_text id)
      (block_text (label_pc label_pcs id))
  | VM.Mark id -> Printf.sprintf "JDEST %s" (label_text id)
  | op -> String.escaped (VM.op_text op)

let labels_at value pc = refs value.symbols_at pc

let entries_at value pc =
  refs value.entries_at pc

let analyze ~digest raw image =
  let code = image.VM.code in
  let symbols = labels code in
  let routines = functions code in
  let label_pcs = label_map symbols in
  let symbols_at =
    List.fold_left (fun out (id, pc) -> push pc id out) Pc_map.empty symbols
  in
  let entries_at =
    owner_entries label_pcs routines
    |> List.fold_left
      (fun out (owner, pc) -> push pc owner out)
      Pc_map.empty
  in
  let parts = blocks code label_pcs in
  let graph = List.concat_map (edges code label_pcs) parts in
  let nexts = edge_index graph in
  let links = index parts graph in
  let owners = owner_index label_pcs routines nexts in
  let owned = owned_index parts owners in
  let const_refs = const_refs raw code image.cells in
  let refs_at =
    List.fold_left
      (fun out item -> Pc_map.add item.pc item out)
      Pc_map.empty const_refs
  in
  let uses =
    List.fold_left
      (fun out item -> push item.id (item.use ^ ":" ^ pc_text item.pc) out)
      Pc_map.empty const_refs
  in
  { digest; raw; code; image; symbols; routines; label_pcs; symbols_at;
    entries_at; parts; graph; nexts; links; owners; owned; const_refs; refs_at;
    uses }

let status out value =
  emit out
    "status = pass command = dump emission = %s output = %s instructions = %d blocks = %d edges = %d bytes = %d sha256 = %s veil = %s veils = %s veil_depth = %s"
    (emission value.image) (output value.image) (Array.length value.code)
    (List.length value.parts)
    (List.length value.graph) (String.length value.raw) value.digest
    (veil value.image) (veils value.image) (veil_depth value.image)

let write_function out value owner =
  let blocks = function_blocks value owner in
  let exits = function_exits value owner in
  let callers_text =
    match owner with
    | Main -> "[]"
    | Func id -> callers value.links id
  in
  let entry =
    match owner with
    | Main -> 0
    | Func id -> label_pc value.label_pcs id
  in
  emit out "function = %s entry = %s callers = %s blocks = %s exits = %s calls = %s"
    (owner_text owner) (block_text entry) callers_text (block_list blocks)
    (block_list exits) (function_calls value owner)

let write_text out value =
  emit out
    "image = octb version = 1 vm = AML emission = %s output = %s bytes = %d instructions = %d sha256 = %s veil = %s veils = %s veil_depth = %s"
    (emission value.image) (output value.image) (String.length value.raw)
    (Array.length value.code) value.digest (veil value.image) (veils value.image)
    (veil_depth value.image);
  emit out "section = .head file = %s size = 12 entries = 1" (offset_text 0);
  emit out "section = .const file = %s size = %d entries = %d" (offset_text 12)
    (value.image.text_at - 12) (Array.length value.image.consts);
  emit out "section = .text file = %s size = %d entries = %d"
    (offset_text value.image.text_at)
    (String.length value.raw - value.image.text_at)
    (Array.length value.code);
  Array.iter
    (fun (row : VM.const_row) ->
      let kind, body, facts = constant_value row.value in
      emit out
        "constant = %s file = %s size = %d type = %s value = %s%s refs = %s"
        (const_text row.id) (offset_text row.at) row.size kind body facts
        (const_users value row.id);
      write_data_text out row.id row.value)
    value.image.consts;
  write_function out value Main;
  List.iter (fun id -> write_function out value (Func id)) value.routines;
  List.iter
    (fun block ->
      List.iter
        (fun owner ->
          emit out "symbol = %s pc = %d block = %s kind = function"
            (owner_text owner) block.first (block_text block.first))
        (entries_at value block.first);
      List.iter
        (fun id ->
          emit out "symbol = %s pc = %d block = %s kind = label"
            (label_text id) block.first (block_text block.first))
        (labels_at value block.first);
      emit out "block = %s first = %d last = %d owners = %s incoming = %s outgoing = %s"
        (block_text block.first) block.first block.last
        (owner_list value.owners block.first)
        (incoming value.links block) (outgoing value.links block);
      iter_range block.first block.last (fun pc ->
        let cell = value.image.cells.(pc) in
        let data = hex value.raw cell.at cell.size in
        let reference = const_ref_at value pc in
        let op = resolved_op value.label_pcs reference value.code.(pc) in
        let constant, use =
          match reference with
          | None -> "none", "none"
          | Some item -> const_text item.id, item.use
        in
        emit out
          "instruction = %s address = %s file = %s size = %d bytes = %s op = %s constant = %s use = %s"
          (pc_text pc) (offset_text pc) (offset_text cell.at) cell.size data op
          constant use))
    value.parts;
  List.iter
    (fun edge ->
      let symbol = Option.fold ~none:"none" ~some:label_text edge.label in
      emit out "xref = code source = %s target = %s type = %s symbol = %s"
        (block_text edge.src) (target value.links.starts edge.dst)
        (flow_text edge.flow) symbol)
    value.graph;
  List.iter
    (fun item ->
      emit out "xref = data source = %s target = %s type = %s"
        (pc_text item.pc) (const_text item.id) item.use)
    value.const_refs;
  List.iter
    (fun id ->
      emit out "xref = return function = %s exits = %s resumes = %s"
        (function_text id) (block_list (function_returns value (Func id)))
        (call_resumes value id))
    value.routines;
  status out value

let write_events out value =
  emit out
    "event = image format = OCTB version = 1 vm = AML emission = %s output = %s bytes = %d instructions = %d sha256 = %s veil = %s veils = %s veil_depth = %s"
    (emission value.image) (output value.image) (String.length value.raw)
    (Array.length value.code) value.digest (veil value.image) (veils value.image)
    (veil_depth value.image);
  emit out "event = section name = .head file = 0 size = 12 entries = 1";
  emit out "event = section name = .const file = 12 size = %d entries = %d"
    (value.image.text_at - 12) (Array.length value.image.consts);
  emit out "event = section name = .text file = %d size = %d entries = %d"
    value.image.text_at (String.length value.raw - value.image.text_at)
    (Array.length value.code);
  Array.iter
    (fun (row : VM.const_row) ->
      let kind, body, facts = constant_value row.value in
      emit out
        "event = constant name = %s file = %d size = %d type = %s value = %s%s refs = %s"
        (const_text row.id) row.at row.size kind body facts
        (const_users value row.id);
      write_data_event out row.id row.value)
    value.image.consts;
  emit out
    "event = graph entry = %s blocks = %d edges = %d symbols = %d functions = %d"
    (block_text 0) (List.length value.parts) (List.length value.graph)
    (List.length value.symbols) (List.length value.routines + 1);
  List.iter
    (fun (id, pc) ->
      emit out "event = symbol name = %s pc = %d exact = %b"
        (label_text id) pc (id = pc))
    value.symbols;
  let event_function owner =
    let blocks = function_blocks value owner in
    let exits = function_exits value owner in
    match owner with
    | Main ->
      emit out
        "event = function name = main symbol = entry entry = b0000 callers = [] blocks = %s exits = %s calls = %s"
        (block_list blocks) (block_list exits) (function_calls value owner)
    | Func id ->
      let pc = label_pc value.label_pcs id in
      emit out
        "event = function name = %s symbol = %s entry = %s callers = %s blocks = %s exits = %s calls = %s"
        (function_text id) (label_text id) (block_text pc)
        (callers value.links id) (block_list blocks) (block_list exits)
        (function_calls value owner)
  in
  event_function Main;
  List.iter (fun id -> event_function (Func id)) value.routines;
  List.iter
    (fun block ->
      emit out
        "event = block id = %s first = %d last = %d incoming = %s outgoing = %s owners = %s"
        (block_text block.first) block.first block.last
        (incoming value.links block) (outgoing value.links block)
        (owner_list value.owners block.first);
      iter_range block.first block.last (fun pc ->
        let cell = value.image.cells.(pc) in
        let reference = const_ref_at value pc in
        let constant =
          match reference with
          | None -> "none"
          | Some item -> const_text item.id ^ ":" ^ item.use
        in
        emit out
          "event = instruction block = %s pc = %d op = %s file = %d bytes = %s constant = %s"
          (block_text block.first) pc
          (String.escaped (resolved_op value.label_pcs reference value.code.(pc)))
          cell.at (hex value.raw cell.at cell.size) constant))
    value.parts;
  List.iter
    (fun edge ->
      let symbol = Option.fold ~none:"none" ~some:label_text edge.label in
      emit out "event = edge source = %s flow = %s target = %s symbol = %s"
        (block_text edge.src) (flow_text edge.flow)
        (target value.links.starts edge.dst) symbol)
    value.graph;
  List.iter
    (fun item ->
      emit out "event = xref source = %s kind = %s target = %s"
        (pc_text item.pc) item.use (const_text item.id))
    value.const_refs;
  List.iter
    (fun id ->
      emit out "event = return function = %s exits = %s resumes = %s"
        (function_text id) (block_list (function_returns value (Func id)))
        (call_resumes value id))
    value.routines;
  status out value

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

let dot_label value block =
  let rows = ref ["block = " ^ block_text block.first ^
    " owners = " ^ owner_list value.owners block.first] in
  iter_range block.first block.last (fun pc ->
    rows := Printf.sprintf "pc = %04d op = %s" pc
      (resolved_op value.label_pcs (const_ref_at value pc) value.code.(pc)) :: !rows);
  dot_escape (String.concat "\n" (List.rev !rows))

let write_dot out value =
  line out "digraph octb {";
  emit out "  graph [label = \"OCTB/1 %s\", labelloc = t];" value.digest;
  line out "  node [shape = box, fontname = monospace];";
  line out "  edge [fontname = monospace];";
  List.iter
    (fun block ->
      let entries = entries_at value block.first in
      let ring = if entries = [] then "" else ", peripheries = 2" in
      emit out "  \"%s\" [label = \"%s\"%s];"
        (block_text block.first) (dot_label value block) ring)
    value.parts;
  List.iter
    (fun edge ->
      let style = if edge.flow = Call then ", style = dashed" else "" in
      emit out "  \"%s\" -> \"%s\" [label = \"%s\"%s];"
        (block_text edge.src) (target value.links.starts edge.dst)
        (flow_text edge.flow) style)
    value.graph;
  line out "}"

let write out ~format ~digest raw image =
  let value = analyze ~digest raw image in
  match format with
  | Text -> write_text out value
  | Events -> write_events out value
  | Dot -> write_dot out value