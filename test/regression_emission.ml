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
module Feed = Octra_vm.C_feed
module Bin = Octra_vm.C_bin
module Sess = Octra_vm.C_sess
module Sha = Octra_vm.C_sha
module Parse = Octra_vm.C_parse
module Eval = Octra_vm.C_eval
module Limit = Octra_vm.C_limit
module Rval = Octra_vm.C_rval

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

let local ?(trace = false) ?(view = true) ?(grants = [])
    name artifact method_name args =
  let image =
    match Octra_vm.Bytecode.decode_image artifact.Octb.octb with
    | Ok value -> value
    | Error _ -> fail name
  in
  let config =
    Local.config
      ~view
      ~byte_result:Vm.Typed_bytes
      ~method_name
      ~args
      ~grants
      ()
  in
  match Local.run ~trace config image.code with
  | Ok value -> value
  | Error _ -> fail name

let local_code ?(view = true) ?(grants = []) name code method_name args =
  let config =
    Local.config
      ~view
      ~byte_result:Vm.Typed_bytes
      ~method_name
      ~args
      ~grants
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

let raw_image name artifact =
  match Bytecode.decode_image artifact.Octb.octb with
  | Ok image -> image
  | Error _ -> fail name

let wrapper_label target =
  target = Octb.dispatch_label 0
  || target = Octb.dispatch_label 1
  || target >= Octb.check_label 0 0
    && target < Octb.check_label Octb.input_limit 0
  || target >= Octb.data_label 0
    && target < Octb.data_label Octb.label_limit
  || target >= Octb.guard_label 0
    && target < Octb.guard_label Octb.label_limit
  || target >= Octb.body_label 0

let wrapper_labels name artifact =
  let code = (raw_image name artifact).Bytecode.code in
  let marks =
    Array.fold_left
      (fun out -> function Vm.JDEST target -> target :: out | _ -> out)
      [] code
  in
  if List.length marks <> List.length (List.sort_uniq Int.compare marks) then
    fail (name ^ " duplicate");
  Array.iter
    (function
      | Vm.JDEST target ->
        if not (wrapper_label target) then fail (name ^ " mark")
      | Vm.JMP target | Vm.JIF (_, target) ->
        if not (wrapper_label target) || not (List.mem target marks) then
          fail (name ^ " target")
      | _ -> ())
    code

let recode image code =
  Bytecode.encode ?state:image.Bytecode.state ?proof:image.proof
    ?emission:image.emission ?veil:image.veil code

let schema inputs output results =
  let reg value = Option.bind (Nat.of_int value) Bin.num in
  let code =
    Option.bind (Bin.list_code Bin.ty_code inputs) (fun inputs ->
      Option.bind (Bin.ty_code output) (fun output ->
        Option.map
          (fun results ->
            Bin.Tag (Z.zero,
              Bin.Cons (inputs,
                Bin.Cons (output, Bin.Cons (results, Bin.Nil)))))
          (Bin.list_code reg results)))
  in
  match Option.bind code Bin.enc_code with
  | Some bits ->
    "\000OCTRA_AML_OPEN\000"
    ^ String.of_seq (List.to_seq (List.map (fun bit -> if bit then '1' else '0') bits))
  | None -> fail "schema"

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

let open_vec = {|
program OpenVec {
  input many values: vec[4, int]
  term vec[int](at[3](values), at[1](values), at[2](values), at[0](values))
}
|}

let open_pair = {|
program OpenPair {
  input erase empty: unit
  input many value: int * bool
  term split value as many number: int, many flag: bool in
    (if flag then number + 1 else number - 1, flag)
}
|}

let open_sum = {|
program OpenSum {
  input many value: result[int, bool]
  term value
}
|}

let open_unit = {|
program OpenUnit {
  input erase value: unit
  term unit
}
|}

let open_erased = {|
program OpenErased {
  input erase first: int
  input erase second: int
  term 2 + 3
}
|}

let open_branches = {|
program OpenBranches {
  input many flag: bool
  term
    let many first: int = if flag then 1 else 2 in
    if flag then first else 3
}
|}

let open_close = {|
program OpenClose {
  permit cap[7] = close
  input once gate: cap[7]
  term close(gate)
}
|}

let open_range = {|
program OpenRange {
  input many value: uint[8]
  term wide(value) + 1
}
|}

let open_signed = {|
program OpenSigned {
  input many value: sint[8]
  term wide(value)
}
|}

let open_fit = {|
program OpenFit {
  input many value: int
  term fit[uint[8]](value)
}
|}

let open_seq = {|
program OpenSeq {
  input many xs: seq[8, uint[8]]
  term (
    length(xs),
    fold xs from 0 with
      many item: uint[8], once sum: int => wide(item) + sum
  )
}
|}

let seq_trailing = {|
program SeqTrailing {
  term seq[4, int](1,)
}
|}

let open_seq_id = {|
program OpenSeqId {
  input many xs: seq[4, uint[8]]
  term xs
}
|}

let open_seq32 = {|
program OpenSeq32 {
  input once xs: seq[32, uint[64]]
  term
    fold xs from (0, 0) with
      many item: uint[64], once state: int * int =>
        split state as once n: int, once sum: int in
          (n + 1, wide(item) + sum)
}
|}

let wide_vec size =
  Printf.sprintf
    "program WideVec { input erase values: vec[%d, int] term unit }"
    size

let deep_width =
  "program DeepWidth { input erase value: vec[1000000, vec[1000000, vec[1000000, vec[1000000, int]]]] term unit }"

let wide_unit =
  "program WideUnit { input erase value: vec[1000000, unit] term unit }"

let unit_inputs count =
  let inputs =
    List.init count (fun index ->
      Printf.sprintf "input erase value%d: unit" index)
    |> String.concat " "
  in
  "program UnitInputs { " ^ inputs ^ " term unit }"

let service_result =
  let inputs =
    List.init 60 (fun index ->
      Printf.sprintf "input many value%d: int" index)
    |> String.concat " "
  in
  "program ServiceResult { " ^ inputs ^ " term (1, 2) }"

let rec sum_tree depth =
  if depth = 0 then Type.Unit
  else
    let item = sum_tree (depth - 1) in
    Type.Sum (item, item)

let rec sum_text depth =
  if depth = 0 then "unit"
  else
    let item = sum_text (depth - 1) in
    "result[" ^ item ^ "," ^ item ^ "]"

let rec vec_tree depth =
  if depth = 0 then Type.Unit
  else Type.Vec (nat "open schema zero" 0, vec_tree (depth - 1))

let type_nodes_source =
  "program TypeNodes { input many value: " ^ sum_text 11 ^ " term value }"

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

let order_neq = {|
program OrderNeq {
  input many left: int
  input many right: int
  term equal[bool](equal[int](left, right), false)
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
  let neq = compile "order neq" order_neq in
  let less = function Octb.Less _ -> true | _ -> false in
  let greater = function Octb.Greater _ -> true | _ -> false in
  let same = function Octb.Same _ -> true | _ -> false in
  let different = function Octb.Different _ -> true | _ -> false in
  if not (has less lt.code) || has greater lt.code || has same lt.code then
    fail "order lt code";
  if not (has greater le.code) || not (has same le.code) then
    fail "order le code";
  if not (has greater gt.code) || has less gt.code || has same gt.code then
    fail "order gt code";
  if not (has less ge.code) || not (has same ge.code) then
    fail "order ge code";
  if not (has different neq.code) || has same neq.code then
    fail "order neq code";
  let neq_sha = Digestif.SHA256.(to_hex (digest_string neq.octb)) in
  if String.length neq.octb <> 178
      || not (String.equal neq_sha
        "174a693862158c01d79561e2b29dba8ad7e5d93d6481e885809a4f0687acfa50") then
    fail "order neq bytes";
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
  output "order neq output" Type.Bool neq;
  check "order lt" lt false 44 22;
  check "order le" le true 47 24;
  check "order gt" gt false 44 22;
  check "order ge" ge true 47 24;
  check "order neq" neq false 44 22;
  let out = local "order neq apart" neq "main"
    [Vm.VInt (Z.of_int 5); Vm.VInt (Z.of_int 4)] in
  returned "order neq apart" out;
  begin
    match out.result with
    | Vm.VBool true -> ()
    | _ -> fail "order neq apart"
  end;
  if out.effort <> 44 || out.steps <> 22 then fail "order neq apart cost";
  let changed =
    native "order neq mutation" neq
    |> Array.map (function Vm.NEQ (dst, left, right) -> Vm.EQ (dst, left, right)
      | op -> op)
  in
  let changed = local_code "order neq mutation" changed "main"
    [Vm.VInt (Z.of_int 5); Vm.VInt (Z.of_int 4)] in
  begin
    match changed.result with
    | Vm.VBool false -> ()
    | _ -> fail "order neq mutation"
  end

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
      (replace bool_code (bool_count - 8) (Vm.LDI (0, Vm.VInt Z.one)))
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

let typed_open name artifact raws =
  let image = decoded name artifact in
  let values =
    match Input.core_octb image.inputs raws with
    | Ok values -> values
    | Error _ -> fail (name ^ " input")
  in
  let args =
    List.concat_map (fun (value : Input.core_value) -> value.vms) values
  in
  let outcome = local ~trace:true name artifact "main" args in
  returned name outcome;
  begin
    match image.output with
    | Some output ->
      begin
        match
          Aml_cli.open_match ~guarded:image.guarded ~entry:image.entry image.code output
            image.results values outcome
        with
        | Ok () -> ()
        | Error _ -> fail (name ^ " match")
      end
    | None -> fail (name ^ " output")
  end;
  let result =
    match image.output with
    | Some output -> fst (Aml_cli.core_result name output image.results outcome.regs)
    | None -> fail (name ^ " output")
  in
  image, outcome, result

let typed_result name typ raw found =
  let expected =
    match Feed.parse_value typ raw with
    | Ok value -> Mach.literal typ value
    | Error _ -> None
  in
  match expected with
  | Some value when Mach.equal value found -> ()
  | Some _ | None -> fail name

let eval_source name source raws =
  let parsed =
    match Parse.parse source with
    | Ok value -> value
    | Error error -> failwith (name ^ " reason = " ^ Parse.text error)
  in
  let prog, info =
    match Parse.compile parsed with
    | Ok value -> value
    | Error error -> failwith (name ^ " reason = " ^ Parse.text error)
  in
  let rec inputs out binds values =
    match binds, values with
    | [], [] -> List.rev out
    | bind :: bind_rest, raw :: raw_rest ->
      begin
        match Feed.parse_value bind.Term.typ raw with
        | Ok value -> inputs ((bind, value) :: out) bind_rest raw_rest
        | Error _ -> fail (name ^ " input")
      end
    | _, _ -> fail (name ^ " arity")
  in
  let values = inputs [] prog.inputs raws in
  let out =
    match Eval.run_in values prog.term with
    | Ok value -> value
    | Error error -> failwith (name ^ " reason = " ^ Eval.text error)
  in
  let used = Limit.used ~steps:out.steps ~work:out.work in
  if not (Limit.le used info.res) then fail (name ^ " resource");
  info.typ, out

let type_codec name typ =
  match Option.bind (Bin.ty_code typ) Bin.ty_get with
  | Some found when Type.equal typ found -> ()
  | Some _ | None -> fail name

let range_checks () =
  let bits = nat "range bits" 8 in
  let u8 = Type.Num (Type.Unsigned, bits) in
  let s8 = Type.Num (Type.Signed, bits) in
  let u64 = Type.Num (Type.Unsigned, nat "range bits" 64) in
  let seq8 = Type.Seq (nat "sequence cap" 8, u8) in
  let seq4 = Type.Seq (nat "sequence id cap" 4, u8) in
  let seq32 = Type.Seq (nat "sequence cap" 32, u64) in
  begin
    match Parse.parse seq_trailing with
    | Error _ -> ()
    | Ok _ -> fail "sequence trailing comma"
  end;
  begin
    match Type.range Type.Unsigned bits, Type.range Type.Signed bits with
    | Some (ulow, uhigh), Some (slow, shigh)
        when Z.equal ulow Z.zero
          && Z.equal uhigh (Z.of_int 255)
          && Z.equal slow (Z.of_int (-128))
          && Z.equal shigh (Z.of_int 127) -> ()
    | _, _ -> fail "range limits"
  end;
  if Type.valid (Type.Num (Type.Unsigned, Nat.zero))
      || Type.valid (Type.Num (Type.Signed, nat "range over" 257))
      || Type.valid (Type.Seq (Nat.one, Type.Cap Nat.one)) then
    fail "range type admission";
  for width = 1 to Type.max_bits do
    let bits = nat "range generated bits" width in
    let scale = Z.shift_left Z.one width in
    let half = Z.shift_left Z.one (width - 1) in
    let cases = [
      Type.Unsigned, Z.zero, Z.pred scale;
      Type.Signed, Z.neg half, Z.pred half;
    ] in
    List.iter
      (fun (sign, low, high) ->
        let typ = Type.Num (sign, bits) in
        begin
          match Type.range sign bits with
          | Some (found_low, found_high)
              when Z.equal low found_low && Z.equal high found_high -> ()
          | Some _ | None -> fail "range generated limits"
        end;
        List.iter
          (fun (value, wanted) ->
            if Type.admits typ value <> wanted then
              fail "range generated admission")
          [Z.pred low, false; low, true; high, true; Z.succ high, false];
        type_codec "range generated codec" typ)
      cases
  done;
  List.iter (fun typ -> type_codec "range type codec" typ)
    [u8; s8; u64; seq8; seq4; seq32];
  for cap = 0 to 16 do
    for len = 0 to cap do
      let cap_nat = nat "sequence generated cap" cap in
      let typ = Type.Seq (cap_nat, u8) in
      let values =
        Array.init cap (fun index ->
          Eval.Int (if index < len then Z.of_int (index + 1) else Z.zero))
      in
      let value = Eval.Pair (Eval.Int (Z.of_int len), Eval.Vec values) in
      if not (Eval.typed typ value) then fail "sequence generated type";
      begin
        match Mach.atoms typ value with
        | Some atoms ->
          begin
            match Mach.value typ atoms with
            | Some (found, []) when Eval.equal found value -> ()
            | Some _ | None -> fail "sequence generated machine"
          end
        | None -> fail "sequence generated atoms"
      end;
      begin
        match Rval.make typ value with
        | Ok image ->
          begin
            match Rval.decode (Rval.encode image) with
            | Ok found when Rval.equal image found -> ()
            | Ok _ | Error _ -> fail "sequence generated result"
          end
        | Error _ -> fail "sequence generated image"
      end;
      if len < cap then begin
        let changed = Array.copy values in
        changed.(len) <- Eval.Int Z.one;
        let hidden = Eval.Pair (Eval.Int (Z.of_int len), Eval.Vec changed) in
        if Eval.typed typ hidden then fail "sequence generated tail"
      end
    done
  done;
  let range = compile "open range" open_range in
  let signed = compile "open signed" open_signed in
  let fit = compile "open fit" open_fit in
  let sequence = compile "open sequence" open_seq in
  let identity = compile "open sequence identity" open_seq_id in
  let sequence32 = compile "open sequence 32" open_seq32 in
  List.iter (wrapper_labels "sequence labels")
    [range; signed; fit; sequence; identity; sequence32];
  List.iter
    (fun artifact ->
      expect "range lowered" Mach.Lowered artifact;
      if Option.is_some artifact.Octb.result then fail "range result")
    [range; signed; fit; sequence; identity; sequence32];
  output "range output" Type.Int range;
  output "signed output" Type.Int signed;
  output "fit output" (Type.Sum (u8, Type.Int)) fit;
  output "sequence output" (Type.Pair (Type.Int, Type.Int)) sequence;
  output "sequence identity output" seq4 identity;
  output "sequence 32 output" (Type.Pair (Type.Int, Type.Int)) sequence32;
  let check_scalar name artifact typ raw wanted effort steps =
    let _, outcome, result = typed_open name artifact [raw] in
    typed_result (name ^ " result") typ wanted result;
    if outcome.effort <> effort || outcome.steps <> steps then
      fail (name ^ " cost")
  in
  check_scalar "range zero" range Type.Int "int:0" "1" 51 26;
  check_scalar "range high" range Type.Int "int:255" "256" 51 26;
  check_scalar "signed low" signed Type.Int "int:-128" "-128" 46 24;
  check_scalar "signed high" signed Type.Int "int:127" "127" 46 24;
  begin
    match Input.core_octb [|u8|] ["int:-1"],
        Input.core_octb [|u8|] ["int:256"] with
    | Error _, Error _ -> ()
    | _, _ -> fail "range input admission"
  end;
  refused "range raw low" (local "range raw low" range "main" [Vm.VInt Z.minus_one]);
  refused "range raw high"
    (local "range raw high" range "main" [Vm.VInt (Z.of_int 256)]);
  let fit_cases = [
    "int:-1", "err(-1)", 57, 33;
    "int:0", "ok(0)", 70, 34;
    "int:255", "ok(255)", 70, 34;
    "int:256", "err(256)", 57, 28;
  ] in
  List.iter
    (fun (raw, wanted, effort, steps) ->
      check_scalar ("fit " ^ raw) fit (Type.Sum (u8, Type.Int)) raw wanted
        effort steps)
    fit_cases;
  let seq_cases = [
    "seq()", "(0,0)", 475, 234;
    "seq(7)", "(1,7)", 482, 243;
    "seq(1,2,3)", "(3,6)", 496, 261;
    "seq(1,2,3,4,5,6,7,8)", "(8,36)", 531, 306;
  ] in
  List.iter
    (fun (raw, wanted, effort, steps) ->
      let _, outcome, result = typed_open ("sequence " ^ raw) sequence [raw] in
      typed_result ("sequence result " ^ raw)
        (Type.Pair (Type.Int, Type.Int)) wanted result;
      if outcome.effort <> effort || outcome.steps <> steps then
        fail ("sequence cost " ^ raw);
      let typ, evaluated = eval_source ("sequence eval " ^ raw) open_seq [raw] in
      begin
        match Mach.literal typ evaluated.value with
        | Some found when Mach.equal found result -> ()
        | Some _ | None -> fail ("sequence evaluator " ^ raw)
      end)
    seq_cases;
  let full =
    List.init 32 (fun index -> string_of_int (index + 1))
    |> String.concat ","
    |> Printf.sprintf "seq(%s)"
  in
  let _, outcome, result = typed_open "sequence 32" sequence32 [full] in
  typed_result "sequence 32 result" (Type.Pair (Type.Int, Type.Int))
    "(32,528)" result;
  if outcome.effort <> 2194 || outcome.steps <> 1273 then
    fail "sequence 32 cost";
  let typ, evaluated = eval_source "sequence 32 eval" open_seq32 [full] in
  begin
    match Mach.literal typ evaluated.value with
    | Some found when Mach.equal found result -> ()
    | Some _ | None -> fail "sequence 32 evaluator"
  end;
  begin
    match Input.core_octb [|seq8|]
        ["seq(1,2,3,4,5,6,7,8,9)"],
      Input.core_octb [|seq8|] ["seq(1,)"] with
    | Error _, Error _ -> ()
    | _, _ -> fail "sequence text admission"
  end;
  let seq_args len values =
    Vm.VInt (Z.of_int len)
    :: List.map (fun value -> Vm.VInt (Z.of_int value)) values
  in
  refused "sequence negative length"
    (local "sequence negative length" sequence "main"
      (seq_args (-1) [0; 0; 0; 0; 0; 0; 0; 0]));
  refused "sequence excessive length"
    (local "sequence excessive length" sequence "main"
      (seq_args 9 [0; 0; 0; 0; 0; 0; 0; 0]));
  refused "sequence active range"
    (local "sequence active range" sequence "main"
      (seq_args 1 [256; 0; 0; 0; 0; 0; 0; 0]));
  refused "sequence hidden tail"
    (local "sequence hidden tail" sequence "main"
      (seq_args 0 [1; 0; 0; 0; 0; 0; 0; 0]));
  let image = decoded "sequence identity image" identity in
  let raw = raw_image "sequence identity raw" identity in
  let args = seq_args 0 [0; 0; 0; 0] in
  let reject_output name at value =
    let changed = replace raw.code (image.entry + at) value in
    let encoded = recode raw changed in
    begin
      match Octb.decode encoded with
      | Ok _ -> ()
      | Error _ -> fail (name ^ " decode")
    end;
    refused name (local_code name changed "main" args)
  in
  reject_output "sequence output length" 0
    (Vm.LDI (image.results.(0), Vm.VInt (Z.of_int 5)));
  reject_output "sequence output range" 1
    (Vm.LDI (image.results.(1), Vm.VInt (Z.of_int 256)));
  reject_output "sequence output tail" 4
    (Vm.LDI (image.results.(4), Vm.VInt Z.one))

let structural_checks () =
  let vec_type = Type.Vec (nat "open vec length" 4, Type.Int) in
  let pair_type = Type.Pair (Type.Int, Type.Bool) in
  let sum_type = Type.Sum (Type.Int, Type.Bool) in
  let vec = compile "open vec" open_vec in
  let pair = compile "open pair" open_pair in
  let sum = compile "open sum" open_sum in
  let unit = compile "open unit" open_unit in
  let erased = compile "open erased" open_erased in
  let branches = compile "open branches" open_branches in
  List.iter
    (fun artifact ->
      expect "structured lowered" Mach.Lowered artifact;
      if Option.is_some artifact.Octb.result then fail "structured result")
    [vec; pair; sum; unit];
  List.iter (wrapper_labels "structured labels")
    [vec; pair; sum; unit; branches];
  begin
    match erased.Octb.code with
    | [|Octb.Load (1, Emit.Int first); Octb.Load (2, Emit.Int second);
        Octb.Plus (1, 1, 2); Octb.Move (0, 1); Octb.Stop|]
        when Z.equal first (Z.of_int 2) && Z.equal second (Z.of_int 3) -> ()
    | _ -> fail "open erased register order"
  end;
  let opaque = [|Octb.Mark 0; Octb.Jump 0|] in
  let opaque_raw =
    match Octb.encode opaque with
    | Ok value -> value
    | Error _ -> fail "opaque backward encode"
  in
  begin
    match Octb.decode opaque_raw with
    | Ok image when image.code = opaque && Option.is_none image.emission -> ()
    | Ok _ | Error _ -> fail "opaque backward compatibility"
  end;
  let branch_raw = raw_image "open branches raw" branches in
  let rec first_mark pc =
    if pc = Array.length branch_raw.code then fail "open branch mark"
    else
      match branch_raw.code.(pc) with
      | Vm.JDEST target when target >= 10_000_000 -> pc, target
      | _ -> first_mark (pc + 1)
  in
  let mark_pc, mark = first_mark 0 in
  let changed = Array.copy branch_raw.code in
  let rec change pc =
    if pc = Array.length changed then fail "open backward jump"
    else
      match changed.(pc) with
      | Vm.JIF (reg, _) when pc > mark_pc ->
        changed.(pc) <- Vm.JIF (reg, mark)
      | Vm.JMP _ when pc > mark_pc -> changed.(pc) <- Vm.JMP mark
      | _ -> change (pc + 1)
  in
  change (mark_pc + 1);
  begin
    match Octb.decode (recode branch_raw changed) with
    | Error (Octb.Jump_ref _) -> ()
    | Error _ | Ok _ -> fail "open backward jump accepted"
  end;
  let vec_image, vec_out, vec_result =
    typed_open "open vec" vec ["vec(1,2,3,4)"]
  in
  if not vec_image.guarded then fail "open vec guard";
  if vec_image.code <> vec.code then fail "open vec machine body";
  let first =
    match Input.core_octb [|vec_type|] ["vec(1,2,3,4)"] with
    | Ok value -> value
    | Error _ -> fail "open vec first input"
  in
  let second =
    match Input.core_octb [|vec_type|] ["vec(4,3,2,1)"] with
    | Ok value -> value
    | Error _ -> fail "open vec second input"
  in
  if String.equal
      (Aml_cli.input_hash open_vec "main" first)
      (Aml_cli.input_hash open_vec "main" second) then
    fail "open vec input hash";
  typed_result "open vec result" vec_type "vec(4,2,3,1)" vec_result;
  if Array.length vec_image.results <> 4 then fail "open vec results";
  let _, pair_out, pair_result =
    typed_open "open pair" pair ["unit"; "(8,true)"]
  in
  typed_result "open pair result" pair_type "(9,true)" pair_result;
  let _, sum_left, left_result = typed_open "open sum left" sum ["ok(7)"] in
  typed_result "open sum left result" sum_type "ok(7)" left_result;
  let _, sum_right, right_result = typed_open "open sum right" sum ["err(true)"] in
  typed_result "open sum right result" sum_type "err(true)" right_result;
  let unit_image, unit_out, unit_result = typed_open "open unit" unit ["unit"] in
  typed_result "open unit result" Type.Unit "unit" unit_result;
  if Array.length unit_image.results <> 0 then fail "open unit results";
  let wide = compile "open width" (wide_vec 60) in
  let wide_items = List.init 60 string_of_int |> String.concat "," in
  let wide_raw = "vec(" ^ wide_items ^ ")" in
  let wide_image, wide_out, wide_result =
    typed_open "open width" wide [wide_raw]
  in
  typed_result "open width result" Type.Unit "unit" wide_result;
  if Array.length wide_image.results <> 0 then fail "open width results";
  let units = compile "open zero width" (unit_inputs 61) in
  let unit_values = List.init 61 (fun _ -> "unit") in
  let zero_image, zero_out, zero_result =
    typed_open "open zero width" units unit_values
  in
  typed_result "open zero width result" Type.Unit "unit" zero_result;
  if Array.length zero_image.inputs <> 61
      || Array.length zero_image.results <> 0 then
    fail "open zero width schema";
  compile_refused "open width limit" "machine input count = 61 maximum = 60"
    (wide_vec 61);
  compile_refused "open deep width"
    "machine input count = 1000000000000000000000000 maximum = 60"
    deep_width;
  compile_refused "open layout limit"
    "machine layout cells = 1000002 maximum = 4096" wide_unit;
  compile_refused "open type limit"
    "machine type nodes = 8190 maximum = 4096" type_nodes_source;
  compile_refused "open result register limit"
    "OCTB result registers must be distinct and below 61" service_result;
  if vec_out.storage <> [] || vec_out.events <> []
      || pair_out.storage <> [] || pair_out.events <> []
      || sum_left.storage <> [] || sum_left.events <> []
      || sum_right.storage <> [] || sum_right.events <> []
      || unit_out.storage <> [] || unit_out.events <> []
      || wide_out.storage <> [] || wide_out.events <> []
      || zero_out.storage <> [] || zero_out.events <> [] then
    fail "structured effects";
  begin
    match Input.core_octb vec_image.inputs ["vec(1,2,3)"] with
    | Error _ -> ()
    | Ok _ -> fail "open vec short"
  end;
  refused "open vec leaf type"
    (local "open vec leaf type" vec "main"
      [Vm.VBool true; Vm.VInt (Z.of_int 2); Vm.VInt (Z.of_int 3);
       Vm.VInt (Z.of_int 4)]);
  refused "open sum tag type"
    (local "open sum tag type" sum "main"
      [Vm.VInt Z.one; Vm.VInt (Z.of_int 7)]);
  let raw = raw_image "open vec raw" vec in
  let changed = Array.copy raw.code in
  begin
    match changed.(7) with
    | Vm.LDI (61, Vm.VString value) ->
      changed.(7) <- Vm.LDI (61, Vm.VString (value ^ "0"))
    | _ -> fail "open vec schema marker"
  end;
  begin
    match Octb.decode (recode raw changed) with
    | Error Octb.Schema_invalid -> ()
    | Error _ | Ok _ -> fail "open vec schema mutation"
  end;
  let changed = Array.copy raw.code in
  changed.(7) <-
    Vm.LDI (61, Vm.VString (schema [vec_type] vec_type [61; 1; 2; 3]));
  begin
    match Octb.decode (recode raw changed) with
    | Error Octb.Schema_invalid -> ()
    | Error _ | Ok _ -> fail "open vec service register"
  end;
  let changed = Array.copy raw.code in
  changed.(7) <-
    Vm.LDI (61, Vm.VString (schema [vec_type] vec_type [0; 0; 2; 3]));
  begin
    match Octb.decode (recode raw changed) with
    | Error Octb.Schema_invalid -> ()
    | Error _ | Ok _ -> fail "open vec repeated register"
  end;
  let changed = Array.copy raw.code in
  let wide = Type.Vec (nat "open schema length" 1000000, Type.Unit) in
  changed.(7) <- Vm.LDI (61, Vm.VString (schema [wide] vec_type [0; 1; 2; 3]));
  begin
    match Octb.decode (recode raw changed) with
    | Error Octb.Schema_invalid -> ()
    | Error _ | Ok _ -> fail "open vec schema cell limit"
  end;
  let deep = sum_tree 11 in
  begin
    match Type.nodes deep with
    | Some 4095 -> ()
    | Some _ | None -> fail "open schema type nodes"
  end;
  let edge = vec_tree Type.max_depth in
  let over = vec_tree (Type.max_depth + 1) in
  begin
    match Type.nodes edge, Type.nodes over with
    | Some count, None when count = Type.max_depth + 1 -> ()
    | _, _ -> fail "open schema type depth"
  end;
  let changed = Array.copy raw.code in
  changed.(7) <-
    Vm.LDI (61, Vm.VString (schema [deep] deep (List.init 11 Fun.id)));
  begin
    match Octb.decode (recode raw changed) with
    | Error Octb.Schema_invalid -> ()
    | Error _ | Ok _ -> fail "open schema type limit"
  end;
  let changed = Array.copy raw.code in
  changed.(7) <-
    Vm.LDI (61, Vm.VString (schema [over] vec_type [0; 1; 2; 3]));
  begin
    match Octb.decode (recode raw changed) with
    | Error Octb.Schema_invalid -> ()
    | Error _ | Ok _ -> fail "open schema depth limit"
  end;
  let changed = Array.copy raw.code in
  let oversized =
    "\000OCTRA_AML_OPEN\000" ^ String.make ((Type.max_nodes * 128) + 1) '0'
  in
  changed.(7) <- Vm.LDI (61, Vm.VString oversized);
  begin
    match Octb.decode (recode raw changed) with
    | Error Octb.Schema_invalid -> ()
    | Error _ | Ok _ -> fail "open schema bit limit"
  end;
  let changed = Array.copy raw.code in
  changed.(12) <- Vm.NOP;
  begin
    match Octb.decode (recode raw changed) with
    | Error (Octb.Opcode _) -> ()
    | Error _ | Ok _ -> fail "open vec check mutation"
  end;
  let changed = Array.copy raw.code in
  changed.(Array.length changed - 2) <- Vm.NOP;
  begin
    match Octb.decode (recode raw changed) with
    | Error (Octb.Opcode _) -> ()
    | Error _ | Ok _ -> fail "open vec result guard mutation"
  end

let close_checks () =
  List.iter
    (fun input ->
      let expected = Digestif.SHA256.(to_raw_string (digest_string input)) in
      if not (String.equal (Sha.hash input) expected) then
        fail "open close sha")
    [""; "abc"; String.make 129 'x'];
  let artifact = compile "open close" open_close in
  expect "open close emission" Mach.Lowered artifact;
  output "open close output" Type.Unit artifact;
  if not
      (Array.exists
        (function Octb.Cap_close (kind, _) -> Nat.equal kind (nat "close kind" 7)
          | _ -> false)
        artifact.code)
  then fail "open close code";
  let image = decoded "open close image" artifact in
  let values =
    match Input.core_octb image.inputs ["cap[7](9)"] with
    | Ok values -> values
    | Error _ -> fail "open close input"
  in
  let args =
    List.concat_map (fun (value : Input.core_value) -> value.vms) values
  in
  let cap =
    match args with
    | [Vm.VCap cap] -> cap
    | _ -> fail "open close grant"
  in
  let outcome =
    local ~trace:true ~view:false ~grants:[cap]
      "open close runtime" artifact "main" args
  in
  returned "open close runtime" outcome;
  if outcome.closes <> [cap] || outcome.storage <> [] || outcome.events <> [] then
    fail "open close effects";
  begin
    match
      Aml_cli.open_match ~guarded:image.guarded ~entry:image.entry image.code Type.Unit
        image.results values outcome
    with
    | Ok () -> ()
    | Error _ -> fail "open close match"
  end;
  let direct = [|
    Vm.MLOAD (1, 1001);
    Vm.CAP_CHECK (Z.of_int 7, 1);
    Vm.CAP_CLOSE (Z.of_int 7, 1);
    Vm.STOP;
  |] in
  let run ?(view = false) ?(grants = [cap]) code =
    let config = Local.config ~view ~grants ~method_name:"main" ~args () in
    match Local.run_at ~trace:false config ~entry:0 code with
    | Ok value -> value
    | Error _ -> fail "open close direct"
  in
  let exact = run direct in
  returned "open close exact" exact;
  if exact.effort <> 74 || exact.steps <> 4 || exact.closes <> [cap] then
    fail "open close exact cost";
  let raw = Bytecode.encode direct in
  begin
    match Bytecode.decode_image raw with
    | Ok decoded when decoded.code = direct -> ()
    | Ok _ | Error _ -> fail "open close wire"
  end;
  begin
    match Vm.Verifier.verify [|Vm.LDI (0, Vm.VCap cap); Vm.STOP|] with
    | Error (Vm.Verifier.CapabilityLiteral 0) -> ()
    | Error _ | Ok () -> fail "open close literal"
  end;
  begin
    match Vm.Verifier.verify [|Vm.CAP_CLOSE (Z.minus_one, 0); Vm.STOP|] with
    | Error (Vm.Verifier.CapabilityKind (0, kind)) when Z.equal kind Z.minus_one -> ()
    | Error _ | Ok () -> fail "open close kind"
  end;
  let wrong = { cap with scope = String.make 32 '1' } in
  refused "open close absent" (run ~grants:[] direct);
  refused "open close scope" (run ~grants:[wrong] direct);
  refused "open close view" (run ~view:true direct);
  let run_cap value =
    let config =
      Local.config ~view:false ~grants:[value] ~method_name:"main"
        ~args:[Vm.VCap value] ()
    in
    match Local.run_at ~trace:false config ~entry:0 direct with
    | Ok value -> value
    | Error _ -> fail "open close malformed"
  in
  refused "open close scope size"
    (run_cap { cap with scope = String.make 31 '0' });
  refused "open close negative id" (run_cap { cap with id = -1 });
  refused "open close excessive rev"
    (run_cap { cap with rev = 1_000_001 });
  let excessive = List.init 61 (fun _ -> cap) in
  let config =
    Local.config ~view:false ~grants:excessive ~method_name:"main"
      ~args:[Vm.VCap cap] ()
  in
  begin
    match Local.run_at ~trace:false config ~entry:0 direct with
    | Error (Local.Grant_count (60, 61)) -> ()
    | Error _ | Ok _ -> fail "open close grant count"
  end;
  let config =
    Local.config ~view:false ~grants:[cap; cap] ~method_name:"main"
      ~args:[Vm.VCap cap] ()
  in
  begin
    match Local.run_at ~trace:false config ~entry:0 direct with
    | Error Local.Grant_repeat -> ()
    | Error _ | Ok _ -> fail "open close repeated grant"
  end;
  let rollback = run [|
    Vm.MLOAD (1, 1001);
    Vm.CAP_CHECK (Z.of_int 7, 1);
    Vm.CHECKPOINT;
    Vm.CAP_CLOSE (Z.of_int 7, 1);
    Vm.ROLLBACK;
    Vm.STOP;
  |] in
  returned "open close rollback" rollback;
  if rollback.closes <> [] then fail "open close rollback state";
  let nested = run [|
    Vm.MLOAD (1, 1001);
    Vm.CAP_CHECK (Z.of_int 7, 1);
    Vm.CHECKPOINT;
    Vm.CHECKPOINT;
    Vm.CAP_CLOSE (Z.of_int 7, 1);
    Vm.COMMIT;
    Vm.ROLLBACK;
    Vm.STOP;
  |] in
  returned "open close nested" nested;
  if nested.closes <> [] then fail "open close nested state";
  let committed = run [|
    Vm.MLOAD (1, 1001);
    Vm.CAP_CHECK (Z.of_int 7, 1);
    Vm.CHECKPOINT;
    Vm.CAP_CLOSE (Z.of_int 7, 1);
    Vm.COMMIT;
    Vm.STOP;
  |] in
  returned "open close commit" committed;
  if committed.closes <> [cap] then fail "open close commit state";
  refused "open close repeated" (run [|
    Vm.MLOAD (1, 1001);
    Vm.CAP_CHECK (Z.of_int 7, 1);
    Vm.CAP_CLOSE (Z.of_int 7, 1);
    Vm.CAP_CLOSE (Z.of_int 7, 1);
    Vm.STOP;
  |]);
  refused "open close revert" (run [|
    Vm.MLOAD (1, 1001);
    Vm.CAP_CHECK (Z.of_int 7, 1);
    Vm.CAP_CLOSE (Z.of_int 7, 1);
    Vm.REVERT;
  |]);
  refused "open close event" (run [|
    Vm.MLOAD (1, 1001);
    Vm.EMIT ("Leaked", [1]);
    Vm.STOP;
  |]);
  let reject_cap name regs code =
    let state =
      Vm.create_state
        ~strict_values:true
        ~caller:"caller"
        ~origin:"origin"
        ~address:"program"
        ~value:Z.zero
        ~storage:(Hashtbl.create 0)
        ()
    in
    List.iter (fun (reg, value) -> state.Vm.regs.(reg) <- value) regs;
    ignore (Vm.run state code);
    if not state.reverted || state.closes <> [] then fail name
  in
  reject_cap "open close call"
    [1, Vm.VString "target"; 2, Vm.VString "method"; 3, Vm.VCap cap]
    [|Vm.XCALL (0, 1, 2, 3, 1); Vm.STOP|];
  reject_cap "open close spawn"
    [1, Vm.VString "code"; 2, Vm.VCap cap]
    [|Vm.SPAWN2 (0, 1, 2, 1); Vm.STOP|];
  reject_cap "open close memory"
    [1, Vm.VCap cap]
    [|Vm.MSTORE (0, 1); Vm.STOP|];
  reject_cap "open close memory register"
    [1, Vm.VInt Z.zero; 2, Vm.VCap cap]
    [|Vm.MSTORER (1, 2); Vm.STOP|];
  let exceptional =
    Vm.create_state
      ~ctx:{ Vm.default_ctx with cap_live = Vm.cap_equal cap }
      ~caller:"caller"
      ~origin:"origin"
      ~address:"program"
      ~value:Z.zero
      ~storage:(Hashtbl.create 0)
      ()
  in
  exceptional.Vm.regs.(1) <- Vm.VCap cap;
  ignore (Vm.run exceptional [|
    Vm.CAP_CLOSE (Z.of_int 7, 1);
    Vm.JMP (-1);
  |]);
  if not exceptional.reverted || exceptional.closes <> [] then
    fail "open close exceptional refusal";
  let scope =
    match
      Sess.scope ~chain:"chain" ~prog:"program" ~root:(String.make 64 '2')
    with
    | Ok value -> value
    | Error _ -> fail "open close session scope"
  in
  let state, token =
    match Sess.issue (Sess.empty scope) ~kind:(Z.of_int 7) ~id:(Z.of_int 9) with
    | Ok value -> value
    | Error _ -> fail "open close session issue"
  in
  let auth =
    match Local.grant state token with
    | Some (Vm.VCap cap) -> cap
    | Some _ | None -> fail "open close session grant"
  in
  if String.length auth.scope <> 32 then fail "open close scope digest";
  let distinct chain prog root =
    let scope =
      match Sess.scope ~chain ~prog ~root with
      | Ok value -> value
      | Error _ -> fail "open close distinct scope"
    in
    let state, token =
      match Sess.issue (Sess.empty scope) ~kind:(Z.of_int 7) ~id:(Z.of_int 9) with
      | Ok value -> value
      | Error _ -> fail "open close distinct issue"
    in
    match Local.grant state token with
    | Some (Vm.VCap cap) -> cap
    | Some _ | None -> fail "open close distinct grant"
  in
  let variants = [
    distinct "c-hain" "program" (String.make 64 '2');
    distinct "chain" "p-rogram" (String.make 64 '2');
    distinct "chain" "program" (String.make 63 '2' ^ "3");
    distinct "a" "bc" "d";
    distinct "ab" "c" "d";
  ] in
  if List.exists (Vm.cap_equal auth) variants then
    fail "open close scope separation";
  begin
    match List.rev variants with
    | right :: left :: _ when not (Vm.cap_equal left right) -> ()
    | _ -> fail "open close scope framing"
  end;
  let host code =
    let config =
      Local.config ~view:false ~grants:[auth] ~method_name:"main"
        ~args:[Vm.VCap auth] ()
    in
    match Local.run_at ~trace:false config ~entry:0 code with
    | Ok value -> value
    | Error _ -> fail "open close session run"
  in
  let success = host direct in
  let closed, tokens =
    match Local.settle state [token] success with
    | Ok value -> value
    | Error _ -> fail "open close session settle"
  in
  if tokens <> [] || Sess.current closed token
      || Option.is_some (Local.grant closed token) then
    fail "open close session closed";
  begin
    match Local.settle closed [token] success with
    | Error (Local.Session (Sess.Stale _)) -> ()
    | Error _ | Ok _ -> fail "open close session replay"
  end;
  let rejected = { success with Local.stop = Local.Reverted; closes = [auth] } in
  begin
    match Local.settle state [token] rejected with
    | Ok (same, [kept]) when Sess.current same kept -> ()
    | Ok _ | Error _ -> fail "open close session rejection"
  end;
  let state, second =
    match Sess.issue state ~kind:(Z.of_int 7) ~id:(Z.of_int 10) with
    | Ok value -> value
    | Error _ -> fail "open close session second"
  in
  begin
    match Local.grants state [token; second] with
    | Some [Vm.VCap left; Vm.VCap right]
        when String.equal left.scope right.scope
          && left.id = 9 && right.id = 10 -> ()
    | Some _ | None -> fail "open close session grants"
  end;
  if Option.is_some (Local.grants state [token; token]) then
    fail "open close duplicate tokens";
  begin
    match Local.settle state [token; token] success with
    | Error Local.Grant_repeat -> ()
    | Error _ | Ok _ -> fail "open close duplicate settlement"
  end;
  let absent = { auth with id = 11 } in
  let mixed = { success with Local.closes = [auth; absent] } in
  begin
    match Local.settle state [token; second] mixed with
    | Error (Local.Grant (kind, id, rev))
        when Z.equal kind (Z.of_int 7) && Z.equal id (Z.of_int 11)
          && Z.equal rev Z.zero -> ()
    | Error _ | Ok _ -> fail "open close session atomic"
  end;
  if not (Sess.current state token && Sess.current state second) then
    fail "open close session preserved"

let open_checks () =
  let int_artifact = compile "open int" open_int in
  let bool_artifact = compile "open bool" open_bool in
  let bytes_artifact = compile "open bytes" open_bytes in
  List.iter (wrapper_labels "scalar labels")
    [int_artifact; bool_artifact; bytes_artifact];
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
    match
      Aml_cli.open_match ~guarded:image.guarded ~entry:image.entry image.code Type.Int
        image.results values int_out
    with
    | Ok () -> ()
    | Error _ -> fail "open machine match"
  end;
  let changed_result =
    replace_first image.code
      (function Octb.Plus _ -> true | _ -> false)
      (Octb.Minus (0, 1, 2))
  in
  begin
    match
      Aml_cli.open_match ~guarded:image.guarded ~entry:image.entry changed_result Type.Int
        image.results values int_out
    with
    | Error _ -> ()
    | Ok () -> fail "open result mutation"
  end;
  let changed_cost = Array.append [|Octb.Noop|] image.code in
  begin
    match
      Aml_cli.open_match ~guarded:image.guarded ~entry:image.entry changed_cost Type.Int
        image.results values int_out
    with
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
  structural_checks ();
  range_checks ();
  close_checks ();
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