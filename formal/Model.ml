(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

module Type = Octra_vm.C_type
module Eval = Octra_vm.C_eval
module Fhe = Octra_vm.C_fhe
module Graph = Graph_model
module Native_graph = Octra_vm.C_graph
module Layout = Layout_model
module Otb = Otb_model
module Mach = Octra_vm.C_mach
module Octb = Octra_vm.C_octb
module Syn = Octra_vm.C_syn
module Hop = Hop_model
module Local = Octra_vm.Local_vm
module Vm = Octra_vm.Contract_vm

let fail name = failwith name

let nat name value =
  match Octra_vm.C_nat.of_int value with
  | Some value -> value
  | None -> fail name

let range () =
  for width = 0 to Type.max_bits + 1 do
    let bits = nat "range width" width in
    let model_bits = Z.of_int width in
    let expected = width >= 1 && width <= Type.max_bits in
    if Range_model.valid model_bits <> expected then fail "range model width";
    List.iter
      (fun (sign, model_sign) ->
        let typ = Type.Num (sign, bits) in
        if Type.valid typ <> expected then fail "range native width";
        match Type.range sign bits with
        | None when not expected -> ()
        | None -> fail "range limits"
        | Some _ when not expected -> fail "range invalid limits"
        | Some (low, high) ->
          if not (Z.equal low (Range_model.low model_sign model_bits))
              || not (Z.equal high (Range_model.high model_sign model_bits)) then
            fail "range model limits";
          List.iter
            (fun value ->
              let admitted = Type.admits typ value in
              if admitted <> Range_model.admits model_sign model_bits value then
                fail "range model admission";
              match Range_model.fit model_sign model_bits value with
              | Range_model.Inside found when admitted && Z.equal found value -> ()
              | Range_model.Outside found
                  when not admitted && Z.equal found value -> ()
              | Range_model.Inside _ | Range_model.Outside _ ->
                fail "range model fit")
            [Z.pred low; low; Z.zero; high; Z.succ high])
      [Type.Signed, Range_model.Signed;
        Type.Unsigned, Range_model.Unsigned]
  done

let seq () =
  for cap = 0 to 32 do
    let typ = Type.Seq (nat "sequence capacity" cap, Type.Int) in
    let model_cap = Z.of_int cap in
    for len = -1 to cap + 1 do
      let found = Seq_model.read_len model_cap (Z.of_int len) in
      if Option.is_some found <> (len >= 0 && len <= cap) then
        fail "sequence model length"
    done;
    for len = 0 to cap do
      let values = List.init len (fun index -> Z.of_int (index + 1)) in
      let count, packed = Seq_model.make model_cap Z.zero values in
      let value =
        Eval.Pair
          (Eval.Int count,
            Eval.Vec (Array.of_list (List.map (fun v -> Eval.Int v) packed)))
      in
      if not (Eval.typed typ value) then fail "sequence model type";
      if Seq_model.active (count, packed) <> values then
        fail "sequence model active";
      let sum = Seq_model.run Z.add (count, packed) Z.zero in
      if not (Z.equal sum (List.fold_left Z.add Z.zero values)) then
        fail "sequence model run";
      if len < cap then begin
        let changed = Array.of_list (List.map (fun v -> Eval.Int v) packed) in
        changed.(len) <- Eval.Int Z.one;
        let hidden = Eval.Pair (Eval.Int count, Eval.Vec changed) in
        if Eval.typed typ hidden then fail "sequence model tail"
      end
    done;
    let values = List.init (cap + 1) (fun index -> Z.of_int (index + 1)) in
    let count, packed = Seq_model.make model_cap Z.zero values in
    let value =
      Eval.Pair
        (Eval.Int count,
          Eval.Vec (Array.of_list (List.map (fun v -> Eval.Int v) packed)))
    in
    if Eval.typed typ value then fail "sequence model capacity"
  done

type hop_exp = {
  native : Fhe.t;
  proved : Hop.ftm;
}

type hop_spec = {
  key : int;
  rem : int;
}

type hop_ins =
  | Vload of int * Z.t * Z.t
  | Vnarrow of Z.t * Z.t * Z.t
  | Vadd of Z.t * Z.t
  | Vmul of Z.t * Z.t
  | Vrecrypt of Z.t * Z.t

type gen = {
  seed : int64;
}

let next state =
  { seed = Int64.add (Int64.mul state.seed 6364136223846793005L)
      1442695040888963407L }

let pick limit state =
  let state = next state in
  let value = Int64.logand state.seed Int64.max_int in
  Int64.to_int (Int64.rem value (Int64.of_int limit)), state

type layout_shape = {
  nshape : Mach.shape;
  pshape : Layout.shape;
}

let layout_unit = { nshape = Mach.SUnit; pshape = Layout.ShUnit }
let layout_atom = { nshape = Mach.SAtom; pshape = Layout.ShAtom }

let layout_cap kind = {
  nshape = Mach.SCap (nat "layout capability" kind);
  pshape = Layout.ShCap (Z.of_int kind);
}

let layout_pair left right = {
  nshape = Mach.SPair (left.nshape, right.nshape);
  pshape = Layout.ShPair (left.pshape, right.pshape);
}

let layout_vec len elem = {
  nshape = Mach.SVec (nat "layout vector" len, elem.nshape);
  pshape = Layout.ShVec (Z.of_int len, elem.pshape);
}

let layout_sum payload = {
  nshape = Mach.SSum payload.nshape;
  pshape = Layout.ShSum payload.pshape;
}

let layout_check first shape =
  let regs =
    Layout.shape_regs (Z.of_int first) shape.pshape
    |> List.map Z.to_int
  in
  let width = Z.to_int (Layout.shape_width shape.pshape) in
  if Mach.shape_width shape.nshape <> Z.of_int width then
    fail "layout width";
  match Octb.registers ~first shape.nshape with
  | Ok (found, next) when first + width <= 64 ->
    if found <> regs || next <> first + width then fail "layout registers";
    if next <= 61 && not (Octb.result_regs found) then
      fail "result layout"
  | Error Octb.Register when first + width > 64 -> ()
  | Ok _ | Error _ -> fail "layout capacity"

let result_regs_check values =
  let native = Octb.result_regs values in
  let proved = Layout.result_regs_b (List.map Z.of_int values) in
  if native <> proved then fail "result registers"

let label_value name native proved =
  if not (Z.equal (Z.of_int native) proved) then fail name

let label_count_check count =
  let native = Octb.label_count count in
  let proved = Layout.label_count_b (Z.of_int count) in
  if native <> proved then fail "label count"

let label_check (dispatch, input, side, data, guard, body) =
  label_value "dispatch label"
    (Octb.dispatch_label dispatch)
    (Layout.dispatch_label (Z.of_int dispatch));
  label_value "check label"
    (Octb.check_label input side)
    (Layout.check_label (Z.of_int input) (Z.of_int side));
  label_value "data label"
    (Octb.data_label data)
    (Layout.data_label (Z.of_int data));
  label_value "guard label"
    (Octb.guard_label guard)
    (Layout.guard_label (Z.of_int guard));
  label_value "body label"
    (Octb.body_label body)
    (Layout.body_label (Z.of_int body))

let body_target_check count target =
  let native = Octb.body_target count target in
  let proved =
    Layout.body_target (Z.of_int count) (Z.of_int target)
    |> Option.map Z.to_int
  in
  if native <> proved then fail "body target"

type label_zone = {
  native_label : int;
  proved_zone : Layout.label_zone;
}

let zone dispatch input side data guard body choice =
  match choice with
  | 0 -> {
      native_label = Octb.dispatch_label dispatch;
      proved_zone = Layout.ZDispatch (Z.of_int dispatch);
    }
  | 1 -> {
      native_label = Octb.check_label input side;
      proved_zone = Layout.ZCheck (Z.of_int input, Z.of_int side);
    }
  | 2 -> {
      native_label = Octb.data_label data;
      proved_zone = Layout.ZData (Z.of_int data);
    }
  | 3 -> {
      native_label = Octb.guard_label guard;
      proved_zone = Layout.ZGuard (Z.of_int guard);
    }
  | _ -> {
      native_label = Octb.body_label body;
      proved_zone = Layout.ZBody (Z.of_int body);
    }

let zone_check left right =
  if not (Layout.zone_b left.proved_zone)
      || not (Layout.zone_b right.proved_zone) then
    fail "label zone domain";
  let native = left.native_label = right.native_label in
  let proved =
    Z.equal
      (Layout.zone_value left.proved_zone)
      (Layout.zone_value right.proved_zone)
  in
  if native <> proved then fail "label zone identity"

let labels () =
  if Octb.label_limit <> Z.to_int Layout.label_limit then
    fail "label limit";
  if Octb.label_count (-1) then fail "negative label count";
  let counts = [0; 1; 999_999; 1_000_000; 1_000_001] in
  List.iter label_count_check counts;
  let direct = [
    0, 0, 0, 0, 0, 0;
    1, 59, 1, 999_999, 999_999, 1_048_575;
  ] in
  List.iter label_check direct;
  List.iter (fun (count, target) -> body_target_check count target) [
    0, Octb.body_label 0;
    1, Octb.body_label 0;
    1, Octb.body_label 1;
    2, Octb.body_label 1;
    1_048_576, Octb.body_label 1_048_575;
    1_048_576, Octb.body_label 1_048_576;
    1, Octb.body_label 0 - 1;
  ];
  if Octb.body_target (-1) (Octb.body_label 0) <> None
      || Octb.body_target 1 (-1) <> None then
    fail "negative body target";
  let exact = zone 1 59 1 999_999 999_999 1_048_575 4 in
  zone_check exact exact;
  List.iter
    (fun choice ->
      zone_check
        (zone 0 0 0 0 0 0 choice)
        (zone 1 59 1 999_999 999_999 1_048_575 ((choice + 1) mod 5)))
    [0; 1; 2; 3; 4];
  let rec walk index state =
    if index = 10_000 then ()
    else
      let dispatch, state = pick 2 state in
      let input, state = pick 60 state in
      let side, state = pick 2 state in
      let data, state = pick 1_000_000 state in
      let guard, state = pick 1_000_000 state in
      let body, state = pick 1_048_576 state in
      label_check (dispatch, input, side, data, guard, body);
      let count, state = pick 1_048_577 state in
      let target, state = pick 1_048_578 state in
      body_target_check count (Octb.body_label 0 + target - 1);
      let left_choice, state = pick 5 state in
      let right_choice, state = pick 5 state in
      let left = zone dispatch input side data guard body left_choice in
      let dispatch, state = pick 2 state in
      let input, state = pick 60 state in
      let side, state = pick 2 state in
      let data, state = pick 1_000_000 state in
      let guard, state = pick 1_000_000 state in
      let body, state = pick 1_048_576 state in
      let right = zone dispatch input side data guard body right_choice in
      zone_check left right;
      walk (index + 1) state
  in
  walk 0 { seed = 0x4c4142454c5a4f4eL };
  List.length counts + List.length direct + 20_016

let rec layout_gen depth state =
  let choices = if depth = 0 then 3 else 6 in
  let choice, state = pick choices state in
  match choice with
  | 0 -> layout_unit, state
  | 1 -> layout_atom, state
  | 2 ->
    let kind, state = pick 8 state in
    layout_cap kind, state
  | 3 ->
    let left, state = layout_gen (depth - 1) state in
    let right, state = layout_gen (depth - 1) state in
    layout_pair left right, state
  | 4 ->
    let len, state = pick 8 state in
    let elem, state = layout_gen (depth - 1) state in
    layout_vec len elem, state
  | _ ->
    let payload, state = layout_gen (depth - 1) state in
    layout_sum payload, state

let layout () =
  let direct = [
    layout_unit;
    layout_atom;
    layout_cap 7;
    layout_pair layout_atom layout_unit;
    layout_vec 60 layout_atom;
    layout_vec 61 layout_atom;
    layout_sum (layout_pair layout_atom layout_atom);
  ] in
  List.iter (layout_check 1) direct;
  layout_check 63 layout_atom;
  layout_check 64 layout_atom;
  begin
    match Octb.registers ~first:(-1) Mach.SAtom with
    | Error Octb.Register -> ()
    | Ok _ | Error _ -> fail "layout negative register"
  end;
  List.iter result_regs_check
    [[]; [0]; [60]; [61]; [0; 60]; [60; 60]; [61; 0]];
  if Octb.result_regs [-1] then fail "negative result register";
  let rec walk index state =
    if index = 10_000 then ()
    else
      let shape, state = layout_gen 5 state in
      let first, state = pick 64 state in
      layout_check (first + 1) shape;
      walk (index + 1) state
  in
  walk 0 { seed = 0x4c41594f55545245L };
  let rec results index state =
    if index = 10_000 then ()
    else
      let len, state = pick 66 state in
      let rec values left state out =
        if left = 0 then List.rev out, state
        else
          let value, state = pick 66 state in
          values (left - 1) state (value :: out)
      in
      let values, state = values len state [] in
      result_regs_check values;
      results (index + 1) state
  in
  results 0 { seed = 0x524553554c545245L };
  List.length direct + 11 + 20_000

let rec otb_type = function
  | Type.Unit -> Otb.OUnit
  | Type.Bool -> Otb.OBool
  | Type.Int -> Otb.OInt
  | Type.Num (sign, width) ->
    Otb.ONum (sign = Type.Signed, Octra_vm.C_nat.to_z width)
  | Type.Bytes len -> Otb.OBytes (Octra_vm.C_nat.to_z len)
  | Type.Vec (len, elem) ->
    Otb.OVec (Octra_vm.C_nat.to_z len, otb_type elem)
  | Type.Seq (cap, elem) ->
    Otb.OSeq (Octra_vm.C_nat.to_z cap, otb_type elem)
  | Type.Cap kind -> Otb.OCap (Octra_vm.C_nat.to_z kind)
  | Type.Enc (key, rem) ->
    Otb.OEnc (Octra_vm.C_nat.to_z key, Octra_vm.C_nat.to_z rem)
  | Type.Pair (first, second) ->
    Otb.OPair (otb_type first, otb_type second)
  | Type.Sum (first, second) ->
    Otb.OSum (otb_type first, otb_type second)

let rec otb_shape = function
  | Mach.SUnit -> Otb.ShUnit
  | Mach.SAtom -> Otb.ShAtom
  | Mach.SCap kind -> Otb.ShCap (Octra_vm.C_nat.to_z kind)
  | Mach.SPair (first, second) ->
    Otb.ShPair (otb_shape first, otb_shape second)
  | Mach.SVec (len, elem) ->
    Otb.ShVec (Octra_vm.C_nat.to_z len, otb_shape elem)
  | Mach.SSum payload -> Otb.ShSum (otb_shape payload)

let otb_shape_check typ =
  match Mach.shape_of typ, Otb.otype_shape (otb_type typ) with
  | Some native, Some proved ->
    if otb_shape native <> proved then fail "open shape";
    if not (Z.equal (Mach.shape_width native) (Otb.shape_width proved)) then
      fail "open shape width";
    if not (Z.equal (Mach.shape_cells native) (Otb.shape_cells proved)) then
      fail "open shape cells"
  | None, None -> ()
  | Some _, None | None, Some _ -> fail "open shape admission"

let rec otb_type_gen depth state =
  let limit = if depth = 0 then 8 else 12 in
  let choice, state = pick limit state in
  match choice with
  | 0 -> Type.Unit, state
  | 1 -> Type.Bool, state
  | 2 -> Type.Int, state
  | 3 ->
    let sign, state = pick 2 state in
    let width, state = pick Type.max_bits state in
    let sign = if sign = 0 then Type.Signed else Type.Unsigned in
    Type.Num (sign, nat "open shape width" (width + 1)), state
  | 4 ->
    let len, state = pick 17 state in
    Type.Bytes (nat "open shape bytes" len), state
  | 5 ->
    let kind, state = pick 17 state in
    Type.Cap (nat "open shape capability" kind), state
  | 6 ->
    let key, state = pick 17 state in
    let rem, state = pick 17 state in
    Type.Enc
      (nat "open shape key" key, nat "open shape depth" rem), state
  | 7 -> Type.Seq (nat "open shape sequence" 4, Type.Int), state
  | 8 ->
    let len, state = pick 9 state in
    let elem, state = otb_type_gen (depth - 1) state in
    Type.Vec (nat "open shape vector" len, elem), state
  | 9 ->
    let cap, state = pick 9 state in
    Type.Seq (nat "open shape sequence" cap, Type.Int), state
  | 10 ->
    let first, state = otb_type_gen (depth - 1) state in
    let second, state = otb_type_gen (depth - 1) state in
    Type.Pair (first, second), state
  | _ ->
    let first, state = otb_type_gen (depth - 1) state in
    let same, state = pick 2 state in
    if same = 0 then Type.Sum (first, first), state
    else
      let second, state = otb_type_gen (depth - 1) state in
      Type.Sum (first, second), state

let rec native_input_layout = function
  | [] -> Some (Z.zero, Z.zero)
  | typ :: rest ->
    begin
      match Mach.shape_of typ, native_input_layout rest with
      | Some form, Some (width, cells) ->
        Some
          (Z.add (Mach.shape_width form) width,
            Z.add (Mach.shape_cells form) cells)
      | Some _, None | None, Some _ | None, None -> None
    end

let native_layout_b inputs output results =
  match native_input_layout inputs, Mach.shape_of output with
  | Some (width, cells), Some form ->
    Z.leq width (Z.of_int 60)
      && Z.leq (Z.add cells (Mach.shape_cells form)) (Z.of_int 4096)
      && Z.equal (Mach.shape_width form) (Z.of_int (List.length results))
  | Some _, None | None, Some _ | None, None -> false

let otb_layout_check inputs output results =
  let types = List.map otb_type inputs in
  let proved = Otb.input_layout types in
  let native = native_input_layout inputs in
  if native <> proved then fail "open input layout";
  let accepted = native_layout_b inputs output results in
  if accepted <> Otb.layout_b types (otb_type output) (List.map Z.of_int results)
  then fail "open layout admission"

let native_frame_bits inputs output results =
  let reg value =
    Option.bind
      (Octra_vm.C_nat.of_int value)
      Octra_vm.C_bin.num
  in
  Option.bind
    (Octra_vm.C_bin.list_code Octra_vm.C_bin.ty_code inputs)
    (fun input_codes ->
      Option.bind
        (Octra_vm.C_bin.ty_code output)
        (fun output_code ->
          Option.bind
            (Octra_vm.C_bin.list_code reg results)
            (fun result_codes ->
              Octra_vm.C_bin.enc_code
                (Octra_vm.C_bin.Tag
                  (Z.zero,
                    Octra_vm.C_bin.Cons
                      (input_codes,
                        Octra_vm.C_bin.Cons
                          (output_code,
                            Octra_vm.C_bin.Cons
                              (result_codes, Octra_vm.C_bin.Nil))))))))

let otb_bits raw =
  let rec walk index out =
    if index = String.length raw then List.rev out
    else
      match raw.[index] with
      | '0' -> walk (index + 1) (false :: out)
      | '1' -> walk (index + 1) (true :: out)
      | _ -> fail "open frame bit"
  in
  walk 0 []

let otb_prefix = "\000OCTRA_AML_OPEN\000"

let otb_header_op = function
  | Octra_vm.Contract_vm.JDEST label -> Otb.HMark (Z.of_int label)
  | Octra_vm.Contract_vm.MLOAD (reg, at) ->
    Otb.HMem (Z.of_int reg, Z.of_int at)
  | Octra_vm.Contract_vm.LDI (reg, Octra_vm.Contract_vm.VString value)
      when String.equal value "main" -> Otb.HMain (Z.of_int reg)
  | Octra_vm.Contract_vm.LDI (reg, Octra_vm.Contract_vm.VString value)
      when String.length value > String.length otb_prefix
        && String.equal
          (String.sub value 0 (String.length otb_prefix)) otb_prefix ->
    Otb.HFrame
      (Z.of_int reg,
        otb_bits
          (String.sub value (String.length otb_prefix)
            (String.length value - String.length otb_prefix)))
  | Octra_vm.Contract_vm.EQ (out, left, right) ->
    Otb.HEqual (Z.of_int out, Z.of_int left, Z.of_int right)
  | Octra_vm.Contract_vm.JIF (reg, label) ->
    Otb.HJump (Z.of_int reg, Z.of_int label)
  | Octra_vm.Contract_vm.REVERT -> Otb.HRefuse
  | _ -> fail "open header opcode"

let otb_header artifact =
  match Octra_vm.Bytecode.decode_image artifact.Octb.octb with
  | Ok image when Array.length image.code >= 8 ->
    let native = Array.sub image.code 0 8 |> Array.to_list in
    native, List.map otb_header_op native
  | Ok _ | Error _ -> fail "open header image"

let otb_args artifact count =
  match Octra_vm.Bytecode.decode_image artifact.Octb.octb with
  | Ok image when Array.length image.code >= 8 + count ->
    let native = Array.sub image.code 8 count |> Array.to_list in
    native, List.map otb_header_op native
  | Ok _ | Error _ -> fail "open argument image"

let otb_stype = function
  | Type.Int -> Otb.XInt
  | Type.Bool -> Otb.XBool
  | Type.Bytes len -> Otb.XBytes (Octra_vm.C_nat.to_z len)
  | Type.Unit | Type.Num _ | Type.Vec _ | Type.Seq _ | Type.Cap _
  | Type.Enc _ | Type.Pair _ | Type.Sum _ -> fail "scalar type"

let otb_vm_xop = function
  | Octra_vm.Contract_vm.MLOAD (reg, at) ->
    Otb.XMem (Z.of_int reg, Z.of_int at)
  | Octra_vm.Contract_vm.LDI (reg, Octra_vm.Contract_vm.VInt value)
      when Z.sign value >= 0 ->
    Otb.XNum (Z.of_int reg, value)
  | Octra_vm.Contract_vm.LDI (reg, Octra_vm.Contract_vm.VBytes value)
      when String.equal value "" ->
    Otb.XEmpty (Z.of_int reg)
  | Octra_vm.Contract_vm.SUB (dst, left, right) ->
    Otb.XSub (Z.of_int dst, Z.of_int left, Z.of_int right)
  | Octra_vm.Contract_vm.JIF (reg, label) ->
    Otb.XIf (Z.of_int reg, Z.of_int label)
  | Octra_vm.Contract_vm.NOP -> Otb.XNoop
  | Octra_vm.Contract_vm.JMP label -> Otb.XJump (Z.of_int label)
  | Octra_vm.Contract_vm.JDEST label -> Otb.XMark (Z.of_int label)
  | Octra_vm.Contract_vm.EQ (dst, left, right) ->
    Otb.XEq (Z.of_int dst, Z.of_int left, Z.of_int right)
  | Octra_vm.Contract_vm.STRLEN (dst, source) ->
    Otb.XSize (Z.of_int dst, Z.of_int source)
  | Octra_vm.Contract_vm.REVERT -> Otb.XRefuse
  | Octra_vm.Contract_vm.SUBSTR (dst, source, first, count) ->
    Otb.XSlice
      (Z.of_int dst, Z.of_int source, Z.of_int first, Z.of_int count)
  | Octra_vm.Contract_vm.STOP -> Otb.XStop
  | Octra_vm.Contract_vm.DIV (dst, left, right) ->
    Otb.XDiv (Z.of_int dst, Z.of_int left, Z.of_int right)
  | _ -> fail "scalar VM opcode"

let otb_local_xop = function
  | Octb.Load (reg, Octra_vm.C_emit.Int value) when Z.sign value >= 0 ->
    Otb.XNum (Z.of_int reg, value)
  | Octb.Load (reg, Octra_vm.C_emit.Bytes value)
      when String.equal value "" ->
    Otb.XEmpty (Z.of_int reg)
  | Octb.Minus (dst, left, right) ->
    Otb.XSub (Z.of_int dst, Z.of_int left, Z.of_int right)
  | Octb.Jump_if (reg, label) ->
    Otb.XIf (Z.of_int reg, Z.of_int label)
  | Octb.Noop -> Otb.XNoop
  | Octb.Jump label -> Otb.XJump (Z.of_int label)
  | Octb.Mark label -> Otb.XMark (Z.of_int label)
  | Octb.Same (dst, left, right) ->
    Otb.XEq (Z.of_int dst, Z.of_int left, Z.of_int right)
  | Octb.Size (dst, source) ->
    Otb.XSize (Z.of_int dst, Z.of_int source)
  | Octb.Slice (dst, source, first, count) ->
    Otb.XSlice
      (Z.of_int dst, Z.of_int source, Z.of_int first, Z.of_int count)
  | Octb.Stop -> Otb.XStop
  | Octb.Quotient (dst, left, right) ->
    Otb.XDiv (Z.of_int dst, Z.of_int left, Z.of_int right)
  | Octb.Load _ | Octb.Move _ | Octb.Plus _ | Octb.Times _
  | Octb.Remainder _ | Octb.Negate _ | Octb.Absolute _ | Octb.Different _
  | Octb.Less _ | Octb.Greater _ | Octb.Join _ | Octb.Cap_close _ ->
    fail "scalar local opcode"

let list_set at value values =
  List.mapi (fun index item -> if index = at then value else item) values

let array_set at value values =
  let changed = Array.copy values in
  changed.(at) <- value;
  changed

let otb_local_vm = function
  | Octb.Load (reg, Octra_vm.C_emit.Int value) ->
    Octra_vm.Contract_vm.LDI (reg, Octra_vm.Contract_vm.VInt value)
  | Octb.Load (reg, Octra_vm.C_emit.Bytes value) ->
    Octra_vm.Contract_vm.LDI (reg, Octra_vm.Contract_vm.VBytes value)
  | Octb.Minus (dst, left, right) ->
    Octra_vm.Contract_vm.SUB (dst, left, right)
  | Octb.Jump_if (reg, label) -> Octra_vm.Contract_vm.JIF (reg, label)
  | Octb.Noop -> Octra_vm.Contract_vm.NOP
  | Octb.Jump label -> Octra_vm.Contract_vm.JMP label
  | Octb.Mark label -> Octra_vm.Contract_vm.JDEST label
  | Octb.Same (dst, left, right) ->
    Octra_vm.Contract_vm.EQ (dst, left, right)
  | Octb.Size (dst, source) -> Octra_vm.Contract_vm.STRLEN (dst, source)
  | Octb.Slice (dst, source, first, count) ->
    Octra_vm.Contract_vm.SUBSTR (dst, source, first, count)
  | Octb.Stop -> Octra_vm.Contract_vm.STOP
  | Octb.Quotient (dst, left, right) ->
    Octra_vm.Contract_vm.DIV (dst, left, right)
  | Octb.Load _ | Octb.Move _ | Octb.Plus _ | Octb.Times _
  | Octb.Remainder _ | Octb.Negate _ | Octb.Absolute _ | Octb.Different _
  | Octb.Less _ | Octb.Greater _ | Octb.Join _ | Octb.Cap_close _ ->
    fail "scalar local cost"

let otb_bytes value =
  List.init (String.length value)
    (fun index -> Z.of_int (Char.code value.[index]))

let otb_xvalue = function
  | Vm.VInt value -> Otb.XvInt value
  | Vm.VBool value -> Otb.XvBool value
  | Vm.VBytes value -> Otb.XvBytes (otb_bytes value)
  | _ -> fail "scalar VM value"

let otb_vm_value typ index =
  match typ with
  | Type.Int -> Vm.VInt (Z.of_int (index - 30))
  | Type.Bool -> Vm.VBool (index mod 2 = 0)
  | Type.Bytes len ->
    let size = Octra_vm.C_nat.to_int len in
    Vm.VBytes
      (String.init size (fun at -> Char.chr ((index + at) land 255)))
  | Type.Unit | Type.Num _ | Type.Vec _ | Type.Seq _ | Type.Cap _
  | Type.Enc _ | Type.Pair _ | Type.Sum _ -> fail "scalar input value"

let otb_wrong_value = function
  | Type.Int | Type.Bytes _ -> Vm.VBool true
  | Type.Bool -> Vm.VInt Z.one
  | Type.Unit | Type.Num _ | Type.Vec _ | Type.Seq _ | Type.Cap _
  | Type.Enc _ | Type.Pair _ | Type.Sum _ -> fail "scalar wrong value"

let otb_run native args =
  let config =
    Local.config
      ~view:true
      ~byte_result:Vm.Bytes_result
      ~method_name:"main"
      ~args
      ~strict_values:true
      ()
  in
  match Local.run ~trace:true config native.Octra_vm.Bytecode.code with
  | Ok outcome -> outcome
  | Error error -> fail (Local.error_text error)

let otb_effort outcome first last =
  List.fold_left
    (fun total (frame : Local.frame) ->
      if frame.pc >= first && frame.pc < last then
        total + frame.effort_after - frame.effort_before
      else total)
    0 outcome.Local.frames

let otb_returned name outcome =
  match outcome.Local.stop with
  | Local.Returned -> ()
  | Local.Reverted | Local.Step_cap | Local.Host_operation _ -> fail name

let otb_refused name outcome =
  match outcome.Local.stop with
  | Local.Reverted -> ()
  | Local.Returned | Local.Step_cap | Local.Host_operation _ -> fail name

let otb_refuse native code =
  let raw =
    Octra_vm.Bytecode.encode ?state:native.Octra_vm.Bytecode.state
      ?proof:native.proof ?emission:native.emission ?veil:native.veil code
  in
  match Octb.decode raw with
  | Error _ -> ()
  | Ok _ -> fail "scalar mutation accepted"

let otb_scalar_artifact typ =
  let inputs =
    List.init 60
      (fun index ->
        Printf.sprintf "input many x%d: %s" index (Type.text typ))
    |> String.concat " "
  in
  let source = "program Scalar { " ^ inputs ^ " term x0 }" in
  let artifact =
    match Octb.compile source with
    | Ok value -> value
    | Error error -> fail (Octb.text error)
  in
  let native =
    match Octra_vm.Bytecode.decode_image artifact.Octb.octb with
    | Ok image -> image
    | Error _ -> fail "scalar artifact image"
  in
  match Octb.decode artifact.Octb.octb with
  | Ok image
      when Array.length image.inputs = 60
        && Array.for_all (Type.equal typ) image.inputs
        && Option.fold ~none:false ~some:(Type.equal typ) image.output ->
    native, image
  | Ok _ | Error _ -> fail "scalar artifact type"

let otb_scalar () =
  let eight = nat "scalar bytes" 8 in
  let types = [
    Type.Int;
    Type.Bool;
    Type.Bytes (nat "scalar empty bytes" 0);
    Type.Bytes (nat "scalar one byte" 1);
    Type.Bytes eight;
    Type.Bytes (nat "scalar page bytes" 4096);
  ] in
  let input_cases = ref 0 in
  let output_cases = ref 0 in
  let mutations = ref 0 in
  let run_cases = ref 0 in
  List.iter
    (fun typ ->
      let native, image = otb_scalar_artifact typ in
      let scalar = otb_stype typ in
      let args = List.init 60 (otb_vm_value typ) in
      let outcome = otb_run native args in
      otb_returned "scalar runtime" outcome;
      let pc = ref 7 in
      for index = 0 to 59 do
        let scalar = otb_stype typ in
        let model_index = Z.of_int index in
        let expected = Otb.in_code model_index scalar in
        let count = List.length expected in
        if !pc + count >= Array.length native.code then
          fail "scalar artifact length";
        let native_input = Array.sub native.code !pc count in
        let proved = Array.to_list native_input |> List.map otb_vm_xop in
        if expected <> proved then fail "scalar input code";
        begin
          match Otb.in_read model_index proved with
          | Some found when found = scalar -> ()
          | Some _ | None -> fail "scalar input read"
        end;
        let native_cost =
          Array.fold_left
            (fun total op -> total + Octra_vm.Contract_vm.effort_cost op)
            0 native_input
        in
        if not
            (Z.equal (Otb.xops_cost proved) (Z.of_int native_cost)
              && Z.equal (Otb.in_cost scalar) (Z.of_int native_cost)) then
          fail "scalar input cost";
        if not (Otb.xregs_b proved) then fail "scalar input register";
        let value = otb_xvalue (List.nth args index) in
        let effort = otb_effort outcome !pc (!pc + count) in
        begin
          match Otb.in_turn model_index proved value with
          | Some (found, cost)
              when found = value && Z.equal cost (Z.of_int effort) -> ()
          | Some (_, cost) ->
            fail
              (Printf.sprintf
                "scalar input runtime type = %s index = %d model = %s observed = %d"
                (Type.text typ) index (Z.to_string cost) effort)
          | None ->
            fail
              (Printf.sprintf "scalar input runtime type = %s index = %d model = none"
                (Type.text typ) index)
        end;
        incr run_cases;
        Array.iteri
          (fun at _ ->
            let changed_input =
              array_set at Octra_vm.Contract_vm.STOP native_input
            in
            let changed = Array.to_list changed_input |> List.map otb_vm_xop in
            if Option.is_some (Otb.in_read model_index changed) then
              fail "scalar input mutation";
            let changed_code =
              array_set (!pc + at) Octra_vm.Contract_vm.STOP native.code
            in
            otb_refuse native changed_code;
            incr mutations)
          native_input;
        pc := !pc + count;
        incr input_cases
      done;
      if native.code.(!pc) <> Octra_vm.Contract_vm.NOP then
        fail "scalar artifact body";
      let tail_count = List.length (Otb.out_code Z.zero scalar) in
      let first = Array.length image.code - tail_count in
      if first < 0 then fail "scalar output length";
      let tail = Array.sub image.code first tail_count in
      let proved = Array.to_list tail |> List.map otb_local_xop in
      let model_first = Z.of_int first in
      if Otb.out_code model_first scalar <> proved then
        fail "scalar native output code";
      begin
        match Otb.out_read model_first proved with
        | Some found when found = scalar -> ()
        | Some _ | None -> fail "scalar native output read"
      end;
      let native_cost =
        Array.fold_left
          (fun total op ->
            total + Octra_vm.Contract_vm.effort_cost (otb_local_vm op))
          0 tail
      in
      if not
          (Z.equal (Otb.xops_cost proved) (Z.of_int native_cost)
            && Z.equal (Otb.out_cost scalar) (Z.of_int native_cost)) then
        fail "scalar native output cost";
      let value = otb_xvalue outcome.Local.result in
      let absolute = image.entry + first in
      let effort = otb_effort outcome absolute (Array.length native.code) in
      begin
        match Otb.out_turn model_first proved value with
        | Some (found, cost)
            when found = value && Z.equal cost (Z.of_int effort) -> ()
        | Some _ | None -> fail "scalar output runtime"
      end;
      incr run_cases;
      Array.iteri
        (fun at op ->
          let changed_op = if op = Octb.Noop then Octb.Stop else Octb.Noop in
          let changed_tail = array_set at changed_op tail in
          let changed = Array.to_list changed_tail |> List.map otb_local_xop in
          if Option.is_some (Otb.out_read model_first changed) then
            fail "scalar native output mutation";
          let native_op =
            if op = Octb.Noop then Octra_vm.Contract_vm.STOP
            else Octra_vm.Contract_vm.NOP
          in
          let changed_code =
            array_set (image.entry + first + at) native_op native.code
          in
          otb_refuse native changed_code;
          incr mutations)
        tail;
      let wrong = otb_wrong_value typ in
      let wrong_args = wrong :: List.tl args in
      let wrong_value = otb_xvalue wrong in
      if Option.is_some
          (Otb.in_turn Z.zero (Otb.in_code Z.zero scalar) wrong_value) then
        fail "scalar input type model";
      otb_refused "scalar input type runtime" (otb_run native wrong_args);
      incr run_cases;
      begin
        match typ with
        | Type.Bytes len ->
          let size = Octra_vm.C_nat.to_int len in
          let changed_size = if size = 0 then 1 else size - 1 in
          let changed = Vm.VBytes (String.make changed_size '\000') in
          let changed_value = otb_xvalue changed in
          if Option.is_some
              (Otb.in_turn Z.zero (Otb.in_code Z.zero scalar) changed_value)
          then fail "scalar input length model";
          otb_refused "scalar input length runtime"
            (otb_run native (changed :: List.tl args));
          incr run_cases
        | Type.Int | Type.Bool -> ()
        | Type.Unit | Type.Num _ | Type.Vec _ | Type.Seq _ | Type.Cap _
        | Type.Enc _ | Type.Pair _ | Type.Sum _ -> fail "scalar runtime type"
      end;
      let changed = Array.copy native.code in
      changed.(absolute - 1) <-
        begin
          match typ with
          | Type.Int | Type.Bytes _ -> Vm.LDI (0, Vm.VBool true)
          | Type.Bool -> Vm.LDI (0, Vm.VInt Z.one)
          | Type.Unit | Type.Num _ | Type.Vec _ | Type.Seq _ | Type.Cap _
          | Type.Enc _ | Type.Pair _ | Type.Sum _ -> fail "scalar output type"
        end;
      let config =
        Local.config
          ~view:true
          ~byte_result:Vm.Bytes_result
          ~method_name:"main"
          ~args
          ~strict_values:true
          ()
      in
      let changed_outcome =
        match Local.run ~trace:true config changed with
        | Ok value -> value
        | Error error -> fail (Local.error_text error)
      in
      otb_refused "scalar output type runtime" changed_outcome;
      incr run_cases)
    types;
  for first = 0 to 31 do
    List.iter
      (fun typ ->
        let scalar = otb_stype typ in
        let model_first = Z.of_int first in
        let proved = Otb.out_code model_first scalar in
        begin
          match Otb.out_read model_first proved with
          | Some found when found = scalar -> ()
          | Some _ | None -> fail "scalar output read"
        end;
        if not (Z.equal (Otb.xops_cost proved) (Otb.out_cost scalar)) then
          fail "scalar output cost";
        if not (Otb.xregs_b proved) then fail "scalar output register";
        List.iteri
          (fun at op ->
            let changed_op = if op = Otb.XNoop then Otb.XStop else Otb.XNoop in
            let changed = list_set at changed_op proved in
            if Option.is_some (Otb.out_read model_first changed) then
              fail "scalar output mutation";
            incr mutations)
          proved;
        incr output_cases)
      types
  done;
  !input_cases, !output_cases, !mutations, List.length types, !run_cases

let otb_schema artifact =
  let image =
    match Octb.decode artifact.Octb.octb with
    | Ok value -> value
    | Error error -> fail (Octb.decode_text error)
  in
  let rec find index =
    if index = Array.length image.consts then fail "open frame absent"
    else
      match image.consts.(index).value with
      | Octb.CText raw
          when String.length raw > String.length otb_prefix
            && String.equal
              (String.sub raw 0 (String.length otb_prefix)) otb_prefix ->
        otb_bits
          (String.sub raw (String.length otb_prefix)
            (String.length raw - String.length otb_prefix))
      | Octb.CInt _ | Octb.CBool _ | Octb.CText _ | Octb.CData _
      | Octb.CBytes _ -> find (index + 1)
  in
  image, find 0

let otb_frame () =
  let eight = nat "open frame eight" 8 in
  let sixteen = nat "open frame sixteen" 16 in
  let type_cases =
    [Type.Unit;
      Type.Bool;
      Type.Int;
      Type.Num (Type.Signed, eight);
      Type.Num (Type.Unsigned, sixteen);
      Type.Bytes eight;
      Type.Vec (eight, Type.Int);
      Type.Seq (eight, Type.Num (Type.Unsigned, sixteen));
      Type.Cap eight;
      Type.Enc (eight, sixteen);
      Type.Pair (Type.Int, Type.Bool);
      Type.Sum (Type.Bytes eight, Type.Unit)]
  in
  let shape_cases =
    type_cases
    @ [Type.Sum (Type.Int, Type.Bool);
        Type.Pair
          (Type.Seq (eight, Type.Int), Type.Vec (sixteen, Type.Bool))]
  in
  List.iter otb_shape_check shape_cases;
  let type_output = Type.Pair (Type.Int, Type.Bool) in
  let type_results = [0; 1] in
  let proved_types = List.map otb_type type_cases in
  let proved_output = otb_type type_output in
  let proved_bits = Otb.frame_bits proved_types proved_output [Z.zero; Z.one] in
  begin
    match native_frame_bits type_cases type_output type_results with
    | Some native_bits when native_bits = proved_bits -> ()
    | Some _ | None -> fail "open frame type code"
  end;
  if not (Otb.frame_b proved_types proved_output [Z.zero; Z.one]) then
    fail "open frame type set";
  let source =
    "program Frame { input many xs: vec[2, int] term xs }"
  in
  let artifact =
    match Octb.compile source with
    | Ok value -> value
    | Error error -> fail (Octb.text error)
  in
  let image, bits = otb_schema artifact in
  let native_header, proved_header = otb_header artifact in
  let native_args, proved_args = otb_args artifact 2 in
  let inputs = Array.to_list image.inputs |> List.map otb_type in
  let output =
    match image.output with
    | Some value -> otb_type value
    | None -> fail "open frame output"
  in
  let results = Array.to_list image.results |> List.map Z.of_int in
  if Otb.frame_bits inputs output results <> bits then
    fail "open frame bits";
  begin
    match Otb.frame_read bits with
    | Some ((found_inputs, found_output), found_results)
        when found_inputs = inputs && found_output = output
          && found_results = results -> ()
    | Some _ | None -> fail "open frame read"
  end;
  begin
    match Otb.layout_read bits with
    | Some ((found_inputs, found_output), found_results)
        when found_inputs = inputs && found_output = output
          && found_results = results -> ()
    | Some _ | None -> fail "open layout read"
  end;
  if Option.is_some (Otb.frame_read (bits @ [false])) then
    fail "open frame suffix";
  if Otb.frame_b [] output results
      || Otb.frame_b inputs output [Z.of_int 61]
      || Otb.frame_b inputs output [Z.zero; Z.zero]
      || Otb.frame_b inputs (Otb.ONum (true, Z.zero)) results
      || Otb.frame_b inputs (Otb.OSeq (Z.one, Otb.OCap Z.one)) results then
    fail "open frame admission";
  if Otb.header bits <> proved_header then fail "open header code";
  begin
    match Otb.header_read proved_header with
    | Some ((found_inputs, found_output), found_results)
        when found_inputs = inputs && found_output = output
          && found_results = results -> ()
    | Some _ | None -> fail "open header read"
  end;
  let native_cost =
    List.fold_left
      (fun total op -> total + Octra_vm.Contract_vm.effort_cost op)
      0 native_header
  in
  if not (Z.equal (Otb.header_cost proved_header) (Z.of_int native_cost)) then
    fail "open header cost";
  let changed_header =
    List.mapi
      (fun index op ->
        if index = 1 then Otb.HMem (Z.of_int 60, Z.of_int 1000) else op)
      proved_header
  in
  if Option.is_some (Otb.header_read changed_header) then
    fail "open header mutation";
  if Otb.arg_code Z.zero (Z.of_int 2) <> proved_args then
    fail "open argument code";
  begin
    match Otb.arg_read Z.zero proved_args with
    | Some count when Z.equal count (Z.of_int 2) -> ()
    | Some _ | None -> fail "open argument read"
  end;
  let native_arg_cost =
    List.fold_left
      (fun total op -> total + Octra_vm.Contract_vm.effort_cost op)
      0 native_args
  in
  if not
      (Z.equal (Otb.header_cost proved_args) (Z.of_int native_arg_cost)) then
    fail "open argument cost";
  let changed_arg_reg =
    match proved_args with
    | _ :: rest -> Otb.HMem (Z.of_int 2, Z.of_int 1001) :: rest
    | [] -> fail "open argument absent"
  in
  if Option.is_some (Otb.arg_read Z.zero changed_arg_reg) then
    fail "open argument register mutation";
  let changed_arg_addr =
    match proved_args with
    | _ :: rest -> Otb.HMem (Z.one, Z.of_int 1002) :: rest
    | [] -> fail "open argument absent"
  in
  if Option.is_some (Otb.arg_read Z.zero changed_arg_addr) then
    fail "open argument address mutation";
  let direct_layouts = [
    [Type.Vec (nat "open layout input" 2, Type.Int)],
      Type.Vec (nat "open layout output" 2, Type.Int), [0; 1];
    [Type.Vec (nat "open layout width" 61, Type.Int)], Type.Int, [0];
    [Type.Vec (nat "open layout cells" 4096, Type.Unit)], Type.Unit, [];
    [Type.Enc (eight, sixteen)], Type.Int, [0];
    [Type.Int], Type.Pair (Type.Int, Type.Bool), [0];
  ] in
  List.iter (fun (types, typ, regs) -> otb_layout_check types typ regs)
    direct_layouts;
  let rec layouts index state =
    if index = 10_000 then ()
    else
      let count, state = pick 5 state in
      let rec types left state out =
        if left = 0 then List.rev out, state
        else
          let typ, state = otb_type_gen 3 state in
          types (left - 1) state (typ :: out)
      in
      let input_types, state = types count state [] in
      let output_type, state = otb_type_gen 3 state in
      let result_count, state = pick 63 state in
      let result_regs = List.init result_count Fun.id in
      List.iter otb_shape_check (output_type :: input_types);
      otb_layout_check input_types output_type result_regs;
      layouts (index + 1) state
  in
  layouts 0 { seed = 0x4f50454e4c41594fL };
  List.length type_cases + 8, 4, 5,
    List.length shape_cases + List.length direct_layouts + 10_000

let graph_base id =
  let tag = nat "graph base tag" id in
  Native_graph.base ~tag,
  { Graph.ltag = Z.of_int id; lrule = Graph.Base }

let graph_prod id left right =
  let tag = nat "graph product tag" id in
  let left_id = nat "graph product left" left in
  let right_id = nat "graph product right" right in
  Native_graph.prod ~tag ~left:left_id ~right:right_id,
  { Graph.ltag = Z.of_int id;
    lrule = Graph.Prod (Z.of_int left, Z.of_int right) }

let graph_rules id =
  let products =
    List.init id Fun.id
    |> List.concat_map (fun left ->
         List.init id (fun right -> graph_prod id left right))
  in
  graph_base id :: products

let graph_depth native proved =
  let native_depth =
    match Native_graph.mul_depth (Native_graph.graph native []) with
    | Ok depth -> Octra_vm.C_nat.to_z depth
    | Error error -> fail (Native_graph.text error)
  in
  match Graph.mul_depth proved with
  | Some depth when Z.equal native_depth depth -> Z.to_int depth
  | Some _ | None -> fail "graph depth differs"

let graph_exact size =
  let rec walk id native proved =
    if id = size then begin
      let depth = graph_depth (List.rev native) (List.rev proved) in
      if depth > size then fail "graph depth exceeds layer count";
      1
    end else
      List.fold_left
        (fun count (native_rule, proved_rule) ->
          count + walk (id + 1) (native_rule :: native) (proved_rule :: proved))
        0 (graph_rules id)
  in
  walk 0 [] []

let graph_invalid () =
  let zero = nat "graph invalid tag" 0 in
  let native = Native_graph.prod ~tag:zero ~left:zero ~right:zero in
  let proved =
    { Graph.ltag = Z.zero; lrule = Graph.Prod (Z.zero, Z.zero) }
  in
  begin
    match Native_graph.mul_depth (Native_graph.graph [native] []) with
    | Error Native_graph.Layer -> ()
    | Error _ | Ok _ -> fail "graph native topology accepted"
  end;
  if Graph.mul_depth [proved] <> None then fail "graph proved topology accepted"

let graph_known () =
  let pairs = [
    graph_base 0;
    graph_prod 1 0 0;
    graph_prod 2 1 0;
    graph_prod 3 2 1;
    graph_prod 4 3 2;
  ] in
  let native, proved = List.split pairs in
  if graph_depth native proved <> 4 then fail "graph chain depth"

let graph () =
  graph_invalid ();
  graph_known ();
  let cases = List.init 6 graph_exact |> List.fold_left ( + ) 0 in
  if cases <> 1814 then fail "graph case count";
  cases

let hop_name id =
  match Syn.name ("v" ^ string_of_int id) with
  | Some name -> name
  | None -> fail "fhe emission name"

let hop_names = Array.init 8 hop_name

let hop_name_id value =
  let rec find at =
    if at = Array.length hop_names then fail "fhe emission input"
    else if Syn.name_equal value hop_names.(at) then at
    else find (at + 1)
  in
  find 0

let hop_cfg depth add mul recrypt =
  match Fhe.cfg
      ~depth:(Z.of_int depth) ~add:(Z.of_int add) ~mul:(Z.of_int mul)
      ~recrypt:(Z.of_int recrypt) with
  | Ok cfg -> cfg
  | Error error -> fail (Fhe.text error)

let hop_native_profile =
  match Fhe.profile [
    Z.zero, hop_cfg 4 2 11 29;
    Z.one, hop_cfg 3 3 13 31;
  ] with
  | Ok profile -> profile
  | Error error -> fail (Fhe.text error)

let hop_model_profile = [
  Z.zero, { Hop.cfull = Z.of_int 4; cadd = Z.of_int 2;
            cmul = Z.of_int 11; cre = Z.of_int 29 };
  Z.one, { Hop.cfull = Z.of_int 3; cadd = Z.of_int 3;
           cmul = Z.of_int 13; cre = Z.of_int 31 };
]

let hop_specs = [
  { key = 0; rem = 4 };
  { key = 0; rem = 4 };
  { key = 0; rem = 2 };
  { key = 0; rem = 0 };
  { key = 1; rem = 3 };
  { key = 1; rem = 3 };
]

let hop_native_env =
  let inputs =
    List.mapi
      (fun id spec ->
        Fhe.input hop_names.(id)
          ~key:(Z.of_int spec.key) ~rem:(Z.of_int spec.rem))
      hop_specs
  in
  match Fhe.env hop_native_profile inputs with
  | Ok env -> env
  | Error error -> fail (Fhe.text error)

let hop_model_env =
  List.mapi
    (fun id spec ->
      Z.of_int id, { Hop.ekey = Z.of_int spec.key; erem = Z.of_int spec.rem })
    hop_specs

let native_enc typ =
  Octra_vm.C_nat.to_z typ.Fhe.key, Octra_vm.C_nat.to_z typ.Fhe.rem
let model_enc typ = Hop.(typ.ekey, typ.erem)

let native_ins = function
  | Fhe.Load (name, typ) ->
      let key, rem = native_enc typ in
      Vload (hop_name_id name, key, rem)
  | Fhe.Narrow (depth, typ) ->
      let key, rem = native_enc typ in
      Vnarrow (Octra_vm.C_nat.to_z depth, key, rem)
  | Fhe.Add_cipher typ ->
      let key, rem = native_enc typ in
      Vadd (key, rem)
  | Fhe.Mul_cipher typ ->
      let key, rem = native_enc typ in
      Vmul (key, rem)
  | Fhe.Recrypt_cipher typ ->
      let key, rem = native_enc typ in
      Vrecrypt (key, rem)

let model_ins = function
  | Hop.HArgOp (name, typ) ->
      let key, rem = model_enc typ in
      Vload (Z.to_int name, key, rem)
  | Hop.HTrimOp (depth, typ) ->
      let key, rem = model_enc typ in
      Vnarrow (depth, key, rem)
  | Hop.HAddOp typ ->
      let key, rem = model_enc typ in
      Vadd (key, rem)
  | Hop.HMulOp typ ->
      let key, rem = model_enc typ in
      Vmul (key, rem)
  | Hop.HReOp typ ->
      let key, rem = model_enc typ in
      Vrecrypt (key, rem)

let hop_var id = {
  native = Fhe.var hop_names.(id);
  proved = Hop.FVar (Z.of_int id);
}

let hop_trim rem term = {
  native = Fhe.trim (Z.of_int rem) term.native;
  proved = Hop.FTrim (Z.of_int rem, term.proved);
}

let hop_add left right = {
  native = Fhe.add left.native right.native;
  proved = Hop.FAdd (left.proved, right.proved);
}

let hop_mul left right = {
  native = Fhe.mul left.native right.native;
  proved = Hop.FMul (left.proved, right.proved);
}

let hop_recrypt term = {
  native = Fhe.recrypt term.native;
  proved = Hop.FRe term.proved;
}

let hop_native_out term =
  match Fhe.host hop_native_profile hop_native_env term.native with
  | Error _ -> None
  | Ok plan ->
      if not (Fhe.host_check hop_native_profile hop_native_env plan) then
        fail "native fhe host check";
      if not (Fhe.emit_check hop_native_profile hop_native_env plan) then
        fail "native fhe emission check";
      begin
        match Fhe.check hop_native_profile hop_native_env (Fhe.host_term plan),
              Fhe.check hop_native_profile hop_native_env term.native with
        | Ok erased, Ok source
            when Octra_vm.C_nat.equal erased.typ.key source.typ.key
              && Octra_vm.C_nat.equal erased.typ.rem source.typ.rem -> ()
        | _ -> fail "native fhe host erasure"
      end;
      Some (List.map native_ins (Fhe.emit plan))

let hop_model_out term =
  match Hop.lower hop_model_profile hop_model_env term.proved with
  | None -> None
  | Some plan ->
      if Hop.herase plan <> term.proved then fail "proved fhe host erasure";
      if Hop.hval hop_model_profile hop_model_env plan <> Some (Hop.hty plan)
      then fail "proved fhe host check";
      let code = Hop.hemit plan in
      if Hop.hexec hop_model_profile hop_model_env code []
          <> Some [Hop.hty plan] then
        fail "proved fhe emission check";
      Some (List.map model_ins code)

let hop_check label term =
  if hop_native_out term <> hop_model_out term then
    fail (label ^ ": fhe emission result")

let hop_fixed () =
  let first = hop_mul (hop_var 0) (hop_var 1) in
  let zero = hop_mul (hop_trim 1 (hop_var 2)) (hop_trim 1 (hop_var 2)) in
  [
    hop_var 0;
    hop_trim 2 (hop_var 0);
    hop_add (hop_var 0) (hop_var 1);
    first;
    hop_mul first (hop_trim 3 (hop_var 0));
    hop_recrypt (hop_var 3);
    hop_recrypt zero;
    hop_add (hop_var 0) (hop_var 2);
    hop_mul (hop_var 3) (hop_var 3);
    hop_recrypt (hop_var 2);
    hop_trim 5 (hop_var 0);
    hop_add (hop_var 0) (hop_var 4);
  ]

let rec hop_gen depth state =
  let choices = if depth = 0 then 1 else 7 in
  let choice, state = pick choices state in
  match choice with
  | 0 ->
      let id, state = pick 8 state in
      hop_var id, state
  | 1 ->
      let rem, state = pick 6 state in
      let term, state = hop_gen (depth - 1) state in
      hop_trim rem term, state
  | 2 | 3 ->
      let left, state = hop_gen (depth - 1) state in
      let right, state = hop_gen (depth - 1) state in
      hop_add left right, state
  | 4 | 5 ->
      let left, state = hop_gen (depth - 1) state in
      let right, state = hop_gen (depth - 1) state in
      hop_mul left right, state
  | _ ->
      let term, state = hop_gen (depth - 1) state in
      hop_recrypt term, state

let hop_generated count =
  let rec walk index state =
    if index = count then ()
    else
      let term, state = hop_gen 6 state in
      hop_check ("fhe_" ^ string_of_int index) term;
      walk (index + 1) state
  in
  walk 0 { seed = 0x484f5354504c414eL }

let hop_mutations () =
  let typ = { Hop.ekey = Z.zero; erem = Z.of_int 4 } in
  let wrong = { Hop.ekey = Z.zero; erem = Z.of_int 3 } in
  let left = Hop.HArg (Z.zero, typ) in
  let right = Hop.HArg (Z.one, typ) in
  let bad = Hop.HAdd (left, right, wrong) in
  if Hop.hval hop_model_profile hop_model_env bad <> None then
    fail "proved fhe annotation mutation";
  if Hop.hexec hop_model_profile hop_model_env (Hop.hemit bad) [] <> None then
    fail "proved fhe emission mutation";
  let good = Hop.HAdd (left, right, typ) in
  match Hop.hemit good with
  | first :: second :: op :: [] ->
      if Hop.hexec hop_model_profile hop_model_env [op; first; second] []
          <> None then
        fail "proved fhe order mutation"
  | _ -> fail "proved fhe emission shape"

let hop () =
  hop_mutations ();
  let fixed = hop_fixed () in
  List.iteri
    (fun index term -> hop_check ("fixed_" ^ string_of_int index) term)
    fixed;
  hop_generated 10_000;
  List.length fixed + 10_000

let () =
  range ();
  seq ();
  let layout_cases = layout () in
  let label_cases = labels () in
  let frame_cases, header_cases, arg_cases, open_layout_cases = otb_frame () in
  let input_cases, output_cases, wrapper_mutations, artifact_cases,
      wrapper_runs =
    otb_scalar ()
  in
  let graph_cases = graph () in
  let hop_cases = hop () in
  Printf.printf
    "amlc_model = pass range_widths = %d sequence_caps = 33 layout_cases = %d label_cases = %d frame_cases = %d header_cases = %d arg_cases = %d open_layout_cases = %d input_cases = %d output_cases = %d wrapper_mutations = %d artifact_cases = %d wrapper_runs = %d graph_cases = %d fhe_cases = %d\n"
    Type.max_bits layout_cases label_cases frame_cases header_cases arg_cases
    open_layout_cases input_cases output_cases wrapper_mutations artifact_cases
    wrapper_runs graph_cases hop_cases