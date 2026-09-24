(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

module Emit = Octra_vm.C_emit
module Octb = Octra_vm.C_octb
module VM = Octra_vm.C_vm
module Local = Octra_vm.Local_vm
module Native = Octra_vm.Contract_vm
module Bytecode = Octra_vm.Bytecode

let fail name = failwith ("profile " ^ name)

let encode code =
  match Octb.encode code with
  | Ok value -> value
  | Error error -> failwith (Octb.text error)

let decode raw =
  match Octb.decode raw with
  | Ok value -> value
  | Error error -> failwith (Octb.decode_text error)

let alter raw at value =
  let next = Bytes.of_string raw in
  Bytes.set next at (Char.chr value);
  Bytes.to_string next

let refuse name test raw =
  match Octb.decode raw with
  | Error error when test error -> ()
  | Ok _ | Error _ -> fail name

let work code cap =
  let state = VM.make ~cap () in
  let result = VM.run state code in
  result, VM.work state

let active_work code cap =
  let state = VM.make ~cap ~activate:(Some Z.zero) () in
  let result = VM.run state code in
  result, VM.work state

let same_work expected actual = Z.equal (Z.of_int expected) actual

let square_code count =
  Array.init
    (count + 2)
    (fun index ->
      if index = 0 then Native.LDI (0, Native.VInt (Z.of_int 2))
      else if index <= count then Native.MUL (0, 0, 0)
      else Native.STOP)

let math_state ctx code cap =
  let state =
    Native.create_state
      ~ctx
      ~limit:cap
      ~strict_values:true
      ~caller:"caller"
      ~origin:"caller"
      ~address:"program"
      ~value:Z.zero
      ~storage:(Hashtbl.create 1)
      ()
  in
  Native.run state code, state

let square_state ctx count cap =
  math_state ctx (square_code count) cap

let vector_square_code count =
  Array.init
    ((count * 2) + 6)
    (fun index ->
      if index = 0 then Native.LDI (0, Native.VInt (Z.of_int 2))
      else if index = 1 then Native.MSTORE (0, 0)
      else if index = 2 || index = 3 then
        Native.LDI (index - 1, Native.VInt Z.zero)
      else if index = 4 then Native.LDI (3, Native.VInt Z.one)
      else if index = (count * 2) + 5 then Native.STOP
      else if (index - 5) mod 2 = 0 then Native.VECDOT (0, 1, 2, 3)
      else Native.MSTORE (0, 0))

let vector_square_state ctx count cap =
  math_state ctx (vector_square_code count) cap

let matrix_cap_code = [|
  Native.LDI (0, Native.VInt Z.zero);
  Native.LDI (1, Native.VInt Z.zero);
  Native.LDI (2, Native.VInt Z.zero);
  Native.LDI (3, Native.VInt (Z.of_int 1001));
  Native.LDI (4, Native.VInt (Z.of_int 1000));
  Native.LDI (5, Native.VInt Z.one);
  Native.MATMUL (0, 1, 2, 3, 4, 5);
  Native.STOP;
|]

let load_cap_code = [|
  Native.LDI (0, Native.VInt Z.zero);
  Native.LDI (1, Native.VString (String.make 1_000_001 'x'));
  Native.LDI (2, Native.VInt Z.zero);
  Native.LDI (3, Native.VInt (Z.of_int 1_000_001));
  Native.LDI (4, Native.VInt Z.one);
  Native.LOAD_INT8_BYTES_TO_MEM (0, 1, 2, 3, 4);
  Native.STOP;
|]

let overlap_code = [|
  Native.LDI (0, Native.VInt Z.one);
  Native.LDI (1, Native.VInt Z.zero);
  Native.LDI (2, Native.VInt (Z.of_int 2));
  Native.LDI (3, Native.VInt (Z.of_int 131_072));
  Native.MSTORE (0, 3);
  Native.LDI (3, Native.VInt (Z.of_int 196_608));
  Native.MSTORE (1, 3);
  Native.LDI (3, Native.VInt (Z.of_int 262_144));
  Native.MSTORE (2, 3);
  Native.ELEMWISE_MUL_INPLACE (0, 1, 2);
  Native.STOP;
|]

let square_bits name expected state =
  match state.Native.regs.(0) with
  | Native.VInt value ->
    if Z.numbits value <> expected then fail (name ^ " integer width")
  | _ -> fail (name ^ " result type")

let memory_int name state index expected =
  match Hashtbl.find_opt state.Native.memory.data index with
  | Some (Native.VInt value) when Z.equal value expected -> ()
  | _ -> fail (name ^ " memory value")

let native raw cap =
  let image =
    match Bytecode.decode_image raw with
    | Ok value -> value
    | Error _ -> fail "native decode"
  in
  begin
    match Native.Verifier.verify image.code with
    | Ok () -> ()
    | Error _ -> fail "native verify"
  end;
  let config =
    Local.config
      ~view:true
      ~byte_result:Native.Typed_bytes
      ~limit:cap
      ~method_name:"main"
      ~args:[]
      ()
  in
  match Local.run_at ~trace:false config ~entry:0 image.code with
  | Ok value -> value
  | Error _ -> fail "native run"

let () =
  let wide = Z.shift_left Z.one 300 in
  if not (String.equal (Octra_vm.C_eval.int_text wide) "int[301]") then
    fail "integer text";
  let code = [|
    Octb.Load (1, Emit.Int (Z.of_int 7));
    Octb.Load (2, Emit.Int (Z.of_int 5));
    Octb.Plus (0, 1, 2);
    Octb.Stop;
  |] in
  let raw = encode code in
  let image = decode raw in
  if image.code <> code then fail "roundtrip";
  let state = VM.make ~cap:12 () in
  begin
    match VM.run state image.code with
    | Ok () when same_work 6 (VM.work state)
        && Octra_vm.C_mach.equal (VM.result state) (Emit.Int (Z.of_int 12)) -> ()
    | _ -> fail "execution"
  end;
  begin
    let active = VM.make ~cap:12 ~activate:(Some Z.zero) () in
    match VM.run active image.code with
    | Ok () when same_work 7 (VM.work active)
        && Octra_vm.C_mach.equal
          (VM.result active) (Emit.Int (Z.of_int 12)) -> ()
    | _ -> fail "active execution"
  end;
  begin
    match VM.make_in [Emit.Int (Z.of_int 7); Emit.Bool true] with
    | Ok seeded
        when Octra_vm.C_mach.equal
          (VM.value seeded 1) (Emit.Int (Z.of_int 7))
          && Octra_vm.C_mach.equal (VM.value seeded 2) (Emit.Bool true) -> ()
    | Ok _ | Error _ -> fail "input registers"
  end;
  begin
    let maximum = List.init Native.input_limit (fun index -> Emit.Int (Z.of_int index)) in
    match VM.make_in maximum, VM.make_in (Emit.Int Z.zero :: maximum) with
    | Ok _, Error (VM.Input_count count) when count = Native.input_limit + 1 -> ()
    | _ -> fail "input count"
  end;
  begin
    match native raw 12 with
    | { Local.stop = Local.Returned; result = Native.VInt value;
        effort = 7; steps = 4; _ }
        when Z.equal value (Z.of_int 12) -> ()
    | value ->
      failwith
        (Printf.sprintf
          "profile native execution stop = %s result = %s effort = %d steps = %d"
          (Local.stop_text value.stop)
          (Local.value_text value.result)
          value.effort value.steps)
  end;
  refuse "magic" (function Octb.Magic -> true | _ -> false)
    (alter raw 0 (Char.code 'X'));
  refuse "version" (function Octb.Version 2 -> true | _ -> false)
    (alter raw 4 2);
  refuse "trailing" (function Octb.Trailing_data 1 -> true | _ -> false)
    (raw ^ "\000");
  refuse "short" (function Octb.Instruction_data _ -> true | _ -> false)
    (String.sub raw 0 (String.length raw - 1));
  let first = image.cells.(0).at in
  refuse "opcode" (function Octb.Opcode (0, 255) -> true | _ -> false)
    (alter raw first 255);
  refuse "register" (function Octb.Register_ref (0, 64) -> true | _ -> false)
    (alter raw (first + 1) 64);
  refuse "constant" (function Octb.Constant_ref (0, 255) -> true | _ -> false)
    (alter raw (first + 2) 255);
  let branch = [|Octb.Jump 1; Octb.Mark 1; Octb.Stop|] in
  let branch_raw = encode branch in
  let branch_image = decode branch_raw in
  let jump_at = branch_image.cells.(0).at in
  let mark_at = branch_image.cells.(1).at in
  refuse "jump" (function Octb.Jump_ref (0, 2) -> true | _ -> false)
    (alter branch_raw (jump_at + 1) 2);
  refuse "mark" (function Octb.Jump_mark 1 -> true | _ -> false)
    (alter branch_raw (mark_at + 1) 2);
  let loop = [|Octb.Mark 0; Octb.Jump 0|] in
  begin
    match work loop 5 with
    | Error (VM.Work_cap 5), used when same_work 5 used -> ()
    | Error (error), used ->
      failwith (Printf.sprintf "profile loop cap error = %s work = %s"
        (VM.text error) (Z.to_string used))
    | Ok (), used ->
      failwith (Printf.sprintf "profile loop cap accepted work = %s"
        (Z.to_string used))
  end;
  let bytes = String.make 256 '\001' in
  let slice = [|
    Octb.Load (1, Emit.Bytes bytes);
    Octb.Load (2, Emit.Int Z.zero);
    Octb.Load (3, Emit.Int Z.one);
    Octb.Slice (0, 1, 2, 3);
    Octb.Stop;
  |] in
  begin
    match work slice 9 with
    | Error (VM.Work_cap 9), used when same_work 9 used -> ()
    | _ -> fail "slice refusal"
  end;
  begin
    match work slice 10 with
    | Ok (), used when same_work 10 used -> ()
    | _ -> fail "slice acceptance"
  end;
  let types = [|
    Octb.Load (1, Emit.Bool true);
    Octb.Plus (0, 1, 1);
    Octb.Stop;
  |] in
  begin
    match work types 10 with
    | Error (VM.Value_type 1), used when same_work 4 used -> ()
    | _ -> fail "value type"
  end;
  let cell = Z.shift_left Z.one 128 in
  let integers = [|
    Octb.Load (1, Emit.Int cell);
    Octb.Load (2, Emit.Int cell);
    Octb.Times (0, 1, 2);
    Octb.Stop;
  |] in
  begin
    match active_work integers 14 with
    | Error (VM.Work_cap 14), used when same_work 14 used -> ()
    | _ -> fail "integer work refusal"
  end;
  begin
    match active_work integers 15 with
    | Ok (), used when same_work 15 used -> ()
    | _ -> fail "integer work acceptance"
  end;
  if not
      (Z.equal
        (Octra_vm.Int_work.cost ~base:17 Octra_vm.Int_work.Prior
          Octra_vm.Int_work.Mul cell cell)
        (Z.of_int 17))
  then fail "prior opcode work";
  if not
      (Z.equal
        (Octra_vm.Int_work.cost ~base:17 Octra_vm.Int_work.Active
          Octra_vm.Int_work.Mul cell cell)
        (Z.of_int 26))
  then fail "active opcode work";
  let base_ok, base_state = square_state Native.default_ctx 4 1000 in
  if not base_ok || base_state.effort_used <> 14 then
    fail "base integer work";
  square_bits "base integer work" 17 base_state;
  let active_ctx = { Native.default_ctx with int_work = Octra_vm.Int_work.Active } in
  let active_ok, active_state = square_state active_ctx 33 1_000_000 in
  if active_ok || not active_state.reverted
      || active_state.effort_used <> 351_636 then
    fail "active integer work";
  square_bits "active integer work" 65_537 active_state;
  let base_ok, base_state = vector_square_state Native.default_ctx 4 1000 in
  if not base_ok || base_state.effort_used <> 60 then
    fail "base vector work";
  square_bits "base vector work" 17 base_state;
  let active_ok, active_state =
    vector_square_state active_ctx 33 1_000_000
  in
  if active_ok || not active_state.reverted
      || active_state.effort_used <> 351_812 then
    fail "active vector work";
  square_bits "active vector work" 65_537 active_state;
  let active_ok, active_state = math_state active_ctx matrix_cap_code 1_000_000 in
  if active_ok || not active_state.reverted
      || active_state.effort_used <> 1083 then
    fail "active matrix item cap";
  let active_ok, active_state = math_state active_ctx load_cap_code 2_000_000 in
  if active_ok || not active_state.reverted
      || active_state.effort_used <> 500_015 then
    fail "active loader item cap";
  let base_ok, base_state = math_state Native.default_ctx overlap_code 1000 in
  if not base_ok || base_state.effort_used <> 22 then
    fail "base overlap work";
  memory_int "base overlap" base_state 2 (Z.of_int 1_572_864);
  let active_ok, active_state = math_state active_ctx overlap_code 1000 in
  if not active_ok || active_state.effort_used <> 24 then
    fail "active overlap work";
  memory_int "active overlap" active_state 2 (Z.of_int 786_432);
  Printf.printf "aml_profile = pass cases = 27\n"