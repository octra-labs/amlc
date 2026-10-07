(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

module Eff = Octra_vm.C_eff
module Eval = Octra_vm.C_eval
module Check = Octra_vm.C_check
module Nat = Octra_vm.C_nat
module Term = Octra_vm.C_term
module Type = Octra_vm.C_type
module Octb = Octra_vm.C_octb
module Vm = Octra_vm.Contract_vm
module Effect = Octra_vm.Aml_effect
module Evidence = Octra_vm.Aml_evidence
module Call = Octra_vm.Aml_call
module Bin = Octra_vm.C_bin
module Pbin = Octra_vm.C_pbin
module Lang = Octra_vm.Oct_lang
module Local = Octra_vm.Local_vm
module Program = Octra_vm.Vm_program

let fail name = failwith ("emission " ^ name)

let nat name value =
  match Nat.of_int value with
  | Some found -> found
  | None -> fail name

let run_vm ?(storage = []) ?(kinds = []) regs ops =
  let table = Hashtbl.of_seq (List.to_seq storage) in
  let state =
    Vm.create_state
      ~strict_values:true
      ~storage_kinds:kinds
      ~caller:"caller"
      ~origin:"origin"
      ~address:"program"
      ~value:Z.zero
      ~storage:table
      ()
  in
  List.iter (fun (reg, value) -> state.Vm.regs.(reg) <- value) regs;
  Vm.run state (Array.of_list ops), state

let eval name ?(inputs = []) term =
  match Eval.run_in inputs term with
  | Ok out -> out
  | Error error ->
    failwith (name ^ " reason = " ^ Eval.text error)

let sealed name ?(binds = []) term registry =
  match Effect.seal registry binds term with
  | Ok value -> value
  | Error error -> failwith (name ^ " reason = " ^ Effect.text error)

let prepared name registry values =
  match Effect.prepare registry values with
  | Ok value -> value
  | Error error -> failwith (name ^ " reason = " ^ Effect.text error)

let traced name registry actions =
  if not (Effect.trace registry actions) then fail name

let untraced name registry actions =
  if Effect.trace registry actions then fail name

let action_equal left right =
  let origin =
    match left.Eval.origin, right.Eval.origin with
    | Eval.Direct, Eval.Direct -> true
    | Eval.Held (left_kind, left_id), Eval.Held (right_kind, right_id) ->
      Nat.equal left_kind right_kind && Nat.equal left_id right_id
    | Eval.Direct, Eval.Held _ | Eval.Held _, Eval.Direct -> false
  in
  left.atom = right.atom && Eval.equal left.payload right.payload && origin

let effect_plan_checks () =
  let read = Eff.Read (nat "host read" 1) in
  let write = Eff.Write (nat "host write" 2) in
  let emit = Eff.Emit (nat "host emit" 3) in
  let stop = Eff.Fail (nat "host fail" 4) in
  let close = Eff.Close (nat "host close" 5) in
  let digest = String.make 32 '\001' in
  let program = {
    Lang.declaration = Lang.ProgramDecl;
    name = "Effects";
    imports = [];
    structs = [];
    enums = [];
    consts = [];
    invariants_decl = [];
    state = [
      { Lang.sf_name = "total"; sf_typ = Lang.TInt };
      { Lang.sf_name = "digest"; sf_typ = Lang.TBytes32 };
      { Lang.sf_name = "text"; sf_typ = Lang.TString };
    ];
    events = [
      {
        Lang.ev_name = "Changed";
        ev_fields = [
          "value", Lang.TInt, false;
          "digest", Lang.TBytes32, true;
        ];
      };
      { Lang.ev_name = "Empty"; ev_fields = [] };
      { Lang.ev_name = "Value"; ev_fields = ["value", Lang.TInt, false] };
      { Lang.ev_name = "Text"; ev_fields = ["value", Lang.TString, false] };
    ];
    errors = [
      { Lang.err_name = "Denied"; err_code = 7; err_msg = "denied" };
    ];
    interfaces = [];
    implements = [];
    ctor = None;
    funcs = [];
    forms = [];
  } in
  let bindings = [
    Effect.bind read (Effect.State "total");
    Effect.bind write (Effect.State "total");
    Effect.bind emit (Effect.Event "Changed");
    Effect.bind stop (Effect.Fault "Denied");
  ] in
  let effect_term =
    Term.Pair (
      Term.Act (read, Term.Int (Z.of_int 8)),
      Term.Pair (
        Term.Act (write, Term.Int (Z.of_int 9)),
        Term.Pair (
          Term.Act (emit,
            Term.Pair (Term.Int (Z.of_int 9), Term.Bytes digest)),
          Term.Act (stop, Term.Int (Z.of_int 5)))))
  in
  let entries =
    match Effect.make program bindings with
    | Ok value -> value
    | Error error -> failwith (Effect.text error)
  in
  let registry = sealed "host effect seal" effect_term entries in
  let actions = [
    Eval.direct read (Eval.Int (Z.of_int 8));
    Eval.direct write (Eval.Int (Z.of_int 9));
    Eval.direct emit
      (Eval.Pair (Eval.Int (Z.of_int 9), Eval.Bytes digest));
    Eval.direct stop (Eval.Int (Z.of_int 5));
  ] in
  let host = prepared "host prepare" registry [] in
  let plan = host.Effect.plan in
  if List.length host.out.actions <> List.length actions
      || not (List.for_all2 action_equal host.out.actions actions)
  then fail "host prepared actions";
  if not (Z.equal plan.cost (Z.of_int 190)) then fail "host plan cost";
  begin
    match plan.items with
    | [
        { Effect.host = Effect.Load ("total", Vm.VInt loaded);
          rollback = Effect.Preserve;
          ops = [Vm.SLOAD (0, "total"); Vm.EQ (1, 0, 2); Vm.ASSERT 1];
          cost = read_cost; _ };
        { Effect.host = Effect.Store ("total", Vm.VInt stored);
          rollback = Effect.Journal;
          ops = [Vm.SSTORE ("total", 0)]; cost = write_cost; _ };
        { Effect.host = Effect.Log ("Changed",
            [Vm.VInt changed; Vm.VBytes32 found]);
          rollback = Effect.Record;
          ops = [Vm.EMIT ("Changed", [0; 1])]; cost = emit_cost; _ };
        { Effect.host = Effect.Reject ("Denied",
            [Vm.VInt code; Vm.VString message; Vm.VInt detail]);
          rollback = Effect.Abort;
          ops = [Vm.LDI (0, Vm.VInt loaded_code);
            Vm.LDI (1, Vm.VString loaded_message);
            Vm.EMIT ("Error:Denied", [0; 1; 2]); Vm.REVERT];
          cost = fail_cost; _ };
      ]
      when Z.equal loaded (Z.of_int 8)
        && Z.equal stored (Z.of_int 9)
        && Z.equal changed (Z.of_int 9)
        && String.equal found digest
        && Z.equal code (Z.of_int 7)
        && Z.equal loaded_code (Z.of_int 7)
        && String.equal message "denied"
        && String.equal loaded_message "denied"
        && Z.equal detail (Z.of_int 5)
        && Z.equal read_cost (Z.of_int 27)
        && Z.equal write_cost (Z.of_int 100)
        && Z.equal emit_cost (Z.of_int 30)
        && Z.equal fail_cost (Z.of_int 33) -> ()
    | _ -> fail "host plan items"
  end;
  let lower name index payload scratch =
    match Effect.lower registry ~index ~payload ~scratch with
    | Ok value -> value
    | Error error -> failwith (name ^ " reason = " ^ Effect.text error)
  in
  let read_block = lower "host read lower" 0 [2] [0; 1] in
  let write_block = lower "host write lower" 1 [0] [] in
  let emit_block = lower "host emit lower" 2 [0; 1] [] in
  let fail_block = lower "host fail lower" 3 [2] [0; 1] in
  begin
    match read_block, write_block, emit_block, fail_block with
    | { Effect.ops = [Vm.SLOAD (0, "total"); Vm.EQ (1, 0, 2);
          Vm.ASSERT 1]; rollback = Effect.Preserve;
        cost = read_cost; charge = Effect.Exact; _ },
      { Effect.ops = [Vm.SSTORE ("total", 0)]; rollback = Effect.Journal;
        cost = write_cost; charge = Effect.Storage; _ },
      { Effect.ops = [Vm.EMIT ("Changed", [0; 1])];
        rollback = Effect.Record; cost = emit_cost;
        charge = Effect.Exact; _ },
      { Effect.ops = [Vm.LDI (0, Vm.VInt code);
          Vm.LDI (1, Vm.VString message);
          Vm.EMIT ("Error:Denied", [0; 1; 2]); Vm.REVERT];
        rollback = Effect.Abort; cost = fail_cost;
        charge = Effect.Exact; _ }
      when Z.equal code (Z.of_int 7)
        && String.equal message "denied"
        && Z.equal read_cost (Z.of_int 27)
        && Z.equal write_cost (Z.of_int 100)
        && Z.equal emit_cost (Z.of_int 30)
        && Z.equal fail_cost (Z.of_int 33) -> ()
    | _ -> fail "host register lowering"
  end;
  let evidence =
    match Evidence.make registry with
    | Ok value -> value
    | Error error -> failwith (Evidence.text error)
  in
  let bits =
    match Evidence.enc evidence with
    | Some value -> value
    | None -> fail "host evidence encoding"
  in
  let decoded =
    match Evidence.dec (Effect.registry registry) bits with
    | Ok value -> value
    | Error error -> failwith (Evidence.text error)
  in
  let restored =
    match Evidence.dec_any bits with
    | Ok value -> value
    | Error error -> failwith (Evidence.text error)
  in
  if not (Type.equal (Evidence.output decoded) (Effect.typ registry))
      || List.length (Evidence.blocks decoded) <> 4
      || Evidence.program decoded <> Effect.prog registry
      || not (Type.equal (Evidence.output restored) (Effect.typ registry))
      || List.length (Evidence.blocks restored) <> 4
      || Evidence.program restored <> Effect.prog registry
  then fail "host evidence roundtrip";
  let other_program = {
    program with
    state = { Lang.sf_name = "other"; sf_typ = Lang.TInt } :: program.state;
  }
  in
  let other =
    match Effect.make other_program [
      Effect.bind read (Effect.State "other");
      Effect.bind write (Effect.State "total");
      Effect.bind emit (Effect.Event "Changed");
      Effect.bind stop (Effect.Fault "Denied");
    ] with
    | Ok value -> value
    | Error error -> failwith (Effect.text error)
  in
  begin
    match Evidence.dec other bits with
    | Error Evidence.Registry -> ()
    | Error error -> failwith (Evidence.text error)
    | Ok _ -> fail "host evidence registry"
  end;
  begin
    match Evidence.blocks decoded with
    | [
        { Effect.rollback = Effect.Preserve; cost = read_cost; _ };
        { Effect.rollback = Effect.Journal; cost = write_cost; _ };
        { Effect.rollback = Effect.Record; cost = emit_cost; _ };
        { Effect.rollback = Effect.Abort; cost = fail_cost; _ };
      ]
      when Z.equal read_cost (Z.of_int 27)
        && Z.equal write_cost (Z.of_int 100)
        && Z.equal emit_cost (Z.of_int 30)
        && Z.equal fail_cost (Z.of_int 33) -> ()
    | _ -> fail "host evidence blocks"
  end;
  begin
    match Evidence.runtime decoded with
    | Error (Evidence.Lower Octra_vm.C_octb.Stack) -> ()
    | Error error -> failwith (Evidence.text error)
    | Ok _ -> fail "host evidence composite runtime"
  end;
  let guard = Term.bind Nat.zero Type.Many Type.Bool in
  let branch_term = Term.If (
    Term.Var Nat.zero,
    Term.Act (read, Term.Int (Z.of_int 8)),
    Term.Act (write, Term.Int (Z.of_int 9)))
  in
  let branch_registry =
    sealed "host branch seal" ~binds:[guard] branch_term entries
  in
  let branch_evidence =
    match Evidence.make branch_registry with
    | Ok value -> value
    | Error error -> failwith (Evidence.text error)
  in
  let branch_code =
    match Evidence.runtime branch_evidence with
    | Ok value -> Array.to_list value
    | Error error -> failwith (Evidence.text error)
  in
  let branch_read, read_state =
    run_vm
      ~storage:["total", "8"]
      ~kinds:["total", Vm.StorageInt]
      [1, Vm.VBool true]
      branch_code
  in
  if not branch_read
      || read_state.Vm.regs.(0) <> Vm.VInt (Z.of_int 8)
      || Hashtbl.find_opt read_state.Vm.storage "total" <> Some "8"
  then fail "host branch read runtime";
  let branch_write, write_state =
    run_vm
      ~storage:["total", "8"]
      ~kinds:["total", Vm.StorageInt]
      [1, Vm.VBool false]
      branch_code
  in
  if not branch_write
      || write_state.Vm.regs.(0) <> Vm.VInt (Z.of_int 9)
      || Hashtbl.find_opt write_state.Vm.storage "total" <> Some "9"
  then fail "host branch write runtime";
  let replace_field index value input =
    let rec walk index = function
      | Bin.Cons (_, rest) when index = 0 -> Bin.Cons (value, rest)
      | Bin.Cons (head, rest) -> Bin.Cons (head, walk (index - 1) rest)
      | other -> other
    in
    match Bin.dec_code input with
    | Some (Bin.Tag (tag, body)) ->
      begin
        match Bin.enc_code (Bin.Tag (tag, walk index body)) with
        | Some changed -> changed
        | None -> fail "host evidence mutation"
      end
    | Some _ | None -> fail "host evidence root"
  in
  let malformed name changed =
    match Evidence.dec (Effect.registry registry) changed with
    | Error Evidence.Form -> ()
    | Error error -> failwith (name ^ " reason = " ^ Evidence.text error)
    | Ok _ -> fail name
  in
  malformed "host evidence flow"
    (replace_field 3 (Bin.Tag (Z.zero, Bin.Nil)) bits);
  malformed "host evidence layouts"
    (replace_field 5 Bin.Nil bits);
  malformed "host evidence blocks"
    (replace_field 6 Bin.Nil bits);
  malformed "host evidence cost"
    (replace_field 7 (Bin.Tag (Z.zero, Bin.Nil)) bits);
  let read_ok, read_state =
    run_vm
      ~storage:["total", "8"]
      ~kinds:["total", Vm.StorageInt]
      [2, Vm.VInt (Z.of_int 8)]
      read_block.Effect.ops
  in
  if not read_ok
      || Z.of_int read_state.Vm.effort_used <> read_block.Effect.cost
  then
    fail "host read VM cost";
  let read_bad, _ =
    run_vm
      ~storage:["total", "8"]
      ~kinds:["total", Vm.StorageInt]
      [2, Vm.VInt (Z.of_int 7)]
      read_block.Effect.ops
  in
  if read_bad then fail "host read VM assertion";
  let large = Z.pred (Z.shift_left Z.one 255) in
  let write_ok, write_state =
    run_vm
      ~kinds:["total", Vm.StorageInt]
      [0, Vm.VInt large]
      write_block.Effect.ops
  in
  let write_cost =
    Z.add write_block.Effect.cost
      (Z.of_int (Vm.storage_work (Vm.VInt large)))
  in
  if not write_ok
      || Z.of_int write_state.Vm.effort_used <> write_cost
      || Hashtbl.find_opt write_state.Vm.storage "total"
        <> Some (Z.to_string large)
  then fail "host write VM cost";
  let journal_ok, journal_state =
    run_vm
      ~storage:["total", "8"]
      ~kinds:["total", Vm.StorageInt]
      [0, Vm.VInt large]
      (Vm.CHECKPOINT :: write_block.Effect.ops @ [Vm.ROLLBACK])
  in
  if not journal_ok
      || Hashtbl.find_opt journal_state.Vm.storage "total" <> Some "8"
  then fail "host write VM rollback";
  let emit_ok, emit_state =
    run_vm
      [0, Vm.VInt (Z.of_int 9); 1, Vm.VBytes32 digest]
      emit_block.Effect.ops
  in
  if not emit_ok
      || Z.of_int emit_state.Vm.effort_used <> emit_block.Effect.cost
  then
    fail "host emit VM cost";
  let fail_ok, fail_state =
    run_vm
      [2, Vm.VInt (Z.of_int 5)]
      fail_block.Effect.ops
  in
  if fail_ok
      || Z.of_int fail_state.Vm.effort_used <> fail_block.Effect.cost
  then
    fail "host fail VM cost";
  let refused name check result =
    match result with
    | Error error when check error -> ()
    | Error error -> failwith (name ^ " reason = " ^ Effect.text error)
    | Ok _ -> fail name
  in
  untraced "host action reorder" registry [
      Eval.direct write (Eval.Int (Z.of_int 9));
      Eval.direct read (Eval.Int (Z.of_int 8));
      Eval.direct emit
        (Eval.Pair (Eval.Int (Z.of_int 9), Eval.Bytes digest));
      Eval.direct stop (Eval.Int (Z.of_int 5));
    ];
  untraced "host action omission" registry [
      Eval.direct read (Eval.Int (Z.of_int 8));
      Eval.direct write (Eval.Int (Z.of_int 9));
      Eval.direct emit
        (Eval.Pair (Eval.Int (Z.of_int 9), Eval.Bytes digest));
    ];
  refused "host site index"
    (function Effect.Site_index 4 -> true | _ -> false)
    (Effect.lower registry ~index:4 ~payload:[] ~scratch:[]);
  refused "host payload registers"
    (function Effect.Payload_regs (atom, 1, 0) -> atom = read | _ -> false)
    (Effect.lower registry ~index:0 ~payload:[] ~scratch:[0; 1]);
  refused "host scratch registers"
    (function Effect.Scratch_regs (atom, 2, 1) -> atom = read | _ -> false)
    (Effect.lower registry ~index:0 ~payload:[2] ~scratch:[0]);
  refused "host excess scratch"
    (function Effect.Scratch_regs (atom, 0, 1) -> atom = write | _ -> false)
    (Effect.lower registry ~index:1 ~payload:[0] ~scratch:[1]);
  refused "host register alias"
    (function Effect.Register_alias (atom, 2) -> atom = read | _ -> false)
    (Effect.lower registry ~index:0 ~payload:[2] ~scratch:[2; 1]);
  refused "host register range"
    (function Effect.Register 64 -> true | _ -> false)
    (Effect.lower registry ~index:1 ~payload:[64] ~scratch:[]);
  refused "host event registers"
    (function Effect.Payload_regs (atom, 2, 1) -> atom = emit | _ -> false)
    (Effect.lower registry ~index:2 ~payload:[0] ~scratch:[]);
  refused "host payload alias"
    (function Effect.Register_alias (atom, 0) -> atom = emit | _ -> false)
    (Effect.lower registry ~index:2 ~payload:[0; 0] ~scratch:[]);
  refused "host duplicate"
    (function Effect.Atom_repeated atom -> atom = read | _ -> false)
    (Effect.make program (Effect.bind read (Effect.State "total") :: bindings));
  refused "host target kind"
    (function Effect.Target_kind (atom, Effect.Event "Changed") ->
      atom = read | _ -> false)
    (Effect.make program [Effect.bind read (Effect.Event "Changed")]);
  refused "host target absent"
    (function Effect.Target_absent (Effect.State "absent") -> true | _ -> false)
    (Effect.make program [Effect.bind read (Effect.State "absent")]);
  refused "host target repeated"
    (function Effect.Target_repeated (Effect.Event "Changed") -> true
      | _ -> false)
    (Effect.make
      { program with Lang.events = List.hd program.events :: program.events }
      [Effect.bind emit (Effect.Event "Changed")]);
  refused "host declaration"
    (function Effect.Program -> true | _ -> false)
    (Effect.make { program with Lang.declaration = Lang.ContractDecl } bindings);
  refused "host state type"
    (function Effect.Target_type (Effect.State "text", Lang.TString) -> true
      | _ -> false)
    (Effect.make program [Effect.bind read (Effect.State "text")]);
  refused "host event type"
    (function Effect.Target_type (Effect.Event "Text", Lang.TString) -> true
      | _ -> false)
    (Effect.make program [Effect.bind emit (Effect.Event "Text")]);
  let large = {
    Lang.ev_name = "Large";
    ev_fields = List.init 65 (fun index -> string_of_int index, Lang.TInt, false);
  } in
  refused "host event limit"
    (function Effect.Host_limit (atom, 65) -> atom = emit | _ -> false)
    (Effect.make { program with Lang.events = large :: program.events }
      [Effect.bind emit (Effect.Event "Large")]);
  let read_registry =
    match Effect.make program [Effect.bind read (Effect.State "total")] with
    | Ok value -> value
    | Error error -> failwith (Effect.text error)
  in
  let mixed_term = Term.Pair (
      Term.Act (read, Term.Int Z.zero),
      Term.Act (read, Term.Bool true)) in
  refused "host static type"
    (function Effect.Site_type (atom, expected, actual) ->
      atom = read
      && Type.equal expected Type.Int
      && Type.equal actual Type.Bool
      | _ -> false)
    (Effect.seal read_registry [] mixed_term);
  let branch_term = Term.If (
      Term.Bool true,
      Term.Act (read, Term.Int Z.zero),
      Term.Act (emit, Term.Int Z.one)) in
  refused "host branch missing"
    (function Effect.Binding_absent atom -> atom = emit | _ -> false)
    (Effect.seal read_registry [] branch_term);
  let branch_registry =
    match Effect.make program [
      Effect.bind read (Effect.State "total");
      Effect.bind emit (Effect.Event "Value");
    ] with
    | Ok value -> sealed "host branch seal" branch_term value
    | Error error -> failwith (Effect.text error)
  in
  traced "host branch left" branch_registry
    [Eval.direct read (Eval.Int Z.zero)];
  traced "host branch right" branch_registry
    [Eval.direct emit (Eval.Int Z.one)];
  untraced "host branch union" branch_registry [
      Eval.direct read (Eval.Int Z.zero);
      Eval.direct emit (Eval.Int Z.one);
    ];
  let branch_host = prepared "host branch prepare" branch_registry [] in
  begin
    match branch_host.plan.items with
    | [{ Effect.host = Effect.Load ("total", Vm.VInt value); _ }]
        when Z.equal value Z.zero -> ()
    | _ -> fail "host branch selected"
  end;
  let event_registry =
    match Effect.make program [Effect.bind emit (Effect.Event "Changed")] with
    | Ok value -> value
    | Error error -> failwith (Effect.text error)
  in
  let event_term = Term.Act (emit, Term.Bool true) in
  refused "host static event type"
    (function Effect.Site_type (atom, Type.Pair (Type.Int, Type.Bytes len),
      Type.Bool) -> atom = emit && Nat.to_int len = 32 | _ -> false)
    (Effect.seal event_registry [] event_term);
  let fault_registry =
    match Effect.make program [Effect.bind stop (Effect.Fault "Denied")] with
    | Ok value -> value
    | Error error -> failwith (Effect.text error)
  in
  let fault_term =
    Term.Act (stop, Term.Vec (Type.Int, [Term.Int Z.zero])) in
  refused "host static fault type"
    (function Effect.Site_payload (atom, Type.Vec _) -> atom = stop | _ -> false)
    (Effect.seal fault_registry [] fault_term);
  refused "host missing"
    (function Effect.Binding_absent atom -> atom = read | _ -> false)
    (match Effect.make program [] with
     | Ok value -> Effect.seal value [] effect_term
     | Error error -> failwith (Effect.text error));
  untraced "host payload" registry
    [Eval.direct read (Eval.Bool true)];
  untraced "host event order" registry
    [Eval.direct emit (Eval.Pair (Eval.Bytes digest, Eval.Int Z.one))];
  let empty_registry =
    match Effect.make program [Effect.bind emit (Effect.Event "Empty")] with
    | Ok value -> sealed "host empty seal" (Term.Act (emit, Term.Unit)) value
    | Error error -> failwith (Effect.text error)
  in
  begin
    match (prepared "host empty prepare" empty_registry []).plan with
    | { Effect.items = [{ host = Effect.Log ("Empty", []);
        ops = [Vm.EMIT ("Empty", [])]; _ }]; _ } -> ()
    | _ -> fail "host empty event"
  end;
  let value_term = Term.Act (emit, Term.Int (Z.of_int 6)) in
  let value_registry =
    match Effect.make program [Effect.bind emit (Effect.Event "Value")] with
    | Ok value -> sealed "host value seal" value_term value
    | Error error -> failwith (Effect.text error)
  in
  begin
    match (prepared "host value prepare" value_registry []).plan with
    | { Effect.items = [{ host = Effect.Log ("Value", [Vm.VInt value]);
        ops = [Vm.EMIT ("Value", [0])]; _ }]; _ }
        when Z.equal value (Z.of_int 6) -> ()
    | _ -> fail "host scalar event"
  end;
  let item = Term.bind Nat.zero Type.Many Type.Int in
  let state = Term.bind Nat.one Type.One Type.Int in
  let repeated_term = Term.Vfold (
    Term.Vec (Type.Int, [Term.Int Z.one; Term.Int Z.one; Term.Int Z.one]),
    Term.Int Z.zero,
    Term.fold item state
      (Term.Act (emit, Term.Add (Term.Var Nat.zero, Term.Var Nat.one))))
  in
  let repeated_registry =
    match Effect.make program [Effect.bind emit (Effect.Event "Value")] with
    | Ok value -> sealed "host repeated seal" repeated_term value
    | Error error -> failwith (Effect.text error)
  in
  let repeated_evidence =
    match Evidence.make repeated_registry with
    | Ok value -> value
    | Error error -> failwith (Evidence.text error)
  in
  begin
    match Evidence.blocks repeated_evidence with
    | [
        { Effect.index = 0; rollback = Effect.Record; _ };
        { Effect.index = 0; rollback = Effect.Record; _ };
        { Effect.index = 0; rollback = Effect.Record; _ };
      ] -> ()
    | _ -> fail "host repeated evidence"
  end;
  let repeated_code =
    match Evidence.runtime repeated_evidence with
    | Ok value -> Array.to_list value
    | Error error -> failwith (Evidence.text error)
  in
  let repeated_ok, repeated_state = run_vm [] repeated_code in
  if not repeated_ok
      || repeated_state.Vm.regs.(0) <> Vm.VInt (Z.of_int 3)
      || List.length !(repeated_state.Vm.logs) <> 3
  then fail "host repeated runtime";
  let repeated_actions = (eval "host repeated eval" repeated_term).actions in
  begin
    match (prepared "host repeated prepare" repeated_registry []).plan with
    | { Effect.cost; _ } when Z.equal cost (Z.of_int 90) -> ()
    | _ -> fail "host repeated cost"
  end;
  untraced "host repeated limit" repeated_registry
    (repeated_actions @ [Eval.direct emit (Eval.Int (Z.of_int 4))]);
  let rec deep depth =
    if depth = 0 then Term.Act (emit, Term.Unit)
    else
      let item_id = nat "host fuel item" (depth * 2) in
      let state_id = nat "host fuel state" (depth * 2 + 1) in
      let item = Term.bind item_id Type.Many Type.Unit in
      let state = Term.bind state_id Type.Many Type.Unit in
      Term.Vfold (
        Term.Vec (Type.Unit, [Term.Unit; Term.Unit]),
        Term.Unit,
        Term.fold item state (deep (depth - 1)))
  in
  let deep_term = deep 17 in
  begin
    match Check.check deep_term with
    | Ok info when Z.gt info.res.steps Eval.max_cost -> ()
    | Ok _ | Error _ -> fail "host fuel premise"
  end;
  let deep_registry =
    match Effect.make program [Effect.bind emit (Effect.Event "Empty")] with
    | Ok value -> sealed "host fuel seal" deep_term value
    | Error error -> failwith (Effect.text error)
  in
  begin
    match Evidence.make deep_registry with
    | Error (Evidence.Lower Octb.Effect_map) -> ()
    | Error error -> failwith (Evidence.text error)
    | Ok _ -> fail "host fuel evidence"
  end;
  let rec fork depth term =
    if depth = 0 then term
    else
      let next = fork (depth - 1) term in
      Term.If (Term.Bool true, next, next)
  in
  let modest_registry =
    match Effect.make program [Effect.bind emit (Effect.Event "Empty")] with
    | Ok value -> sealed "host emission modest seal" (fork 3 (deep 3)) value
    | Error error -> failwith (Effect.text error)
  in
  begin
    match Evidence.make modest_registry with
    | Ok value when List.length (Evidence.blocks value) = 64 -> ()
    | Ok _ -> fail "host emission modest count"
    | Error error -> failwith (Evidence.text error)
  end;
  let rec scalar depth =
    if depth = 0 then
      Term.Snd (Term.Pair (Term.Act (emit, Term.Unit), Term.Int Z.zero))
    else
      let item = Term.bind (nat "host scalar item" (100 + depth * 2))
        Type.Many Type.Unit in
      let state = Term.bind (nat "host scalar state" (101 + depth * 2))
        Type.Many Type.Int in
      Term.Vfold (
        Term.Vec (Type.Unit, [Term.Unit; Term.Unit]),
        Term.Int Z.zero,
        Term.fold item state (scalar (depth - 1)))
  in
  let scalar_registry =
    match Effect.make program [Effect.bind emit (Effect.Event "Empty")] with
    | Ok value -> sealed "host emission scalar seal" (fork 3 (scalar 3)) value
    | Error error -> failwith (Effect.text error)
  in
  let scalar_evidence =
    match Evidence.make scalar_registry with
    | Ok value when List.length (Evidence.blocks value) = 64 -> value
    | Ok _ -> fail "host emission scalar count"
    | Error error -> failwith (Evidence.text error)
  in
  let scalar_code =
    match Evidence.runtime scalar_evidence with
    | Ok value -> Array.to_list value
    | Error error -> failwith (Evidence.text error)
  in
  let scalar_ok, scalar_state = run_vm [] scalar_code in
  if not scalar_ok
      || scalar_state.Vm.regs.(0) <> Vm.VInt Z.zero
      || List.length !(scalar_state.Vm.logs) <> 8
  then fail "host emission scalar runtime";
  let wide_term = fork 10 (deep 16) in
  let wide_info =
    match Check.check wide_term with
    | Ok value when Z.leq value.res.steps Eval.max_cost -> value
    | Ok _ | Error _ -> fail "host emission premise"
  in
  let wide_count =
    List.fold_left
      (fun total location -> Z.add total location.Check.count)
      Z.zero (Check.locations wide_info)
  in
  if Z.leq wide_count (Z.of_int Check.max_nodes) then
    fail "host emission count";
  let wide_registry =
    match Effect.make program [Effect.bind emit (Effect.Event "Empty")] with
    | Ok value -> sealed "host emission seal" wide_term value
    | Error error -> failwith (Effect.text error)
  in
  begin
    match Octb.effect_layouts (Effect.prog wide_registry) with
    | Error Octb.Effect_map -> ()
    | Error error -> failwith (Octb.text error)
    | Ok _ -> fail "host emission layouts"
  end;
  begin
    match Octb.emit_effects (Effect.prog wide_registry) [] with
    | Error Octb.Effect_map -> ()
    | Error error -> failwith (Octb.text error)
    | Ok _ -> fail "host emission code"
  end;
  begin
    match Evidence.make wide_registry with
    | Error (Evidence.Lower Octb.Effect_map) -> ()
    | Error error -> failwith (Evidence.text error)
    | Ok _ -> fail "host emission evidence"
  end;
  let small_registry =
    match Effect.make program [Effect.bind emit (Effect.Event "Empty")] with
    | Ok value ->
      sealed "host emission small seal" (Term.Act (emit, Term.Unit)) value
    | Error error -> failwith (Effect.text error)
  in
  let small_evidence =
    match Evidence.make small_registry with
    | Ok value -> value
    | Error error -> failwith (Evidence.text error)
  in
  begin
    match Evidence.enc small_evidence,
        Pbin.code (Effect.prog wide_registry) with
    | Some bits, Some program_code ->
      begin
        match Bin.dec_code bits with
        | Some (Bin.Tag (tag, Bin.Cons (_, rest))) ->
          begin
            match Bin.enc_code (Bin.Tag (tag, Bin.Cons (program_code, rest))) with
            | Some changed ->
              begin
                match Evidence.dec (Effect.registry wide_registry) changed with
                | Error (Evidence.Lower Octb.Effect_map) -> ()
                | Error error -> failwith (Evidence.text error)
                | Ok _ -> fail "host emission decode"
              end
            | None -> fail "host emission reencode"
          end
        | Some _ | None -> fail "host emission root"
      end
    | None, _ | _, None -> fail "host emission encoding"
  end;
  let absent_term = Term.Vfold (
    Term.Vec (Type.Int, []),
    Term.Int Z.zero,
    Term.fold item state
      (Term.Act (emit, Term.Add (Term.Var Nat.zero, Term.Var Nat.one))))
  in
  let absent_registry =
    match Effect.make program [Effect.bind emit (Effect.Event "Value")] with
    | Ok value -> sealed "host absent seal" absent_term value
    | Error error -> failwith (Effect.text error)
  in
  let absent_evidence =
    match Evidence.make absent_registry with
    | Ok value -> value
    | Error error -> failwith (Evidence.text error)
  in
  if Evidence.blocks absent_evidence <> [] then fail "host absent evidence";
  let absent_code =
    match Evidence.runtime absent_evidence with
    | Ok value -> Array.to_list value
    | Error error -> failwith (Evidence.text error)
  in
  let absent_ok, absent_state = run_vm [] absent_code in
  if not absent_ok
      || absent_state.Vm.regs.(0) <> Vm.VInt Z.zero
      || !(absent_state.Vm.logs) <> []
  then fail "host absent runtime";
  begin
    match Evidence.enc absent_evidence with
    | None -> fail "host absent evidence encoding"
    | Some bits ->
      begin
        match Evidence.dec (Effect.registry absent_registry) bits with
        | Ok value when Evidence.blocks value = [] -> ()
        | Ok _ -> fail "host absent evidence roundtrip"
        | Error error -> failwith (Evidence.text error)
      end
  end;
  refused "host absent limit"
    (function Effect.Site_limit atom -> atom = emit | _ -> false)
    (Effect.lower absent_registry ~index:0 ~payload:[0] ~scratch:[]);
  let after_fail_term = Term.Pair (
    Term.Act (stop, Term.Int (Z.of_int 5)),
    Term.Act (read, Term.Int Z.zero)) in
  let after_fail_registry =
    match Effect.make program bindings with
    | Ok value -> sealed "host after fail seal" after_fail_term value
    | Error error -> failwith (Effect.text error)
  in
  refused "host after fail"
    (function Effect.After_fail atom -> atom = read | _ -> false)
    (Effect.prepare after_fail_registry []);
  refused "host direct close"
    (function Effect.Site_origin (atom, Check.Direct) -> atom = close | _ -> false)
    (Effect.seal entries [] (Term.Act (close, Term.Unit)));
  let held_kind = nat "host held kind" 2 in
  let held_id = nat "host held id" 12 in
  let held_bind = Term.bind Nat.zero Type.One (Type.Cap held_kind) in
  let held_input = [held_bind, Eval.Cap (held_kind, held_id)] in
  let held_term = Term.Step (Term.Var Nat.zero, Term.Int (Z.of_int 11)) in
  let held_write = (eval "host held write" ~inputs:held_input held_term).actions in
  let held_registry =
    match Effect.make program [Effect.bind write (Effect.State "total")] with
    | Ok value -> sealed "host held seal" ~binds:[held_bind] held_term value
    | Error error -> failwith (Effect.text error)
  in
  begin
    match (prepared "host held prepare" held_registry
      [Eval.Cap (held_kind, held_id)]).plan with
    | { Effect.items = [{ action = { Eval.origin = Eval.Held (kind, id); _ }; _ }]; _ }
      when Nat.equal kind held_kind && Nat.equal id held_id -> ()
    | _ -> fail "host held write"
  end;
  traced "host held trace" held_registry held_write;
  refused "host held input count"
    (function Effect.Input_count (1, 0) -> true | _ -> false)
    (Effect.prepare held_registry []);
  refused "host held input type"
    (function Effect.Run (Eval.Input_type (id, Type.Cap kind)) ->
      Nat.equal id Nat.zero && Nat.equal kind held_kind | _ -> false)
    (Effect.prepare held_registry [Eval.Int Z.zero]);
  refused "host held close"
    (function Effect.Binding_absent (Eff.Close kind) ->
      Nat.equal kind held_kind | _ -> false)
    (Effect.seal
      (match Effect.make program [Effect.bind write (Effect.State "total")] with
       | Ok value -> value
       | Error error -> failwith (Effect.text error))
      [held_bind] (Term.Close (Term.Var Nat.zero)));
  let wide_count = Octb.input_limit + 1 in
  let wide_binds =
    List.init wide_count (fun index ->
      Term.bind (nat "host input limit" index) Type.Many Type.Int)
  in
  let wide_registry =
    match Effect.make program [] with
    | Ok value ->
      sealed "host input limit" ~binds:wide_binds
        (Term.Int Z.zero) value
    | Error error -> failwith (Effect.text error)
  in
  begin
    match Evidence.make wide_registry with
    | Error (Evidence.Lower Octb.Register) -> ()
    | Error error -> failwith (Evidence.text error)
    | Ok _ -> fail "host input register limit"
  end;
  let digest_registry =
    match Effect.make program
      [Effect.bind write (Effect.State "digest")] with
    | Ok value ->
      sealed "host digest seal" (Term.Act (write, Term.Bytes digest)) value
    | Error error -> failwith (Effect.text error)
  in
  begin
    match (prepared "host digest prepare" digest_registry []).plan with
    | { Effect.cost; _ } when Z.equal cost (Z.of_int 101) -> ()
    | _ -> fail "host dynamic cost"
  end;
  let digest_ok, digest_state =
    run_vm
      ~kinds:["digest", Vm.StorageBytes32]
      [0, Vm.VBytes32 digest]
      [Vm.SSTORE ("digest", 0)]
  in
  if not digest_ok || digest_state.Vm.effort_used <> 101 then
    fail "host dynamic VM cost"

let call_checks () =
  let emit = Eff.Emit (nat "call emit" 7) in
  let arg = Term.bind Nat.zero Type.Many Type.Int in
  let program = {
    Lang.declaration = Lang.ProgramDecl;
    name = "Call";
    imports = [];
    structs = [];
    enums = [];
    consts = [];
    invariants_decl = [];
    state = [];
    events = [
      { Lang.ev_name = "Value"; ev_fields = ["value", Lang.TInt, false] };
    ];
    errors = [];
    interfaces = [];
    implements = [];
    ctor = None;
    funcs = [];
    forms = [];
  } in
  let entries =
    match Effect.make program [Effect.bind emit (Effect.Event "Value")] with
    | Ok value -> value
    | Error error -> failwith (Effect.text error)
  in
  let term =
    Term.Act (emit, Term.Add (Term.Var Nat.zero, Term.Int Z.one))
  in
  let sealed = sealed "call seal" ~binds:[arg] term entries in
  let evidence =
    match Evidence.make sealed with
    | Ok value -> value
    | Error error -> failwith (Evidence.text error)
  in
  let call =
    match Call.make ~entry:900 ~first:1_000_000 evidence with
    | Ok value -> value
    | Error error -> failwith (Call.text error)
  in
  let runtime =
    match Evidence.runtime evidence with
    | Ok value -> value
    | Error error -> failwith (Evidence.text error)
  in
  let direct = Array.append [|Vm.MLOAD (1, 1001)|] runtime in
  let caller = [|
    Vm.JDEST 100;
    Vm.MLOAD (1, 1001);
    Vm.MSTORE (1001, 1);
    Vm.CALL_INT (0, 900);
    Vm.STOP;
  |] in
  let nested = Array.append caller (Call.code call) in
  let execute name code args =
    let config = Local.config ~method_name:"main" ~args () in
    match Local.run_at ~trace:true config ~entry:0 code with
    | Ok value -> value
    | Error error -> failwith (name ^ " reason = " ^ Local.error_text error)
  in
  let direct_out = execute "call direct" direct [Vm.VInt (Z.of_int 41)] in
  let nested_out = execute "call nested" nested [Vm.VInt (Z.of_int 41)] in
  let returned name value =
    match value.Local.stop with
    | Local.Returned -> ()
    | Local.Reverted | Local.Step_cap | Local.Host_operation _ -> fail name
  in
  returned "call direct return" direct_out;
  returned "call nested return" nested_out;
  if direct_out.result <> Vm.VInt (Z.of_int 42)
      || nested_out.result <> direct_out.result
      || nested_out.events <> direct_out.events
      || List.length nested_out.events <> 1
  then fail "call result";
  let first = Array.length caller + Call.body call in
  let last = first + Call.size call in
  let body =
    List.filter
      (fun frame -> frame.Local.pc >= first && frame.pc < last)
      nested_out.frames
  in
  let direct_body =
    List.filter
      (fun frame -> frame.Local.pc > 0 && frame.pc < Array.length direct - 1)
      direct_out.frames
  in
  let frame_equal left right =
    left.Local.op = right.Local.op
    && left.effort_after - left.effort_before
      = right.effort_after - right.effort_before
  in
  if List.length body <> Call.size call
      || List.length direct_body <> Call.size call
      || not (List.for_all2 frame_equal body direct_body)
  then fail "call body trace";
  if nested_out.steps - direct_out.steps <> 10 then fail "call steps";
  let wrong = execute "call input type" nested [Vm.VBool true] in
  begin
    match wrong.stop with
    | Local.Reverted -> ()
    | Local.Returned | Local.Step_cap | Local.Host_operation _ ->
      fail "call input type"
  end;
  let changed = Array.copy (Call.code call) in
  let at = Call.body call + Call.size call - 1 in
  changed.(at) <- Vm.LDI (0, Vm.VBool true);
  let changed = Array.append caller changed in
  let wrong = execute "call output type" changed [Vm.VInt (Z.of_int 41)] in
  begin
    match wrong.stop with
    | Local.Reverted -> ()
    | Local.Returned | Local.Step_cap | Local.Host_operation _ ->
      fail "call output type"
  end;
  begin
    match Program.scope ~first:10 [|Vm.JDEST 2; Vm.JDEST 2|] with
    | Error (Program.Scope_duplicate 2) -> ()
    | Error error -> failwith (Program.scope_text error)
    | Ok _ -> fail "call repeated label"
  end;
  begin
    match Program.scope ~first:10 [|Vm.JMP 2|] with
    | Error (Program.Scope_missing 2) -> ()
    | Error error -> failwith (Program.scope_text error)
    | Ok _ -> fail "call absent label"
  end

let run () =
  effect_plan_checks ();
  call_checks ()