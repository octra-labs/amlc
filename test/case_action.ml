(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

module Mach = Octra_vm.C_mach
module Emit = Octra_vm.C_emit
module Eff = Octra_vm.C_eff
module Eval = Octra_vm.C_eval
module Check = Octra_vm.C_check
module Nat = Octra_vm.C_nat
module Term = Octra_vm.C_term
module Type = Octra_vm.C_type
module Effect = Octra_vm.Aml_effect
module Lang = Octra_vm.Oct_lang

let fail name = failwith ("emission " ^ name)

let nat name value =
  match Nat.of_int value with
  | Some found -> found
  | None -> fail name

let eval name ?(inputs = []) term =
  match Eval.run_in inputs term with
  | Ok out -> out
  | Error error ->
    failwith (name ^ " reason = " ^ Eval.text error)

let checked name ?(inputs = []) term =
  match Check.check_in inputs term with
  | Ok info ->
    let found =
      Check.sites info
      |> List.map (fun site -> site.Check.atom)
      |> Eff.of_list
    in
    if Eff.equal found info.Check.eff then info
    else fail (name ^ " effect set")
  | Error error -> failwith (name ^ " reason = " ^ Check.text error)

let sealed name ?(binds = []) term registry =
  match Effect.seal registry binds term with
  | Ok value -> value
  | Error error -> failwith (name ^ " reason = " ^ Effect.text error)

let prepared name registry values =
  match Effect.prepare registry values with
  | Ok value -> value
  | Error error -> failwith (name ^ " reason = " ^ Effect.text error)

let projected name out =
  let text = List.map Eff.atom_text in
  if text out.Eval.plan <> text (Eval.atoms out.actions) then fail name

let action_checks () =
  let read_kind = nat "action read kind" 2 in
  let emit_kind = nat "action emit kind" 3 in
  let nested =
    Term.Act (Eff.Read read_kind,
      Term.Act (Eff.Emit emit_kind, Term.Int (Z.of_int 42)))
  in
  let nested_out = eval "action nested" nested in
  let nested_info = checked "action nested check" nested in
  projected "action nested projection" nested_out;
  begin
    match Check.locations nested_info with
    | [
        { Check.index = 0; site = {
            Check.atom = Eff.Read read;
            payload = Type.Int;
            origin = Check.Direct;
          }; count = first };
        { Check.index = 1; site = {
            Check.atom = Eff.Emit emit;
            payload = Type.Int;
            origin = Check.Direct;
          }; count = second };
      ]
      when Nat.equal read_kind read
        && Nat.equal emit_kind emit
        && Z.equal first Z.one
        && Z.equal second Z.one -> ()
    | _ -> fail "action nested static witness"
  end;
  begin
    match nested_out.plan, nested_out.actions with
    | [Eff.Read read; Eff.Emit emit],
      [
        { Eval.atom = Eff.Read action_read;
          payload = Eval.Int first;
          origin = Eval.Direct };
        { Eval.atom = Eff.Emit action_emit;
          payload = Eval.Int second;
          origin = Eval.Direct };
      ]
      when Nat.equal read_kind read
        && Nat.equal read_kind action_read
        && Nat.equal emit_kind emit
        && Nat.equal emit_kind action_emit
        && Z.equal first (Z.of_int 42)
        && Z.equal second (Z.of_int 42) -> ()
    | _ -> fail "action nested witness"
  end;
  begin
    match Mach.lower nested with
    | Some code ->
      begin
        match Mach.replay_actions code with
        | Some ([Emit.Int result], actions)
          when Z.equal result (Z.of_int 42)
            && List.map Eff.atom_text (Eval.atoms actions)
              = List.map Eff.atom_text nested_out.plan ->
          begin
            match actions with
            | [
                { Eval.payload = Eval.Int first; _ };
                { Eval.payload = Eval.Int second; _ };
              ]
              when Z.equal first (Z.of_int 42)
                && Z.equal second (Z.of_int 42) -> ()
            | _ -> fail "action machine payload"
          end
        | _ -> fail "action machine witness"
      end
    | None -> fail "action machine lower"
  end;
  let kind = nat "action held kind" 7 in
  let id = nat "action held id" 11 in
  let bind = Term.bind Nat.zero Type.One (Type.Cap kind) in
  let input = [bind, Eval.Cap (kind, id)] in
  let stepped = eval "action step" ~inputs:input
    (Term.Step (Term.Var Nat.zero, Term.Int (Z.of_int 9)))
  in
  projected "action step projection" stepped;
  begin
    match stepped.actions with
    | [{ Eval.atom = Eff.Write action_kind;
         payload = Eval.Int value;
         origin = Eval.Held (origin_kind, origin_id) }]
      when Nat.equal kind action_kind
        && Nat.equal kind origin_kind
        && Nat.equal id origin_id
        && Z.equal value (Z.of_int 9) -> ()
    | _ -> fail "action step witness"
  end;
  let closed = eval "action close" ~inputs:input
    (Term.Close (Term.Var Nat.zero))
  in
  projected "action close projection" closed;
  begin
    match closed.actions with
    | [{ Eval.atom = Eff.Close action_kind;
         payload = Eval.Unit;
         origin = Eval.Held (origin_kind, origin_id) }]
      when Nat.equal kind action_kind
        && Nat.equal kind origin_kind
        && Nat.equal id origin_id -> ()
    | _ -> fail "action close witness"
  end;
  let branch = Term.If (
    Term.Bool true,
    Term.Act (Eff.Read read_kind, Term.Int Z.one),
    Term.Act (Eff.Emit emit_kind, Term.Int (Z.of_int 2)))
  in
  let branch_info = checked "action branch check" branch in
  let branch_out = eval "action branch" branch in
  begin
    match Check.locations branch_info, branch_out.actions with
    | [
        { Check.index = 0; site = { Check.atom = Eff.Read _; _ }; _ };
        { Check.index = 1; site = { Check.atom = Eff.Emit _; _ }; _ };
      ], [{ Eval.atom = Eff.Read _; payload = Eval.Int value; _ }]
      when Z.equal value Z.one -> ()
    | _ -> fail "action branch upper set"
  end;
  let item = Term.bind Nat.zero Type.Many Type.Int in
  let state = Term.bind Nat.one Type.One Type.Int in
  let folded = Term.Vfold (
    Term.Vec (Type.Int, [Term.Int Z.one; Term.Int Z.one; Term.Int Z.one]),
    Term.Int Z.zero,
    Term.fold item state
      (Term.Act (Eff.Emit emit_kind,
        Term.Add (Term.Var Nat.zero, Term.Var Nat.one))))
  in
  let folded_info = checked "action fold check" folded in
  let folded_out = eval "action fold" folded in
  begin
    match Check.locations folded_info, folded_out.actions with
    | [{ Check.site = { Check.atom = Eff.Emit _; payload = Type.Int; _ };
         count; _ }], [first; second; third]
      when Z.equal count (Z.of_int 3)
        && List.for_all
          (fun action -> action.Eval.atom = Eff.Emit emit_kind)
          [first; second; third] -> ()
    | _ -> fail "action fold limit"
  end

let action_equal left right =
  let origin =
    match left.Eval.origin, right.Eval.origin with
    | Eval.Direct, Eval.Direct -> true
    | Eval.Held (left_kind, left_id), Eval.Held (right_kind, right_id) ->
      Nat.equal left_kind right_kind && Nat.equal left_id right_id
    | Eval.Direct, Eval.Held _ | Eval.Held _, Eval.Direct -> false
  in
  left.atom = right.atom && Eval.equal left.payload right.payload && origin

let effect_generated () =
  let read = Eff.Read (nat "generated read" 1) in
  let write = Eff.Write (nat "generated write" 2) in
  let emit = Eff.Emit (nat "generated emit" 3) in
  let atom seed =
    match seed mod 3 with
    | 0 -> read
    | 1 -> write
    | _ -> emit
  in
  let item = Term.bind Nat.zero Type.Many Type.Int in
  let state = Term.bind Nat.one Type.One Type.Int in
  let rec term depth seed =
    if depth = 0 then
      Term.Act (atom seed, Term.Int (Z.of_int seed))
    else
      match seed mod 5 with
      | 0 ->
        Term.Act (atom seed,
          Term.Add (Term.Int (Z.of_int seed), Term.Int (Z.of_int depth)))
      | 1 ->
        Term.If (Term.Bool (seed mod 2 = 0),
          term (depth - 1) (seed + 3),
          term (depth - 1) (seed + 7))
      | 2 ->
        Term.Fst (Term.Pair (
          term (depth - 1) (seed + 5),
          term (depth - 1) (seed + 11)))
      | 3 ->
        Term.Add (
          term (depth - 1) (seed + 13),
          term (depth - 1) (seed + 17))
      | _ ->
        let count = seed mod 4 in
        let values = List.init count (fun index -> Term.Int (Z.of_int index)) in
        Term.Vfold (Term.Vec (Type.Int, values), Term.Int (Z.of_int seed),
          Term.fold item state
            (Term.Act (emit,
              Term.Add (Term.Var Nat.zero, Term.Var Nat.one))))
  in
  let program = {
    Lang.declaration = Lang.ProgramDecl;
    name = "Generated";
    imports = [];
    structs = [];
    enums = [];
    consts = [];
    invariants_decl = [];
    state = [{ Lang.sf_name = "total"; sf_typ = Lang.TInt }];
    events = [{
      Lang.ev_name = "Value";
      ev_fields = ["value", Lang.TInt, false];
    }];
    errors = [];
    interfaces = [];
    implements = [];
    ctor = None;
    funcs = [];
    forms = [];
  } in
  let base =
    match Effect.make program [
      Effect.bind read (Effect.State "total");
      Effect.bind write (Effect.State "total");
      Effect.bind emit (Effect.Event "Value");
    ] with
    | Ok value -> value
    | Error error -> failwith (Effect.text error)
  in
  for seed = 0 to 255 do
    let source = term (seed mod 5) (seed + 1) in
    let info = checked "generated check" source in
    let registry = sealed "generated seal" source base in
    let out = eval "generated eval" source in
    let host = prepared "generated prepare" registry [] in
    let plan = host.Effect.plan in
    if List.length host.out.actions <> List.length out.actions
        || not (List.for_all2 action_equal host.out.actions out.actions)
    then fail "generated prepared actions";
    let cost =
      List.fold_left
        (fun total (item : Effect.item) -> Z.add total item.cost)
        Z.zero plan.items
    in
    if not (Z.equal cost plan.cost) then fail "generated host cost";
    let cap =
      Check.locations info
      |> List.fold_left
          (fun total location -> Z.add total location.Check.count)
          Z.zero
    in
    if Z.gt (Z.of_int (List.length out.actions)) cap then
      fail "generated action limit";
    begin
      match Mach.lower source with
      | Some code ->
        begin
          match Mach.replay_actions code with
          | Some (_, actions)
              when List.length actions = List.length out.actions
                && List.for_all2 action_equal actions out.actions -> ()
          | _ -> fail "generated action replay"
        end
      | None -> fail "generated action lower"
    end
  done

let run () =
  action_checks ();
  effect_generated ()