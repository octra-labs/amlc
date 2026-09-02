(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Numbers.DecimalString.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import Uni.
Require Import Dec.
Require Import Fun.
Require Import Host.

Import ListNotations.

Inductive target : Type :=
| HState : string -> ty -> target
| HEvent : string -> list ty -> target
| HFault : string -> nat -> string -> target.

Record binding : Type := Binding {
  ba : atom;
  bt : target
}.

Inductive site_origin : Type :=
| SDirect
| SHeld : nat -> site_origin.

Record site : Type := Site {
  sa : atom;
  st : ty;
  so : site_origin
}.

Inductive flow : Type :=
| FPure
| FAction : site -> flow
| FSeq : flow -> flow -> flow
| FFork : flow -> flow -> flow
| FLoop : nat -> flow -> flow.

Record location : Type := Location {
  ls : site;
  ln : nat
}.

Fixpoint flow_sites (selected : flow) : list site :=
  match selected with
  | FPure => []
  | FAction item => [item]
  | FSeq first second => flow_sites first ++ flow_sites second
  | FFork first second => flow_sites first ++ flow_sites second
  | FLoop _ body => flow_sites body
  end.

Fixpoint flow_locations_at (count : nat) (selected : flow)
    : list location :=
  match selected with
  | FPure => []
  | FAction item => [Location item count]
  | FSeq first second | FFork first second =>
      flow_locations_at count first ++ flow_locations_at count second
  | FLoop turns body => flow_locations_at (count * turns) body
  end.

Definition flow_locations (selected : flow) : list location :=
  flow_locations_at 1 selected.

Inductive rollback : Type :=
| Preserve
| Journal
| Record
| Abort.

Inductive host : Type :=
| HLoad : string -> value -> host
| HStore : string -> value -> host
| HLog : string -> list value -> host
| HReject : string -> nat -> string -> list value -> host.

Record item : Type := Item {
  ia : action;
  ih : host;
  ir : rollback;
  ic : nat
}.

Definition scalar (typ : ty) : bool :=
  match typ with
  | TInt | TBool | TBytes 32 => true
  | _ => false
  end.

Definition scalar_value (typ : ty) (payload : value) : bool :=
  scalar typ && Host.typed typ payload.

Fixpoint event_values (types : list ty) (payload : value)
    : option (list value) :=
  match types with
  | [] =>
      match payload with
      | VUnit => Some []
      | _ => None
      end
  | [typ] =>
      if scalar_value typ payload then Some [payload] else None
  | typ :: rest =>
      match payload with
      | VPair head tail =>
          if scalar_value typ head then
            match event_values rest tail with
            | Some values => Some (head :: values)
            | None => None
            end
          else None
      | _ => None
      end
  end.

Fixpoint fault_values (payload : value) : option (list value) :=
  match payload with
  | VUnit => Some []
  | VBool _ | VInt _ | VBytes _ => Some [payload]
  | VPair lhs rhs =>
      match fault_values lhs, fault_values rhs with
      | Some lhs, Some rhs => Some (lhs ++ rhs)
      | _, _ => None
      end
  | VVec _ | VCap _ _ | VEnc _ _ _ | VInl _ | VInr _ => None
  end.

Definition origin_ok (atom : atom) (origin : origin) : bool :=
  match atom, origin with
  | ARead _, ODirect
  | AWrite _, ODirect
  | AEmit _, ODirect
  | AFail _, ODirect => true
  | AWrite kind, OHeld actual _
  | AClose kind, OHeld actual _ => Nat.eqb kind actual
  | _, _ => false
  end.

Fixpoint find (atom : atom) (bindings : list binding) : option target :=
  match bindings with
  | [] => None
  | Binding found target :: rest =>
      if Fun.atom_eqb atom found then Some target else find atom rest
  end.

Fixpoint event_type (types : list ty) : option ty :=
  match types with
  | [] => Some TUnit
  | [typ] => if scalar typ then Some typ else None
  | typ :: rest =>
      if scalar typ then
        match event_type rest with
        | Some tail => Some (TPair typ tail)
        | None => None
        end
      else None
  end.

Fixpoint fault_type (typ : ty) : bool :=
  match typ with
  | TUnit | TBool | TInt | TBytes _ => true
  | TPair first second => fault_type first && fault_type second
  | TVec _ _ | TCap _ | TEnc _ _ | TSum _ _ => false
  end.

Definition site_origin_ok (atom : atom) (origin : site_origin) : bool :=
  match atom, origin with
  | ARead _, SDirect
  | AWrite _, SDirect
  | AEmit _, SDirect
  | AFail _, SDirect => true
  | AWrite kind, SHeld actual
  | AClose kind, SHeld actual => Nat.eqb kind actual
  | _, _ => false
  end.

Definition site_ok (bindings : list binding) (selected : site) : bool :=
  site_origin_ok (sa selected) (so selected) &&
  match sa selected, find (sa selected) bindings with
  | ARead _, Some (HState _ typ)
  | AWrite _, Some (HState _ typ) => ty_eqb (st selected) typ
  | AEmit _, Some (HEvent _ types) =>
      match event_type types with
      | Some typ => ty_eqb (st selected) typ
      | None => false
      end
  | AFail _, Some (HFault _ _ _) => fault_type (st selected)
  | _, _ => false
  end.

Definition action_origin_ok (selected : action) (expected : site_origin)
    : bool :=
  match ao selected, expected with
  | ODirect, SDirect => true
  | OHeld kind _ , SHeld expected => Nat.eqb kind expected
  | _, _ => false
  end.

Definition action_site (selected : action) (expected : site) : bool :=
  Fun.atom_eqb (aa selected) (sa expected) &&
  action_origin_ok selected (so expected) &&
  Host.typed (st expected) (av selected).

Definition path_join (first second : list (list site)) : list (list site) :=
  flat_map
    (fun head => map (fun tail => head ++ tail) second)
    first.

Fixpoint path_power (turns : nat) (body : list (list site))
    : list (list site) :=
  match turns with
  | 0 => [[]]
  | S rest => path_join body (path_power rest body)
  end.

Fixpoint flow_paths (selected : flow) : list (list site) :=
  match selected with
  | FPure => [[]]
  | FAction item => [[item]]
  | FSeq first second => path_join (flow_paths first) (flow_paths second)
  | FFork first second => flow_paths first ++ flow_paths second
  | FLoop turns body => path_power turns (flow_paths body)
  end.

Fixpoint pathb (sites : list site) (actions : list action) : bool :=
  match sites, actions with
  | [], [] => true
  | site :: site_rest, action :: action_rest =>
      action_site action site && pathb site_rest action_rest
  | _, _ => false
  end.

Definition traceb (selected : flow) (actions : list action) : bool :=
  existsb (fun sites => pathb sites actions) (flow_paths selected).

Definition follows (selected : flow) (actions : list action) : Prop :=
  exists sites,
    In sites (flow_paths selected) /\ pathb sites actions = true.

Theorem traceb_sound : forall selected actions,
  traceb selected actions = true -> follows selected actions.
Proof.
  intros selected actions accepted.
  unfold traceb in accepted.
  apply existsb_exists in accepted.
  destruct accepted as [sites [present exact]].
  exists sites.
  split; assumption.
Qed.

Theorem traceb_complete : forall selected actions,
  follows selected actions -> traceb selected actions = true.
Proof.
  intros selected actions [sites [present exact]].
  unfold traceb.
  apply existsb_exists.
  exists sites.
  split; assumption.
Qed.

Example trace_order :
  traceb
    (FSeq
      (FAction (Site (ARead 1) TInt SDirect))
      (FAction (Site (AWrite 2) TInt SDirect)))
    [Action (ARead 1) (VInt 3) ODirect;
     Action (AWrite 2) (VInt 4) ODirect] = true.
Proof.
  reflexivity.
Qed.

Example trace_reorder :
  traceb
    (FSeq
      (FAction (Site (ARead 1) TInt SDirect))
      (FAction (Site (AWrite 2) TInt SDirect)))
    [Action (AWrite 2) (VInt 4) ODirect;
     Action (ARead 1) (VInt 3) ODirect] = false.
Proof.
  reflexivity.
Qed.

Example trace_omission :
  traceb
    (FSeq
      (FAction (Site (ARead 1) TInt SDirect))
      (FAction (Site (AWrite 2) TInt SDirect)))
    [Action (ARead 1) (VInt 3) ODirect] = false.
Proof.
  reflexivity.
Qed.

Example trace_fork_union :
  traceb
    (FFork
      (FAction (Site (ARead 1) TInt SDirect))
      (FAction (Site (AWrite 2) TInt SDirect)))
    [Action (ARead 1) (VInt 3) ODirect;
     Action (AWrite 2) (VInt 4) ODirect] = false.
Proof.
  reflexivity.
Qed.

Fixpoint consume_one (selected : action) (locations : list location)
    : option (list location) :=
  match locations with
  | [] => None
  | Location expected count :: rest =>
      if action_site selected expected then
        match count with
        | 0 =>
            match consume_one selected rest with
            | Some next => Some (Location expected 0 :: next)
            | None => None
            end
        | S remaining => Some (Location expected remaining :: rest)
        end
      else
        match consume_one selected rest with
        | Some next => Some (Location expected count :: next)
        | None => None
        end
  end.

Fixpoint consume_all (locations : list location) (selected : list action)
    : option (list location) :=
  match selected with
  | [] => Some locations
  | head :: rest =>
      match consume_one head locations with
      | Some next => consume_all next rest
      | None => None
      end
  end.

Fixpoint quota (locations : list location) : nat :=
  match locations with
  | [] => 0
  | Location _ count :: rest => count + quota rest
  end.

Definition seal (bindings : list binding) (sites : list site) : bool :=
  forallb (site_ok bindings) sites.

Definition seal_flow (bindings : list binding) (selected : flow) : bool :=
  seal bindings (flow_sites selected).

Lemma seal_forall : forall bindings sites,
  seal bindings sites = true -> Forall (fun site => site_ok bindings site = true) sites.
Proof.
  intros bindings sites accepted.
  unfold seal in accepted.
  pose proof
    (proj1 (@forallb_forall site (site_ok bindings) sites) accepted) as all.
  rewrite Forall_forall.
  exact all.
Qed.

Theorem seal_member : forall bindings sites selected,
  seal bindings sites = true ->
  In selected sites ->
  site_ok bindings selected = true.
Proof.
  intros bindings sites selected accepted present.
  pose proof (seal_forall bindings sites accepted) as all.
  rewrite Forall_forall in all.
  apply all.
  exact present.
Qed.

Corollary seal_flow_member : forall bindings flow selected,
  seal_flow bindings flow = true ->
  In selected (flow_sites flow) ->
  site_ok bindings selected = true.
Proof.
  intros bindings flow selected accepted present.
  apply (seal_member bindings (flow_sites flow) selected accepted present).
Qed.

Theorem site_binding : forall bindings selected,
  site_ok bindings selected = true ->
  exists target, find (sa selected) bindings = Some target.
Proof.
  intros bindings [atom typ origin] accepted.
  unfold site_ok in accepted.
  apply andb_true_iff in accepted.
  destruct accepted as [_ accepted].
  destruct atom; destruct (find _ bindings) as [target |] eqn:found;
    try discriminate;
    exists target;
    reflexivity.
Qed.

Definition base_cost (atom : atom) : nat :=
  match atom with
  | ARead _ => 27
  | AWrite _ => 100
  | AEmit _ => 30
  | AFail _ => 33
  | AClose _ => 0
  end.

Inductive charge : Type :=
| CExact
| CStorage.

Inductive vmop : Type :=
| ILoad : nat -> string -> vmop
| IEqual : nat -> nat -> nat -> vmop
| IAssert : nat -> vmop
| IStore : string -> nat -> vmop
| IEmit : string -> list nat -> vmop
| IInt : nat -> nat -> vmop
| IText : nat -> string -> vmop
| IRevert.

Record vmblock : Type := VmBlock {
  vi : nat;
  vs : site;
  vr : rollback;
  vo : list vmop;
  vc : nat;
  vq : charge
}.

Fixpoint width (typ : ty) : option nat :=
  match typ with
  | TUnit => Some 0
  | TBool | TInt | TBytes _ => Some 1
  | TPair first second =>
      match width first, width second with
      | Some first_width, Some second_width =>
          Some (first_width + second_width)
      | _, _ => None
      end
  | TVec _ _ | TCap _ | TEnc _ _ | TSum _ _ => None
  end.

Definition reg_ok (reg : nat) : bool := Nat.ltb reg 64.

Definition regs_ok (regs : list nat) : bool := forallb reg_ok regs.

Fixpoint regs_unique (regs : list nat) : bool :=
  match regs with
  | [] => true
  | reg :: rest =>
      negb (existsb (Nat.eqb reg) rest) && regs_unique rest
  end.

Definition fresh (reg : nat) (regs : list nat) : bool :=
  reg_ok reg && negb (existsb (Nat.eqb reg) regs).

Definition scratch_pair (payload scratch : list nat)
    : option (nat * nat) :=
  match scratch with
  | [first; second] =>
      if fresh first payload && fresh second (first :: payload) then
        Some (first, second)
      else None
  | _ => None
  end.

Definition payload_ok (typ : ty) (payload : list nat) : bool :=
  match width typ with
  | Some count =>
      Nat.eqb count (List.length payload)
      && (regs_ok payload && regs_unique payload)
  | None => false
  end.

Definition op_regs (op : vmop) : list nat :=
  match op with
  | ILoad reg _ | IAssert reg | IStore _ reg | IInt reg _ | IText reg _ =>
      [reg]
  | IEqual out first second => [out; first; second]
  | IEmit _ regs => regs
  | IRevert => []
  end.

Definition ops_ok (ops : list vmop) : bool :=
  regs_ok (flat_map op_regs ops).

Definition code (bindings : list binding) (selected : site)
    (payload scratch : list nat)
    : option (rollback * list vmop * charge) :=
  match sa selected, find (sa selected) bindings with
  | ARead _, Some (HState name _) =>
      match payload, scratch_pair payload scratch with
      | [value], Some (loaded, guard) =>
          Some (Preserve,
            [ILoad loaded name; IEqual guard loaded value; IAssert guard],
            CExact)
      | _, _ => None
      end
  | AWrite _, Some (HState name _) =>
      match payload, scratch with
      | [value], [] => Some (Journal, [IStore name value], CStorage)
      | _, _ => None
      end
  | AEmit _, Some (HEvent name _) =>
      match scratch with
      | [] => Some (Record, [IEmit name payload], CExact)
      | _ => None
      end
  | AFail _, Some (HFault name fault message) =>
      match scratch_pair payload scratch with
      | Some (code_reg, message_reg) =>
          Some (Abort,
            [IInt code_reg fault; IText message_reg message;
             IEmit (String.append "Error:" name)
               (code_reg :: message_reg :: payload); IRevert],
            CExact)
      | None => None
      end
  | _, _ => None
  end.

Definition lower (bindings : list binding) (index : nat) (selected : site)
    (payload scratch : list nat) : option vmblock :=
  if site_ok bindings selected && payload_ok (st selected) payload then
    match code bindings selected payload scratch with
    | Some (rollback, ops, cost) =>
        if ops_ok ops then
          Some (VmBlock index selected rollback ops
            (base_cost (sa selected)) cost)
        else None
    | None => None
    end
  else None.

Lemma payload_ok_sound : forall typ payload,
  payload_ok typ payload = true ->
  width typ = Some (List.length payload) /\
  regs_ok payload = true /\ regs_unique payload = true.
Proof.
  intros typ payload accepted.
  unfold payload_ok in accepted.
  destruct (width typ) as [count |] eqn:found; try discriminate.
  apply andb_true_iff in accepted.
  destruct accepted as [same valid].
  apply andb_true_iff in valid.
  destruct valid as [valid unique].
  apply Nat.eqb_eq in same.
  subst.
  split.
  - reflexivity.
  - split; assumption.
Qed.

Lemma lower_gate : forall bindings index selected payload scratch block,
  lower bindings index selected payload scratch = Some block ->
  site_ok bindings selected = true /\
  payload_ok (st selected) payload = true.
Proof.
  intros bindings index selected payload scratch block accepted.
  unfold lower in accepted.
  destruct (site_ok bindings selected && payload_ok (st selected) payload)
    eqn:valid; try discriminate.
  apply andb_true_iff in valid.
  exact valid.
Qed.

Theorem lower_site : forall bindings index selected payload scratch block,
  lower bindings index selected payload scratch = Some block ->
  site_ok bindings selected = true.
Proof.
  intros bindings index selected payload scratch block accepted.
  exact (proj1 (lower_gate _ _ _ _ _ _ accepted)).
Qed.

Theorem lower_payload : forall bindings index selected payload scratch block,
  lower bindings index selected payload scratch = Some block ->
  width (st selected) = Some (List.length payload) /\
  regs_ok payload = true /\ regs_unique payload = true.
Proof.
  intros bindings index selected payload scratch block accepted.
  apply payload_ok_sound.
  exact (proj2 (lower_gate _ _ _ _ _ _ accepted)).
Qed.

Theorem lower_identity : forall bindings index selected payload scratch block,
  lower bindings index selected payload scratch = Some block ->
  vi block = index /\ vs block = selected.
Proof.
  intros bindings index selected payload scratch block accepted.
  unfold lower in accepted.
  destruct (site_ok bindings selected && payload_ok (st selected) payload);
    try discriminate.
  destruct (code bindings selected payload scratch)
    as [[[rollback ops] cost] |] eqn:found; try discriminate.
  destruct (ops_ok ops); try discriminate.
  inversion accepted.
  split; reflexivity.
Qed.

Theorem lower_shape : forall bindings index selected payload scratch block,
  lower bindings index selected payload scratch = Some block ->
  code bindings selected payload scratch =
    Some (vr block, vo block, vq block).
Proof.
  intros bindings index selected payload scratch block accepted.
  unfold lower in accepted.
  destruct (site_ok bindings selected && payload_ok (st selected) payload);
    try discriminate.
  destruct (code bindings selected payload scratch)
    as [[[rollback ops] cost] |] eqn:found; try discriminate.
  destruct (ops_ok ops); try discriminate.
  injection accepted as same.
  subst block.
  reflexivity.
Qed.

Theorem lower_regs : forall bindings index selected payload scratch block,
  lower bindings index selected payload scratch = Some block ->
  ops_ok (vo block) = true.
Proof.
  intros bindings index selected payload scratch block accepted.
  unfold lower in accepted.
  destruct (site_ok bindings selected && payload_ok (st selected) payload);
    try discriminate.
  destruct (code bindings selected payload scratch)
    as [[[rollback ops] cost] |] eqn:found; try discriminate.
  destruct (ops_ok ops) eqn:valid; try discriminate.
  inversion accepted.
  exact valid.
Qed.

Theorem lower_cost : forall bindings index selected payload scratch block,
  lower bindings index selected payload scratch = Some block ->
  vc block = base_cost (sa selected).
Proof.
  intros bindings index selected payload scratch block accepted.
  unfold lower in accepted.
  destruct (site_ok bindings selected && payload_ok (st selected) payload);
    try discriminate.
  destruct (code bindings selected payload scratch)
    as [[[rollback ops] cost] |] eqn:found; try discriminate.
  destruct (ops_ok ops); try discriminate.
  inversion accepted.
  reflexivity.
Qed.

Record layout : Type := Layout {
  lp : list nat;
  lx : list nat
}.

Record place : Type := Place {
  pi : nat;
  ps : site
}.

Fixpoint copies (index : nat) (selected : site) (count : nat)
    : list place :=
  match count with
  | 0 => []
  | S rest => Place index selected :: copies index selected rest
  end.

Fixpoint places (index : nat) (locations : list location) : list place :=
  match locations with
  | [] => []
  | Location selected count :: rest =>
      copies index selected count ++ places (S index) rest
  end.

Fixpoint lower_places (bindings : list binding) (selected : list place)
    (layouts : list layout) : option (list vmblock) :=
  match selected, layouts with
  | [], [] => Some []
  | Place index site :: rest, Layout payload scratch :: tail =>
      match lower bindings index site payload scratch,
        lower_places bindings rest tail with
      | Some block, Some blocks => Some (block :: blocks)
      | _, _ => None
      end
  | _, _ => None
  end.

Definition lower_all (bindings : list binding) (index : nat)
    (locations : list location) (layouts : list layout)
    : option (list vmblock) :=
  lower_places bindings (places index locations) layouts.

Fixpoint fit (selected : list place) (blocks : list vmblock) : Prop :=
  match selected, blocks with
  | [], [] => True
  | Place index site :: rest, block :: tail =>
      vi block = index /\ vs block = site /\ fit rest tail
  | _, _ => False
  end.

Definition blocks_exact (index : nat) (locations : list location)
    (blocks : list vmblock) : Prop :=
  fit (places index locations) blocks.

Lemma copies_length : forall index selected count,
  List.length (copies index selected count) = count.
Proof.
  intros index selected count.
  induction count; cbn.
  - reflexivity.
  - rewrite IHcount.
    reflexivity.
Qed.

Lemma places_length : forall index locations,
  List.length (places index locations) = quota locations.
Proof.
  intros index locations.
  revert index.
  induction locations as [|[selected count] rest repeat]; intros index; cbn.
  - reflexivity.
  - rewrite List.length_app, copies_length, repeat.
    reflexivity.
Qed.

Lemma lower_fit : forall bindings selected layouts blocks,
  lower_places bindings selected layouts = Some blocks ->
  fit selected blocks.
Proof.
  intros bindings selected.
  induction selected as [|[index site] rest repeat];
    intros layouts blocks accepted.
  - destruct layouts; cbn in accepted; try discriminate.
    inversion accepted.
    reflexivity.
  - destruct layouts as [|[payload scratch] layouts];
      cbn in accepted; try discriminate.
    destruct (lower bindings index site payload scratch)
      as [block |] eqn:lowered; try discriminate.
    destruct (lower_places bindings rest layouts)
      as [tail |] eqn:more; try discriminate.
    inversion accepted.
    subst blocks.
    cbn.
    pose proof
      (lower_identity bindings index site payload scratch block lowered)
      as [same_index same_site].
    repeat split; try assumption.
    exact (repeat layouts tail more).
Qed.

Lemma lower_places_length : forall bindings selected layouts blocks,
  lower_places bindings selected layouts = Some blocks ->
  List.length blocks = List.length selected.
Proof.
  intros bindings selected.
  induction selected as [|[index site] rest repeat];
    intros layouts blocks accepted.
  - destruct layouts; cbn in accepted; try discriminate.
    inversion accepted.
    reflexivity.
  - destruct layouts as [|[payload scratch] layouts];
      cbn in accepted; try discriminate.
    destruct (lower bindings index site payload scratch); try discriminate.
    destruct (lower_places bindings rest layouts)
      as [tail |] eqn:more; try discriminate.
    inversion accepted.
    subst blocks.
    cbn.
    rewrite (repeat layouts tail more).
    reflexivity.
Qed.

Theorem lower_all_exact : forall bindings index locations layouts blocks,
  lower_all bindings index locations layouts = Some blocks ->
  blocks_exact index locations blocks.
Proof.
  intros bindings index locations layouts blocks accepted.
  unfold lower_all in accepted.
  unfold blocks_exact.
  exact (lower_fit bindings (places index locations) layouts blocks accepted).
Qed.

Theorem lower_all_length : forall bindings index locations layouts blocks,
  lower_all bindings index locations layouts = Some blocks ->
  List.length blocks = quota locations.
Proof.
  intros bindings index locations layouts blocks accepted.
  unfold lower_all in accepted.
  pose proof
    (lower_places_length bindings (places index locations) layouts blocks
      accepted) as exact_length.
  rewrite places_length in exact_length.
  exact exact_length.
Qed.

Definition stored_size (payload : value) : nat :=
  match payload with
  | VBool true => 4
  | VBool false => 5
  | VInt number => String.length (NilZero.string_of_int (Z.to_int number))
  | VBytes bytes => List.length bytes
  | _ => 0
  end.

Definition action_cost (selected : action) : nat :=
  match aa selected with
  | AWrite _ => base_cost (aa selected) + stored_size (av selected) / 32
  | _ => base_cost (aa selected)
  end.

Definition resolve (bindings : list binding) (selected : action)
    : option item :=
  if origin_ok (aa selected) (ao selected) then
    match aa selected, find (aa selected) bindings with
    | ARead _, Some (HState name typ) =>
        if scalar_value typ (av selected) then
          Some (Item selected (HLoad name (av selected)) Preserve 27)
        else None
    | AWrite _, Some (HState name typ) =>
        if scalar_value typ (av selected) then
          Some (Item selected (HStore name (av selected)) Journal
            (action_cost selected))
        else None
    | AEmit _, Some (HEvent name types) =>
        if Nat.leb (List.length types) 64 then
          match event_values types (av selected) with
          | Some values => Some (Item selected (HLog name values) Record 30)
          | None => None
          end
        else None
    | AFail _, Some (HFault name code message) =>
        match fault_values (av selected) with
        | Some values =>
            if Nat.leb (List.length values) 62 then
              Some (Item selected (HReject name code message values) Abort 33)
            else None
        | None => None
        end
    | _, _ => None
    end
  else None.

Definition continueb (selected : action) (rest : list action) : bool :=
  match aa selected, rest with
  | AFail _, _ :: _ => false
  | _, _ => true
  end.

Fixpoint plan (bindings : list binding) (selected : list action)
    : option (list item) :=
  match selected with
  | [] => Some []
  | head :: rest =>
      match resolve bindings head with
      | Some first =>
          if continueb head rest then
            match plan bindings rest with
            | Some tail => Some (first :: tail)
            | None => None
            end
          else None
      | None => None
      end
  end.

Definition sealed_plan (bindings : list binding) (selected : flow)
    (actions : list action) : option (list item) :=
  if seal_flow bindings selected then
    match consume_all (flow_locations selected) actions with
    | Some _ =>
        if traceb selected actions then plan bindings actions else None
    | None => None
    end
  else None.

Lemma consume_one_quota : forall selected locations next,
  consume_one selected locations = Some next ->
  S (quota next) = quota locations.
Proof.
  intros selected locations.
  induction locations as [|[expected count] rest repeat];
    intros next accepted; cbn in accepted; try discriminate.
  destruct (action_site selected expected) eqn:matched.
  - destruct count as [|remaining].
    + destruct (consume_one selected rest) as [tail |] eqn:used;
        try discriminate.
      inversion accepted.
      subst.
      cbn.
      specialize (repeat tail eq_refl).
      lia.
    + inversion accepted.
      subst.
      cbn.
      lia.
  - destruct (consume_one selected rest) as [tail |] eqn:used;
      try discriminate.
    inversion accepted.
    subst.
    cbn.
    specialize (repeat tail eq_refl).
    lia.
Qed.

Theorem consume_all_quota : forall actions locations next,
  consume_all locations actions = Some next ->
  List.length actions + quota next = quota locations.
Proof.
  induction actions as [|head rest repeat]; intros locations next accepted.
  - cbn in accepted.
    injection accepted as same.
    subst next.
    reflexivity.
  - cbn in accepted.
    destruct (consume_one head locations) as [middle |] eqn:used;
      try discriminate.
    pose proof (consume_one_quota head locations middle used) as one.
    pose proof (repeat middle next accepted) as more.
    cbn.
    lia.
Qed.

Theorem sealed_plan_static : forall bindings selected actions items,
  sealed_plan bindings selected actions = Some items ->
  seal_flow bindings selected = true /\
  traceb selected actions = true /\
  exists next, consume_all (flow_locations selected) actions = Some next.
Proof.
  intros bindings selected actions items accepted.
  unfold sealed_plan in accepted.
  destruct (seal_flow bindings selected) eqn:sealed; try discriminate.
  destruct (consume_all (flow_locations selected) actions) as [next |]
    eqn:consumed; try discriminate.
  destruct (traceb selected actions) eqn:traced; try discriminate.
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + exists next.
      reflexivity.
Qed.

Theorem sealed_plan_follows : forall bindings selected actions items,
  sealed_plan bindings selected actions = Some items ->
  follows selected actions.
Proof.
  intros bindings selected actions items accepted.
  destruct (sealed_plan_static _ _ _ _ accepted) as [_ [traced _]].
  apply traceb_sound.
  exact traced.
Qed.

Theorem sealed_plan_limit : forall bindings selected actions items,
  sealed_plan bindings selected actions = Some items ->
  List.length actions <= quota (flow_locations selected).
Proof.
  intros bindings selected actions items accepted.
  destruct (sealed_plan_static _ _ _ _ accepted)
    as [_ [_ [next consumed]]].
  pose proof (consume_all_quota actions (flow_locations selected) next consumed)
    as exact.
  lia.
Qed.

Lemma resolve_action : forall bindings selected found,
  resolve bindings selected = Some found -> ia found = selected.
Proof.
  intros bindings [atom payload origin] found accepted.
  unfold resolve in accepted.
  destruct atom; destruct origin; cbn in accepted;
    repeat
      match goal with
      | H : context [if ?test then _ else _] |- _ => destruct test eqn:?
      | H : context [match ?value with _ => _ end] |- _ => destruct value eqn:?
      end;
    try discriminate;
    inversion accepted;
    reflexivity.
Qed.

Lemma resolve_cost : forall bindings selected found,
  resolve bindings selected = Some found -> ic found = action_cost selected.
Proof.
  intros bindings [atom payload origin] found accepted.
  unfold resolve in accepted.
  destruct atom; destruct origin; cbn in accepted;
    repeat
      match goal with
      | H : context [if ?test then _ else _] |- _ => destruct test eqn:?
      | H : context [match ?value with _ => _ end] |- _ => destruct value eqn:?
      end;
    try discriminate;
    inversion accepted;
    reflexivity.
Qed.

Lemma resolve_no_close : forall bindings selected found,
  resolve bindings selected = Some found ->
  match aa selected with
  | AClose _ => False
  | _ => True
  end.
Proof.
  intros bindings [atom payload origin] found accepted.
  unfold resolve in accepted.
  destruct atom; cbn; try exact I.
  destruct origin; cbn in accepted; try discriminate.
  destruct (Nat.eqb n n0); try discriminate.
Qed.

Theorem plan_actions : forall bindings selected items,
  plan bindings selected = Some items -> map ia items = selected.
Proof.
  induction selected as [|head rest repeat]; intros items accepted.
  - cbn in accepted.
    inversion accepted.
    reflexivity.
  - cbn in accepted.
    destruct (resolve bindings head) as [first |] eqn:resolved;
      try discriminate.
    destruct (continueb head rest); try discriminate.
    destruct (plan bindings rest) as [tail |] eqn:planned;
      try discriminate.
    inversion accepted.
    subst.
    cbn.
    rewrite (resolve_action _ _ _ resolved).
    f_equal.
    apply repeat.
    reflexivity.
Qed.

Theorem plan_costs : forall bindings selected items,
  plan bindings selected = Some items ->
  map ic items = map action_cost selected.
Proof.
  induction selected as [|head rest repeat]; intros items accepted.
  - cbn in accepted.
    inversion accepted.
    reflexivity.
  - cbn in accepted.
    destruct (resolve bindings head) as [first |] eqn:resolved;
      try discriminate.
    destruct (continueb head rest); try discriminate.
    destruct (plan bindings rest) as [tail |] eqn:planned;
      try discriminate.
    inversion accepted.
    subst.
    cbn.
    rewrite (resolve_cost _ _ _ resolved).
    f_equal.
    apply repeat.
    reflexivity.
Qed.

Theorem sealed_plan_actions : forall bindings selected actions items,
  sealed_plan bindings selected actions = Some items ->
  map ia items = actions.
Proof.
  intros bindings selected actions items accepted.
  unfold sealed_plan in accepted.
  destruct (seal_flow bindings selected); try discriminate.
  destruct (consume_all (flow_locations selected) actions); try discriminate.
  destruct (traceb selected actions); try discriminate.
  exact (plan_actions bindings actions items accepted).
Qed.

Theorem sealed_plan_costs : forall bindings selected actions items,
  sealed_plan bindings selected actions = Some items ->
  map ic items = map action_cost actions.
Proof.
  intros bindings selected actions items accepted.
  unfold sealed_plan in accepted.
  destruct (seal_flow bindings selected); try discriminate.
  destruct (consume_all (flow_locations selected) actions); try discriminate.
  destruct (traceb selected actions); try discriminate.
  exact (plan_costs bindings actions items accepted).
Qed.

Theorem plan_no_close : forall bindings selected items,
  plan bindings selected = Some items ->
  Forall
    (fun action =>
      match aa action with
      | AClose _ => False
      | _ => True
      end)
    selected.
Proof.
  induction selected as [|head rest repeat]; intros items accepted.
  - constructor.
  - cbn in accepted.
    destruct (resolve bindings head) as [first |] eqn:resolved;
      try discriminate.
    destruct (continueb head rest); try discriminate.
    destruct (plan bindings rest) as [tail |] eqn:planned;
      try discriminate.
    constructor.
    + apply (resolve_no_close _ _ _ resolved).
    + apply repeat with (items := tail).
      reflexivity.
Qed.

Corollary plan_length : forall bindings selected items,
  plan bindings selected = Some items ->
  List.length items = List.length selected.
Proof.
  intros bindings selected items accepted.
  pose proof (plan_actions _ _ _ accepted) as exact.
  apply (f_equal (@List.length action)) in exact.
  now rewrite length_map in exact.
Qed.