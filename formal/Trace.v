(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import String.

Require Import Uni.
Require Import Comp.
Require Import Src.
Require Import Emit.
Require Import Rval.

Import ListNotations.

Inductive op : Type :=
| Load : lit -> op
| Stop : op.

Record frame : Type := Frame {
  fpc : nat;
  fop : op;
  freg : option lit;
  feffort : nat;
  fhalted : bool
}.

Record vm : Type := Vm {
  vreg : option lit;
  veffort : nat;
  vhalted : bool
}.

Fixpoint nats_eqb (left right : list nat) : bool :=
  match left, right with
  | [], [] => true
  | lhead :: ltail, rhead :: rtail =>
      Nat.eqb lhead rhead && nats_eqb ltail rtail
  | _, _ => false
  end.

Definition lit_eqb (left right : lit) : bool :=
  match left, right with
  | LBool lhs, LBool rhs => Bool.eqb lhs rhs
  | LInt lhs, LInt rhs => Z.eqb lhs rhs
  | LBytes lhs, LBytes rhs => nats_eqb lhs rhs
  | LData lhs, LData rhs => Rval.rval_eqb lhs rhs
  | _, _ => false
  end.

Definition init : vm := Vm None 0 false.

Definition advance (state : vm) (event : frame) : option vm :=
  match state, event with
  | Vm None 0 false, Frame pc (Load value) (Some out) effort false =>
      if Nat.eqb pc 0 && Nat.eqb effort 1 && lit_eqb value out
      then Some (Vm (Some out) 1 false)
      else None
  | Vm (Some value) 1 false, Frame pc Stop (Some out) effort true =>
      if Nat.eqb pc 1 && Nat.eqb effort 2 && lit_eqb value out
      then Some (Vm (Some out) 2 true)
      else None
  | _, _ => None
  end.

Fixpoint replay (state : vm) (events : list frame) : option vm :=
  match events with
  | [] => Some state
  | event :: rest =>
      match advance state event with
      | Some next => replay next rest
      | None => None
      end
  end.

Definition trace (value : lit) : list frame := [
  Frame 0 (Load value) (Some value) 1 false;
  Frame 1 Stop (Some value) 2 true
].

Definition source_trace (source : string) : option (list frame) :=
  match source_emit source with
  | Some value => Some (trace value)
  | None => None
  end.

Lemma nats_eqb_refl : forall values, nats_eqb values values = true.
Proof.
  induction values as [|head tail IH]; simpl.
  - reflexivity.
  - rewrite Nat.eqb_refl, IH.
    reflexivity.
Qed.

Lemma lit_eqb_refl : forall value, lit_eqb value value = true.
Proof.
  intros value.
  destruct value; simpl.
  - destruct b; reflexivity.
  - apply Z.eqb_refl.
  - apply nats_eqb_refl.
  - apply Rval.rval_eqb_refl.
Qed.

Theorem trace_replay : forall value,
  replay init (trace value) = Some (Vm (Some value) 2 true).
Proof.
  intros value.
  unfold init, trace.
  simpl.
  rewrite lit_eqb_refl.
  simpl.
  rewrite lit_eqb_refl.
  reflexivity.
Qed.

Theorem source_trace_sound : forall source events,
  source_trace source = Some events ->
  exists value image out,
    events = trace value /\
    Src.compile source = Some image /\
    Comp.iins image = [] /\
    Comp.irow image = [] /\
    run_fuel (rsteps (Comp.icost image)) [] (Comp.iterm image) =
      Done out [] /\
    rp out = [] /\
    rep (Comp.ityp image) (rv out) value /\
    replay init events = Some (Vm (Some value) 2 true).
Proof.
  intros source events accepted.
  unfold source_trace in accepted.
  destruct (source_emit source) as [value |] eqn:emitted; try discriminate.
  inversion accepted; subst events.
  destruct (source_emit_sound source value emitted)
    as [image [compiled image_emitted]].
  destruct (emit_sound image value image_emitted)
    as [no_inputs [no_effects [out [ran [no_plan represented]]]]].
  exists value, image, out.
  repeat split; try assumption.
  apply trace_replay.
Qed.

Theorem source_trace_unique : forall source left right,
  source_trace source = Some left -> source_trace source = Some right ->
  left = right.
Proof.
  intros source left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.