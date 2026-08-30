(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Uni.
Require Import Dec.
Require Import DecComp.
Require Import DecSound.
Require Import Lim.

Import ListNotations.

Inductive perm : Type :=
| PNil
| PStep
| PClose
| PBoth.

Inductive pop : Type :=
| OStep
| OClose.

Definition phas (value : perm) (op : pop) : bool :=
  match value, op with
  | PStep, OStep | PBoth, OStep => true
  | PClose, OClose | PBoth, OClose => true
  | _, _ => false
  end.

Definition ple (left right : perm) : bool :=
  implb (phas left OStep) (phas right OStep)
    && implb (phas left OClose) (phas right OClose).

Definition pmeet (left right : perm) : perm :=
  match phas left OStep && phas right OStep,
      phas left OClose && phas right OClose with
  | false, false => PNil
  | true, false => PStep
  | false, true => PClose
  | true, true => PBoth
  end.

Definition pcut (source target : perm) : option perm :=
  if ple target source then Some target else None.

Theorem ple_refl : forall value, ple value value = true.
Proof.
  destruct value; reflexivity.
Qed.

Theorem ple_antisym : forall left right,
  ple left right = true ->
  ple right left = true ->
  left = right.
Proof.
  destruct left, right; simpl; intros; try discriminate; reflexivity.
Qed.

Theorem ple_trans : forall first second third,
  ple first second = true ->
  ple second third = true ->
  ple first third = true.
Proof.
  destruct first, second, third; simpl; intros; try discriminate; reflexivity.
Qed.

Theorem ple_has : forall left right op,
  ple left right = true ->
  phas left op = true ->
  phas right op = true.
Proof.
  destruct left, right, op; simpl; intros; try discriminate; reflexivity.
Qed.

Theorem ple_nil : forall value, ple PNil value = true.
Proof.
  destruct value; reflexivity.
Qed.

Theorem ple_both : forall value, ple value PBoth = true.
Proof.
  destruct value; reflexivity.
Qed.

Theorem pmeet_left : forall left right,
  ple (pmeet left right) left = true.
Proof.
  destruct left, right; reflexivity.
Qed.

Theorem pmeet_right : forall left right,
  ple (pmeet left right) right = true.
Proof.
  destruct left, right; reflexivity.
Qed.

Theorem pmeet_greatest : forall value left right,
  ple value left = true ->
  ple value right = true ->
  ple value (pmeet left right) = true.
Proof.
  destruct value, left, right; simpl; intros; try discriminate; reflexivity.
Qed.

Theorem pmeet_comm : forall left right,
  pmeet left right = pmeet right left.
Proof.
  destruct left, right; reflexivity.
Qed.

Theorem pmeet_idem : forall value,
  pmeet value value = value.
Proof.
  destruct value; reflexivity.
Qed.

Theorem pmeet_assoc : forall first second third,
  pmeet first (pmeet second third) = pmeet (pmeet first second) third.
Proof.
  destruct first, second, third; reflexivity.
Qed.

Theorem pcut_sound : forall source target out,
  pcut source target = Some out ->
  out = target /\ ple target source = true.
Proof.
  intros source target out H. unfold pcut in H.
  destruct (ple target source) eqn:Hle; try discriminate.
  inversion H. auto.
Qed.

Theorem pcut_no_gain : forall source target out op,
  pcut source target = Some out ->
  phas out op = true ->
  phas source op = true.
Proof.
  intros source target out op Hcut Hhas.
  destruct (pcut_sound source target out Hcut) as [Hout Hle].
  subst out. eapply ple_has; eauto.
Qed.

Definition pset := list (nat * perm).

Definition pmax : nat := 64 * 64.

Fixpoint pfind (kind : nat) (set : pset) : option perm :=
  match set with
  | [] => None
  | (key, value) :: rest =>
      if Nat.eqb kind key then Some value else pfind kind rest
  end.

Fixpoint phas_kind (kind : nat) (set : pset) : bool :=
  match set with
  | [] => false
  | (key, _) :: rest => Nat.eqb kind key || phas_kind kind rest
  end.

Fixpoint puniq (set : pset) : bool :=
  match set with
  | [] => true
  | (kind, _) :: rest => negb (phas_kind kind rest) && puniq rest
  end.

Fixpoint pkinds (set : pset) : bool :=
  match set with
  | [] => true
  | (kind, _) :: rest => Nat.leb kind lim && pkinds rest
  end.

Definition pset_b (set : pset) : bool :=
  Nat.leb (length set) pmax && puniq set && pkinds set.

Definition patom (set : pset) (item : atom) : bool :=
  match item with
  | AWrite kind =>
      match pfind kind set with
      | Some value => phas value OStep
      | None => false
      end
  | AClose kind =>
      match pfind kind set with
      | Some value => phas value OClose
      | None => false
      end
  | ARead _ | AEmit _ | AFail _ => true
  end.

Definition prow (set : pset) (row : list atom) : bool :=
  forallb (patom set) row.

Definition ppcheck (set : pset) (gamma : ctx) (term : tm) : option chk :=
  if pset_b set then
    match checkb gamma term with
    | Some (typ, row, cost, next) =>
        if prow set row then Some (typ, row, cost, next) else None
    | None => None
    end
  else None.

Theorem ppcheck_sound : forall set gamma term typ row cost next,
  ppcheck set gamma term = Some (typ, row, cost, next) ->
  pset_b set = true /\
  prow set row = true /\
  check gamma term typ row cost next.
Proof.
  intros set gamma term typ row cost next H.
  unfold ppcheck in H.
  destruct (pset_b set) eqn:Hset; try discriminate.
  destruct (checkb gamma term) as [out |] eqn:Hcheck; try discriminate.
  destruct out as [[[out_ty out_row] out_cost] out_next].
  destruct (prow set out_row) eqn:Hrow; try discriminate.
  inversion H; subst.
  repeat split; try assumption.
  eapply checkb_sound. exact Hcheck.
Qed.

Theorem ppcheck_complete : forall set gamma term typ row cost next,
  pset_b set = true ->
  prow set row = true ->
  check gamma term typ row cost next ->
  ppcheck set gamma term = Some (typ, row, cost, next).
Proof.
  intros set gamma term typ row cost next Hset Hrow Hcheck.
  unfold ppcheck. rewrite Hset.
  rewrite (checkb_complete _ _ _ _ _ _ Hcheck), Hrow.
  reflexivity.
Qed.