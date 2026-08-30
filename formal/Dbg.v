(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.

Require Import Uni.
Require Import Emit.
Require Import Trace.
Require Import Mach.

Import ListNotations.

Inductive point : Type :=
| BPc : nat -> point
| BLine : nat -> point.

Definition hit_b (pc line : nat) (value : point) : bool :=
  match value with
  | BPc spot => Nat.eqb spot pc
  | BLine spot => Nat.eqb spot line
  end.

Fixpoint hits_b (pc line : nat) (values : list point) : bool :=
  match values with
  | [] => false
  | value :: rest => hit_b pc line value || hits_b pc line rest
  end.

Record cfg : Type := Config {
  dcap : nat;
  dstops : list point;
  dexpect : option lit
}.

Inductive choice : Type :=
| DStep
| DPause
| DLimit.

Definition decide (config : cfg) (skip : option nat) (seen pc line : nat)
    : choice :=
  if Nat.leb (dcap config) seen then DLimit
  else
    match skip with
    | Some past =>
        if Nat.leb seen past then DStep
        else if hits_b pc line (dstops config) then DPause else DStep
    | None => if hits_b pc line (dstops config) then DPause else DStep
    end.

Definition check (config : cfg) (actual : lit) : bool :=
  match dexpect config with
  | None => true
  | Some wanted => Trace.lit_eqb wanted actual
  end.

Lemma hits_b_sound : forall pc line values,
  hits_b pc line values = true ->
  exists value, In value values /\ hit_b pc line value = true.
Proof.
  intros pc line values.
  induction values as [|value rest IH]; simpl; intros accepted; try discriminate.
  rewrite Bool.orb_true_iff in accepted.
  destruct accepted as [head | tail].
  - exists value.
    split; [left; reflexivity | exact head].
  - destruct (IH tail) as [found [inside hit]].
    exists found.
    split; [right; exact inside | exact hit].
Qed.

Theorem decide_limit : forall config skip seen pc line,
  dcap config <= seen -> decide config skip seen pc line = DLimit.
Proof.
  intros config skip seen pc line reached.
  unfold decide.
  apply Nat.leb_le in reached.
  rewrite reached.
  reflexivity.
Qed.

Theorem decide_pause : forall config skip seen pc line,
  decide config skip seen pc line = DPause ->
  exists value, In value (dstops config) /\ hit_b pc line value = true.
Proof.
  intros config skip seen pc line paused.
  unfold decide in paused.
  destruct (Nat.leb (dcap config) seen); try discriminate.
  destruct skip as [past |].
  - destruct (Nat.leb seen past); try discriminate.
    destruct (hits_b pc line (dstops config)) eqn:hit; try discriminate.
    apply hits_b_sound.
    exact hit.
  - destruct (hits_b pc line (dstops config)) eqn:hit; try discriminate.
    apply hits_b_sound.
    exact hit.
Qed.

Theorem check_sound : forall config actual,
  check config actual = true ->
  dexpect config = None \/
  exists wanted, dexpect config = Some wanted /\ wanted = actual.
Proof.
  intros config actual accepted.
  unfold check in accepted.
  destruct (dexpect config) as [wanted |] eqn:expected.
  - right.
    exists wanted.
    split; [reflexivity |].
    apply Mach.lit_eqb_eq.
    exact accepted.
  - left.
    reflexivity.
Qed.