(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Require Import Uni.
Require Import Dec.
Require Import DecRel.
Require Import DecComp.
Require Import DecSound.
Require Import Surf.
Require Import Fin.
Require Import Low.

Import ListNotations.

Fixpoint oval (count : nat) (seed : stm) (item : sbind) (body : stm) : stm :=
  match count with
  | O => seed
  | S rest => SLet item (oval rest seed item body) body
  end.

Definition obody (item : sbind) (body : stm) : option chk :=
  match pcheck [item] body with
  | Some (typ, row, cost, next) =>
      if ty_eqb typ (sty item) then Some (typ, row, cost, next) else None
  | None => None
  end.

Definition ofit (count : nat) (seed body : stm) : bool :=
  let node_count := fin_nodes seed + count * (fin_nodes body + 1) in
  let depth_count :=
    match count with
    | O => fin_depth seed
    | S _ => count + Nat.max (fin_depth seed) (fin_depth body)
    end
  in
  fin_valid seed && fin_valid body && fin_fit node_count depth_count.

Definition oterm (count : nat) (seed : stm) (item : sbind) (body : stm)
    : option stm :=
  match obody item body with
  | Some _ =>
      if ofit count seed body
      then Some (oval count seed item body)
      else None
  | None => None
  end.

Definition ocheck (inputs : list sbind) (count : nat) (seed : stm)
    (item : sbind) (body : stm) : option chk :=
  match oterm count seed item body with
  | Some term =>
      match pcheck inputs term with
      | Some (typ, row, cost, next) =>
          if ty_eqb typ (sty item)
          then Some (typ, row, cost, next)
          else None
      | None => None
      end
  | None => None
  end.

Theorem oval_zero : forall seed item body,
  oval 0 seed item body = seed.
Proof.
  reflexivity.
Qed.

Theorem oval_succ : forall count seed item body,
  oval (S count) seed item body = SLet item (oval count seed item body) body.
Proof.
  reflexivity.
Qed.

Theorem oval_add : forall left right seed item body,
  oval (left + right) seed item body =
    oval right (oval left seed item body) item body.
Proof.
  intros left right seed item body.
  induction right as [| right IH].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r. simpl. rewrite IH. reflexivity.
Qed.

Theorem onodes : forall count seed item body,
  fin_nodes (oval count seed item body) =
  fin_nodes seed + count * (fin_nodes body + 1).
Proof.
  induction count as [| count IH]; intros seed item body; simpl.
  - lia.
  - rewrite IH. nia.
Qed.

Theorem odepth : forall count seed item body,
  fin_depth (oval count seed item body) =
  match count with
  | O => fin_depth seed
  | S _ => count + Nat.max (fin_depth seed) (fin_depth body)
  end.
Proof.
  induction count as [| count IH]; intros seed item body; simpl.
  - reflexivity.
  - destruct count as [| count].
    + reflexivity.
    + rewrite IH.
      rewrite Nat.max_l by lia.
      lia.
Qed.

Theorem ofit_valid : forall count seed item body,
  ofit count seed body = true ->
  fin_valid (oval count seed item body) = true.
Proof.
  intros count seed item body accepted.
  unfold ofit in accepted.
  apply andb_true_iff in accepted as [_ fit_ok].
  unfold fin_valid.
  rewrite onodes, odepth.
  exact fit_ok.
Qed.

Theorem oterm_valid : forall count seed item body term,
  oterm count seed item body = Some term ->
  fin_valid term = true.
Proof.
  intros count seed item body term built.
  unfold oterm in built.
  destruct (obody item body); try discriminate.
  destruct (ofit count seed body) eqn:fit_ok; try discriminate.
  inversion built; subst.
  apply ofit_valid.
  exact fit_ok.
Qed.

Theorem obody_type : forall item body typ row cost next,
  obody item body = Some (typ, row, cost, next) ->
  typ = sty item.
Proof.
  intros item body typ row cost next accepted.
  unfold obody in accepted.
  destruct (pcheck [item] body) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (sty item)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  reflexivity.
Qed.

Theorem obody_sound : forall item body row cost next,
  obody item body = Some (sty item, row, cost, next) ->
  pcheck [item] body = Some (sty item, row, cost, next).
Proof.
  intros item body row cost next accepted.
  unfold obody in accepted.
  destruct (pcheck [item] body) as [[[[typ brow] bcost] bnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb typ (sty item)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  subst.
  inversion accepted; subst.
  assumption.
Qed.

Theorem obody_complete : forall item body row cost next,
  pcheck [item] body = Some (sty item, row, cost, next) ->
  obody item body = Some (sty item, row, cost, next).
Proof.
  intros item body row cost next checked.
  unfold obody.
  rewrite checked, ty_eqb_refl.
  reflexivity.
Qed.

Theorem oterm_exact : forall count seed item body row cost next,
  obody item body = Some (sty item, row, cost, next) ->
  ofit count seed body = true ->
  oterm count seed item body = Some (oval count seed item body).
Proof.
  intros count seed item body row cost next body_ok fit_ok.
  unfold oterm.
  rewrite body_ok, fit_ok.
  reflexivity.
Qed.

Theorem oterm_zero : forall seed item body row cost next,
  obody item body = Some (sty item, row, cost, next) ->
  ofit 0 seed body = true ->
  oterm 0 seed item body = Some seed.
Proof.
  intros seed item body row cost next body_ok fit_ok.
  rewrite (oterm_exact 0 seed item body row cost next body_ok fit_ok).
  reflexivity.
Qed.

Theorem oterm_succ : forall count seed item body row cost next,
  obody item body = Some (sty item, row, cost, next) ->
  ofit (S count) seed body = true ->
  oterm (S count) seed item body =
    Some (SLet item (oval count seed item body) body).
Proof.
  intros count seed item body row cost next body_ok fit_ok.
  rewrite (oterm_exact (S count) seed item body row cost next body_ok fit_ok).
  reflexivity.
Qed.

Theorem ocheck_type : forall inputs count seed item body typ row cost next,
  ocheck inputs count seed item body = Some (typ, row, cost, next) ->
  typ = sty item.
Proof.
  intros inputs count seed item body typ row cost next accepted.
  unfold ocheck in accepted.
  destruct (oterm count seed item body) as [term |]; try discriminate.
  destruct (pcheck inputs term) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (sty item)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  reflexivity.
Qed.

Theorem ocheck_sound : forall inputs count seed item body typ row cost next,
  ocheck inputs count seed item body = Some (typ, row, cost, next) ->
  exists brow bcost bnext term,
    obody item body = Some (sty item, brow, bcost, bnext) /\
    ofit count seed body = true /\
    oterm count seed item body = Some term /\
    pcheck inputs term = Some (sty item, row, cost, next) /\
    typ = sty item.
Proof.
  intros inputs count seed item body typ row cost next accepted.
  unfold ocheck in accepted.
  destruct (oterm count seed item body) as [term |] eqn:built;
    try discriminate.
  unfold oterm in built.
  destruct (obody item body) as [[[[btyp brow] bcost] bnext] |]
    eqn:body_ok; try discriminate.
  destruct (ofit count seed body) eqn:fit_ok; try discriminate.
  destruct (pcheck inputs term) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (sty item)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  inversion built; subst.
  pose proof (obody_type item body btyp brow bcost bnext body_ok)
    as body_type.
  subst btyp.
  exists brow, bcost, bnext, (oval count seed item body).
  repeat split; assumption.
Qed.

Theorem ocheck_complete : forall inputs count seed item body row cost next
    brow bcost bnext term,
  obody item body = Some (sty item, brow, bcost, bnext) ->
  oterm count seed item body = Some term ->
  pcheck inputs term = Some (sty item, row, cost, next) ->
  ocheck inputs count seed item body =
    Some (sty item, row, cost, next).
Proof.
  intros inputs count seed item body row cost next brow bcost bnext term
    body_ok built checked.
  unfold ocheck.
  rewrite built, checked, ty_eqb_refl.
  reflexivity.
Qed.