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

Fixpoint kval (count keep : nat) (typ : ty) (seed : stm)
    (item : sbind) (body : stm) : stm :=
  match count with
  | O => SVnil typ
  | S rest =>
      SLet (SBind keep MM typ) (SLet item seed body)
        (SVcat (SVcons (SVar keep) (SVnil typ))
          (kval rest keep typ (SVar keep) item body))
  end.

Definition kout (count keep : nat) (seed : stm)
    (item : sbind) (body : stm) : stm :=
  match count with
  | O => SLet (SBind keep M0 (sty item)) seed (SVnil (sty item))
  | S _ => kval count keep (sty item) seed item body
  end.

Definition kbody (item : sbind) (body : stm) : option chk :=
  if data_b (sty item) then
    match pcheck [item] body with
    | Some (typ, row, cost, next) =>
        if ty_eqb typ (sty item)
        then Some (typ, row, cost, next)
        else None
    | None => None
    end
  else None.

Fixpoint kdepth (count seed_depth body_depth : nat) : nat :=
  match count with
  | O => 0
  | S rest =>
      S (Nat.max (S (Nat.max seed_depth body_depth))
        (S (Nat.max 1 (kdepth rest 0 body_depth))))
  end.

Definition kfit (count : nat) (seed body : stm) : bool :=
  let node_count :=
    match count with
    | O => fin_nodes seed + 2
    | S _ => fin_nodes seed + count * (fin_nodes body + 6)
    end
  in
  let depth_count :=
    match count with
    | O => S (fin_depth seed)
    | S _ => kdepth count (fin_depth seed) (fin_depth body)
    end
  in
  fin_valid seed && fin_valid body && fin_fit node_count depth_count.

Definition kterm (keep count : nat) (seed : stm)
    (item : sbind) (body : stm) : option stm :=
  match kbody item body with
  | Some _ =>
      if kfit count seed body then
        if Nat.eqb keep (sname item) then None
        else if has keep seed then None
        else if has keep body then None
        else Some (kout count keep seed item body)
      else None
  | None => None
  end.

Definition kcheck (inputs : list sbind) (keep count : nat)
    (seed : stm) (item : sbind) (body : stm) : option chk :=
  match kterm keep count seed item body with
  | Some term =>
      match pcheck inputs term with
      | Some (typ, row, cost, next) =>
          if ty_eqb typ (TVec count (sty item))
          then Some (typ, row, cost, next)
          else None
      | None => None
      end
  | None => None
  end.

Theorem kval_nodes : forall count keep typ seed item body,
  fin_nodes (kval count keep typ seed item body) =
  match count with
  | O => 1
  | S _ => fin_nodes seed + count * (fin_nodes body + 6)
  end.
Proof.
  induction count as [| count IH]; intros keep typ seed item body; simpl.
  - reflexivity.
  - rewrite IH.
    destruct count; simpl; nia.
Qed.

Theorem kval_depth : forall count keep typ seed item body,
  fin_depth (kval count keep typ seed item body) =
    kdepth count (fin_depth seed) (fin_depth body).
Proof.
  induction count as [| count IH]; intros keep typ seed item body; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Theorem kout_nodes : forall count keep seed item body,
  fin_nodes (kout count keep seed item body) =
  match count with
  | O => fin_nodes seed + 2
  | S _ => fin_nodes seed + count * (fin_nodes body + 6)
  end.
Proof.
  intros count keep seed item body.
  destruct count as [| count].
  - simpl. lia.
  - change (fin_nodes (kval (S count) keep (sty item) seed item body) =
      fin_nodes seed + S count * (fin_nodes body + 6)).
    rewrite kval_nodes.
    reflexivity.
Qed.

Theorem kout_depth : forall count keep seed item body,
  fin_depth (kout count keep seed item body) =
  match count with
  | O => S (fin_depth seed)
  | S _ => kdepth count (fin_depth seed) (fin_depth body)
  end.
Proof.
  intros count keep seed item body.
  destruct count as [| count].
  - simpl. rewrite Nat.max_0_r. reflexivity.
  - change (fin_depth (kval (S count) keep (sty item) seed item body) =
      kdepth (S count) (fin_depth seed) (fin_depth body)).
    apply kval_depth.
Qed.

Theorem kfit_valid : forall count keep seed item body,
  kfit count seed body = true ->
  fin_valid (kout count keep seed item body) = true.
Proof.
  intros count keep seed item body accepted.
  unfold kfit in accepted.
  apply andb_true_iff in accepted as [_ fit_ok].
  unfold fin_valid.
  rewrite kout_nodes, kout_depth.
  exact fit_ok.
Qed.

Theorem kbody_type : forall item body typ row cost next,
  kbody item body = Some (typ, row, cost, next) ->
  typ = sty item.
Proof.
  intros item body typ row cost next accepted.
  unfold kbody in accepted.
  destruct (data_b (sty item)); try discriminate.
  destruct (pcheck [item] body) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (sty item)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  reflexivity.
Qed.

Theorem kbody_sound : forall item body row cost next,
  kbody item body = Some (sty item, row, cost, next) ->
  data_b (sty item) = true /\
  pcheck [item] body = Some (sty item, row, cost, next).
Proof.
  intros item body row cost next accepted.
  unfold kbody in accepted.
  destruct (data_b (sty item)) eqn:data_ok; try discriminate.
  destruct (pcheck [item] body) as [[[[typ brow] bcost] bnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb typ (sty item)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  subst.
  inversion accepted; subst.
  split; reflexivity.
Qed.

Theorem kbody_complete : forall item body row cost next,
  data_b (sty item) = true ->
  pcheck [item] body = Some (sty item, row, cost, next) ->
  kbody item body = Some (sty item, row, cost, next).
Proof.
  intros item body row cost next data_ok checked.
  unfold kbody.
  rewrite data_ok, checked, ty_eqb_refl.
  reflexivity.
Qed.

Theorem kterm_valid : forall keep count seed item body term,
  kterm keep count seed item body = Some term ->
  fin_valid term = true.
Proof.
  intros keep count seed item body term built.
  unfold kterm in built.
  destruct (kbody item body); try discriminate.
  destruct (kfit count seed body) eqn:fit_ok; try discriminate.
  destruct (Nat.eqb keep (sname item)); try discriminate.
  destruct (has keep seed); try discriminate.
  destruct (has keep body); try discriminate.
  inversion built; subst.
  apply kfit_valid.
  exact fit_ok.
Qed.

Theorem kterm_exact : forall keep count seed item body row cost next,
  kbody item body = Some (sty item, row, cost, next) ->
  kfit count seed body = true ->
  keep <> sname item ->
  has keep seed = false ->
  has keep body = false ->
  kterm keep count seed item body =
    Some (kout count keep seed item body).
Proof.
  intros keep count seed item body row cost next body_ok fit_ok
    apart seed_ok term_ok.
  unfold kterm.
  rewrite body_ok, fit_ok.
  apply Nat.eqb_neq in apart.
  rewrite apart, seed_ok, term_ok.
  reflexivity.
Qed.

Theorem kterm_empty : forall keep seed item body row cost next,
  kbody item body = Some (sty item, row, cost, next) ->
  kfit 0 seed body = true ->
  keep <> sname item ->
  has keep seed = false ->
  has keep body = false ->
  kterm keep 0 seed item body =
    Some (SLet (SBind keep M0 (sty item)) seed (SVnil (sty item))).
Proof.
  intros keep seed item body row cost next body_ok fit_ok
    apart seed_ok term_ok.
  rewrite (kterm_exact keep 0 seed item body row cost next body_ok fit_ok
    apart seed_ok term_ok).
  reflexivity.
Qed.

Theorem kterm_succ : forall keep count seed item body row cost next,
  kbody item body = Some (sty item, row, cost, next) ->
  kfit (S count) seed body = true ->
  keep <> sname item ->
  has keep seed = false ->
  has keep body = false ->
  kterm keep (S count) seed item body =
    Some (kval (S count) keep (sty item) seed item body).
Proof.
  intros keep count seed item body row cost next body_ok fit_ok
    apart seed_ok term_ok.
  rewrite (kterm_exact keep (S count) seed item body row cost next
    body_ok fit_ok apart seed_ok term_ok).
  reflexivity.
Qed.

Theorem kcheck_type : forall inputs keep count seed item body
    typ row cost next,
  kcheck inputs keep count seed item body = Some (typ, row, cost, next) ->
  typ = TVec count (sty item).
Proof.
  intros inputs keep count seed item body typ row cost next accepted.
  unfold kcheck in accepted.
  destruct (kterm keep count seed item body) as [term |]; try discriminate.
  destruct (pcheck inputs term) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (TVec count (sty item))) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  reflexivity.
Qed.

Theorem kcheck_sound : forall inputs keep count seed item body
    typ row cost next,
  kcheck inputs keep count seed item body = Some (typ, row, cost, next) ->
  exists brow bcost bnext term,
    kbody item body = Some (sty item, brow, bcost, bnext) /\
    kfit count seed body = true /\
    kterm keep count seed item body = Some term /\
    pcheck inputs term = Some (TVec count (sty item), row, cost, next) /\
    typ = TVec count (sty item).
Proof.
  intros inputs keep count seed item body typ row cost next accepted.
  unfold kcheck in accepted.
  destruct (kterm keep count seed item body) as [term |] eqn:built;
    try discriminate.
  unfold kterm in built.
  destruct (kbody item body) as [[[[btyp brow] bcost] bnext] |]
    eqn:body_ok; try discriminate.
  destruct (kfit count seed body) eqn:fit_ok; try discriminate.
  destruct (Nat.eqb keep (sname item)); try discriminate.
  destruct (has keep seed); try discriminate.
  destruct (has keep body); try discriminate.
  destruct (pcheck inputs term) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (TVec count (sty item))) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  inversion built; subst.
  pose proof (kbody_type item body btyp brow bcost bnext body_ok)
    as body_type.
  subst btyp.
  exists brow, bcost, bnext, (kout count keep seed item body).
  repeat split; assumption.
Qed.

Theorem kcheck_complete : forall inputs keep count seed item body
    row cost next brow bcost bnext term,
  kbody item body = Some (sty item, brow, bcost, bnext) ->
  kterm keep count seed item body = Some term ->
  pcheck inputs term = Some (TVec count (sty item), row, cost, next) ->
  kcheck inputs keep count seed item body =
    Some (TVec count (sty item), row, cost, next).
Proof.
  intros inputs keep count seed item body row cost next brow bcost bnext term
    body_ok built checked.
  unfold kcheck.
  rewrite built, checked, ty_eqb_refl.
  reflexivity.
Qed.