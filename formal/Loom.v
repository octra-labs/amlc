(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.

Require Import Uni.
Require Import Dec.
Require Import DecRel.
Require Import DecComp.
Require Import DecSound.
Require Import Surf.
Require Import Fin.
Require Import Low.

Import ListNotations.

Fixpoint lvals (count pos : nat) (item : sbind) (body : stm) : list stm :=
  match count with
  | O => []
  | S rest =>
      SLet item (SK (VInt (Z.of_nat pos)) TInt) body ::
        lvals rest (S pos) item body
  end.

Fixpoint lvec (out : ty) (values : list stm) : stm :=
  match values with
  | [] => SVnil out
  | value :: rest => SVcons value (lvec out rest)
  end.

Definition lbody (item : sbind) (out : ty) (body : stm) : option chk :=
  if ty_eqb (sty item) TInt && data_b out then
    match pcheck [item] body with
    | Some (typ, row, cost, next) =>
        if ty_eqb typ out then Some (out, row, cost, next) else None
    | None => None
    end
  else None.

Definition lfit (count : nat) (body : stm) : bool :=
  let node_count := 1 + count * (fin_nodes body + 2) in
  let depth_count :=
    match count with
    | O => 0
    | S _ => Nat.max 2 (2 + fin_depth body)
    end
  in
  fin_valid body && fin_fit node_count depth_count.

Definition lterm (count : nat) (out : ty) (item : sbind) (body : stm)
    : option stm :=
  match lbody item out body with
  | Some _ =>
      if lfit count body
      then Some (lvec out (lvals count 0 item body))
      else None
  | None => None
  end.

Definition lcheck (inputs : list sbind) (count : nat) (out : ty)
    (item : sbind) (body : stm) : option chk :=
  match lterm count out item body with
  | Some term =>
      match pcheck inputs term with
      | Some (typ, row, cost, next) =>
          if ty_eqb typ (TVec count out)
          then Some (typ, row, cost, next)
          else None
      | None => None
      end
  | None => None
  end.

Theorem lbody_type : forall item out body typ row cost next,
  lbody item out body = Some (typ, row, cost, next) ->
  typ = out.
Proof.
  intros item out body typ row cost next accepted.
  unfold lbody in accepted.
  destruct (ty_eqb (sty item) TInt && data_b out); try discriminate.
  destruct (pcheck [item] body) as [[[[got grow] gcost] gnext] |];
    try discriminate.
  destruct (ty_eqb got out); try discriminate.
  inversion accepted.
  reflexivity.
Qed.

Theorem lvals_length : forall count pos item body,
  length (lvals count pos item body) = count.
Proof.
  induction count as [| count IH]; intros pos item body; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Theorem lnodes : forall count pos out item body,
  fin_nodes (lvec out (lvals count pos item body)) =
  1 + count * (fin_nodes body + 2).
Proof.
  induction count as [| count IH]; intros pos out item body; simpl.
  - reflexivity.
  - rewrite IH. nia.
Qed.

Theorem ldepth : forall count pos out item body,
  fin_depth (lvec out (lvals count pos item body)) =
  match count with
  | O => 0
  | S _ => Nat.max 2 (2 + fin_depth body)
  end.
Proof.
  induction count as [| count IH]; intros pos out item body; simpl.
  - reflexivity.
  - destruct count as [| count].
    + reflexivity.
    + rewrite IH.
      assert (same : Nat.max 2 (2 + fin_depth body) =
        2 + fin_depth body) by (apply Nat.max_r; lia).
      rewrite same.
      change (Nat.max (2 + fin_depth body) (2 + fin_depth body) =
        2 + fin_depth body).
      apply Nat.max_id.
Qed.

Theorem lfit_valid : forall count out item body,
  lfit count body = true ->
  fin_valid (lvec out (lvals count 0 item body)) = true.
Proof.
  intros count out item body accepted.
  unfold lfit in accepted.
  apply andb_true_iff in accepted as [_ fit_ok].
  unfold fin_valid.
  rewrite lnodes, ldepth.
  exact fit_ok.
Qed.

Theorem lterm_valid : forall count out item body term,
  lterm count out item body = Some term ->
  fin_valid term = true.
Proof.
  intros count out item body term built.
  unfold lterm in built.
  destruct (lbody item out body); try discriminate.
  destruct (lfit count body) eqn:fit_ok; try discriminate.
  inversion built; subst.
  apply lfit_valid.
  exact fit_ok.
Qed.

Theorem lbody_sound : forall item out body row cost next,
  lbody item out body = Some (out, row, cost, next) ->
  sty item = TInt /\
  data_b out = true /\
  pcheck [item] body = Some (out, row, cost, next).
Proof.
  intros item out body row cost next accepted.
  unfold lbody in accepted.
  destruct (ty_eqb (sty item) TInt && data_b out) eqn:data_ok;
    try discriminate.
  apply andb_true_iff in data_ok as [item_ok out_ok].
  apply ty_eqb_eq in item_ok.
  destruct (pcheck [item] body) as [[[[typ brow] bcost] bnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb typ out) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  subst.
  inversion accepted; subst.
  repeat split; assumption.
Qed.

Theorem lbody_complete : forall item out body row cost next,
  sty item = TInt ->
  data_b out = true ->
  pcheck [item] body = Some (out, row, cost, next) ->
  lbody item out body = Some (out, row, cost, next).
Proof.
  intros item out body row cost next item_ok out_ok checked.
  unfold lbody.
  rewrite item_ok, ty_eqb_refl, out_ok, checked, ty_eqb_refl.
  reflexivity.
Qed.

Theorem lterm_exact : forall count out item body row cost next,
  lbody item out body = Some (out, row, cost, next) ->
  lfit count body = true ->
  lterm count out item body = Some (lvec out (lvals count 0 item body)).
Proof.
  intros count out item body row cost next body_ok fit_ok.
  unfold lterm.
  rewrite body_ok, fit_ok.
  reflexivity.
Qed.

Theorem lterm_empty : forall out item body row cost next,
  lbody item out body = Some (out, row, cost, next) ->
  lfit 0 body = true ->
  lterm 0 out item body = Some (SVnil out).
Proof.
  intros out item body row cost next body_ok fit_ok.
  rewrite (lterm_exact 0 out item body row cost next body_ok fit_ok).
  reflexivity.
Qed.

Theorem lcheck_type : forall inputs count out item body typ row cost next,
  lcheck inputs count out item body = Some (typ, row, cost, next) ->
  typ = TVec count out.
Proof.
  intros inputs count out item body typ row cost next accepted.
  unfold lcheck in accepted.
  destruct (lterm count out item body) as [term |]; try discriminate.
  destruct (pcheck inputs term) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (TVec count out)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  reflexivity.
Qed.

Theorem lcheck_sound : forall inputs count out item body typ row cost next,
  lcheck inputs count out item body = Some (typ, row, cost, next) ->
  exists brow bcost bnext term,
    lbody item out body = Some (out, brow, bcost, bnext) /\
    lfit count body = true /\
    lterm count out item body = Some term /\
    pcheck inputs term = Some (TVec count out, row, cost, next) /\
    typ = TVec count out.
Proof.
  intros inputs count out item body typ row cost next accepted.
  unfold lcheck in accepted.
  destruct (lterm count out item body) as [term |] eqn:built;
    try discriminate.
  unfold lterm in built.
  destruct (lbody item out body) as [[[[btyp brow] bcost] bnext] |]
    eqn:body_ok; try discriminate.
  destruct (lfit count body) eqn:fit_ok; try discriminate.
  destruct (pcheck inputs term) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (TVec count out)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  inversion built; subst.
  pose proof (lbody_type item out body btyp brow bcost bnext body_ok)
    as body_type.
  subst btyp.
  exists brow, bcost, bnext, (lvec out (lvals count 0 item body)).
  repeat split; assumption.
Qed.

Theorem lcheck_complete : forall inputs count out item body row cost next
    brow bcost bnext term,
  lbody item out body = Some (out, brow, bcost, bnext) ->
  lterm count out item body = Some term ->
  pcheck inputs term = Some (TVec count out, row, cost, next) ->
  lcheck inputs count out item body =
    Some (TVec count out, row, cost, next).
Proof.
  intros inputs count out item body row cost next brow bcost bnext term
    body_ok built checked.
  unfold lcheck.
  rewrite built, checked, ty_eqb_refl.
  reflexivity.
Qed.