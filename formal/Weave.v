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

Fixpoint wvals (count pos source : nat) (item : sbind) (body : stm)
    : list stm :=
  match count with
  | O => []
  | S rest =>
      SLet item (SAt pos (SVar source)) body ::
        wvals rest (S pos) source item body
  end.

Fixpoint wvec (out : ty) (values : list stm) : stm :=
  match values with
  | [] => SVnil out
  | value :: rest => SVcons value (wvec out rest)
  end.

Definition wbody (item : sbind) (out : ty) (body : stm) : option chk :=
  if data_b (sty item) && data_b out then
    match pcheck [item] body with
    | Some (typ, row, cost, next) =>
        if ty_eqb typ out then Some (out, row, cost, next) else None
    | None => None
    end
  else None.

Definition wfit (count : nat) (source body : stm) : bool :=
  let node_count :=
    fin_nodes source + 2 + count * (fin_nodes body + 3) in
  let depth_count :=
    match count with
    | O => S (fin_depth source)
    | S _ =>
        Nat.max (S (fin_depth source)) (Nat.max 4 (3 + fin_depth body))
    end
  in
  fin_valid source && fin_valid body && fin_fit node_count depth_count.

Definition wterm (source_name count : nat) (out : ty) (source : stm)
    (item : sbind) (body : stm) : option stm :=
  match wbody item out body with
  | None => None
  | Some _ =>
      if wfit count source body then
        if Nat.eqb source_name (sname item) then None
        else if has source_name source then None
        else if has source_name body then None
        else Some (SLet (SBind source_name MM (TVec count (sty item))) source
          (wvec out (wvals count 0 source_name item body)))
      else None
  end.

Definition wcheck (inputs : list sbind) (source_name count : nat) (out : ty)
    (source : stm) (item : sbind) (body : stm) : option chk :=
  match wterm source_name count out source item body with
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

Theorem wbody_type : forall item out body typ row cost next,
  wbody item out body = Some (typ, row, cost, next) ->
  typ = out.
Proof.
  intros item out body typ row cost next accepted.
  unfold wbody in accepted.
  destruct (data_b (sty item) && data_b out); try discriminate.
  destruct (pcheck [item] body) as [[[[got grow] gcost] gnext] |];
    try discriminate.
  destruct (ty_eqb got out); try discriminate.
  inversion accepted.
  reflexivity.
Qed.

Theorem wvals_length : forall count pos source item body,
  length (wvals count pos source item body) = count.
Proof.
  induction count as [| count IH]; intros pos source item body; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Theorem wnodes : forall count pos source out item body,
  fin_nodes (wvec out (wvals count pos source item body)) =
  1 + count * (fin_nodes body + 3).
Proof.
  induction count as [| count IH]; intros pos source out item body; simpl.
  - reflexivity.
  - rewrite IH. nia.
Qed.

Theorem wdepth : forall count pos source out item body,
  fin_depth (wvec out (wvals count pos source item body)) =
  match count with
  | O => 0
  | S _ => Nat.max 3 (2 + fin_depth body)
  end.
Proof.
  induction count as [| count IH]; intros pos source out item body; simpl.
  - reflexivity.
  - destruct count as [| count].
    + reflexivity.
    + rewrite IH.
      change (Nat.max (Nat.max 3 (2 + fin_depth body))
        (Nat.max 3 (2 + fin_depth body)) =
        Nat.max 3 (2 + fin_depth body)).
      apply Nat.max_id.
Qed.

Theorem wout_nodes : forall source_name count out source item body,
  fin_nodes
    (SLet (SBind source_name MM (TVec count (sty item))) source
      (wvec out (wvals count 0 source_name item body))) =
  fin_nodes source + 2 + count * (fin_nodes body + 3).
Proof.
  intros source_name count out source item body.
  simpl.
  rewrite wnodes.
  nia.
Qed.

Theorem wout_depth : forall source_name count out source item body,
  fin_depth
    (SLet (SBind source_name MM (TVec count (sty item))) source
      (wvec out (wvals count 0 source_name item body))) =
  match count with
  | O => S (fin_depth source)
  | S _ =>
      Nat.max (S (fin_depth source)) (Nat.max 4 (3 + fin_depth body))
  end.
Proof.
  intros source_name count out source item body.
  simpl.
  rewrite wdepth.
  destruct count as [| count].
  - rewrite Nat.max_0_r. reflexivity.
  - rewrite !Nat.succ_max_distr. reflexivity.
Qed.

Theorem wfit_valid : forall source_name count out source item body,
  wfit count source body = true ->
  fin_valid
    (SLet (SBind source_name MM (TVec count (sty item))) source
      (wvec out (wvals count 0 source_name item body))) = true.
Proof.
  intros source_name count out source item body accepted.
  unfold wfit in accepted.
  apply andb_true_iff in accepted as [_ fit_ok].
  unfold fin_valid.
  rewrite wout_nodes, wout_depth.
  exact fit_ok.
Qed.

Theorem wterm_valid : forall source_name count out source item body term,
  wterm source_name count out source item body = Some term ->
  fin_valid term = true.
Proof.
  intros source_name count out source item body term built.
  unfold wterm in built.
  destruct (wbody item out body); try discriminate.
  destruct (wfit count source body) eqn:fit_ok; try discriminate.
  destruct (Nat.eqb source_name (sname item)); try discriminate.
  destruct (has source_name source); try discriminate.
  destruct (has source_name body); try discriminate.
  inversion built; subst.
  apply wfit_valid.
  exact fit_ok.
Qed.

Theorem wbody_sound : forall item out body row cost next,
  wbody item out body = Some (out, row, cost, next) ->
  data_b (sty item) = true /\
  data_b out = true /\
  pcheck [item] body = Some (out, row, cost, next).
Proof.
  intros item out body row cost next accepted.
  unfold wbody in accepted.
  destruct (data_b (sty item) && data_b out) eqn:data_ok;
    try discriminate.
  apply andb_true_iff in data_ok as [item_ok out_ok].
  destruct (pcheck [item] body) as [[[[typ brow] bcost] bnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb typ out) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  subst.
  inversion accepted; subst.
  repeat split; assumption.
Qed.

Theorem wbody_complete : forall item out body row cost next,
  data_b (sty item) = true ->
  data_b out = true ->
  pcheck [item] body = Some (out, row, cost, next) ->
  wbody item out body = Some (out, row, cost, next).
Proof.
  intros item out body row cost next item_ok out_ok checked.
  unfold wbody.
  rewrite item_ok, out_ok, checked, ty_eqb_refl.
  reflexivity.
Qed.

Theorem wterm_exact : forall source_name count out source item body
    row cost next,
  wbody item out body = Some (out, row, cost, next) ->
  wfit count source body = true ->
  source_name <> sname item ->
  has source_name source = false ->
  has source_name body = false ->
  wterm source_name count out source item body =
    Some (SLet (SBind source_name MM (TVec count (sty item))) source
      (wvec out (wvals count 0 source_name item body))).
Proof.
  intros source_name count out source item body row cost next
    body_ok fit_ok apart source_ok term_ok.
  unfold wterm.
  rewrite body_ok, fit_ok.
  apply Nat.eqb_neq in apart.
  rewrite apart, source_ok, term_ok.
  reflexivity.
Qed.

Theorem wterm_empty : forall source_name out source item body row cost next,
  wbody item out body = Some (out, row, cost, next) ->
  wfit 0 source body = true ->
  source_name <> sname item ->
  has source_name source = false ->
  has source_name body = false ->
  wterm source_name 0 out source item body =
    Some (SLet (SBind source_name MM (TVec 0 (sty item))) source (SVnil out)).
Proof.
  intros source_name out source item body row cost next
    body_ok fit_ok apart source_ok term_ok.
  rewrite (wterm_exact source_name 0 out source item body row cost next
    body_ok fit_ok apart source_ok term_ok).
  reflexivity.
Qed.

Theorem wcheck_type : forall inputs source_name count out source item body
    typ row cost next,
  wcheck inputs source_name count out source item body =
    Some (typ, row, cost, next) ->
  typ = TVec count out.
Proof.
  intros inputs source_name count out source item body typ row cost next accepted.
  unfold wcheck in accepted.
  destruct (wterm source_name count out source item body) as [term |];
    try discriminate.
  destruct (pcheck inputs term) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (TVec count out)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  reflexivity.
Qed.

Theorem wcheck_sound : forall inputs source_name count out source item body
    typ row cost next,
  wcheck inputs source_name count out source item body =
    Some (typ, row, cost, next) ->
  exists brow bcost bnext term,
    wbody item out body = Some (out, brow, bcost, bnext) /\
    wfit count source body = true /\
    wterm source_name count out source item body = Some term /\
    pcheck inputs term = Some (TVec count out, row, cost, next) /\
    typ = TVec count out.
Proof.
  intros inputs source_name count out source item body typ row cost next accepted.
  unfold wcheck in accepted.
  destruct (wterm source_name count out source item body) as [term |]
    eqn:built; try discriminate.
  unfold wterm in built.
  destruct (wbody item out body) as [[[[btyp brow] bcost] bnext] |]
    eqn:body_ok; try discriminate.
  destruct (wfit count source body) eqn:fit_ok; try discriminate.
  destruct (Nat.eqb source_name (sname item)); try discriminate.
  destruct (has source_name source); try discriminate.
  destruct (has source_name body); try discriminate.
  destruct (pcheck inputs term) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (TVec count out)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  inversion built; subst.
  pose proof (wbody_type item out body btyp brow bcost bnext body_ok)
    as body_type.
  subst btyp.
  destruct (wbody_sound item out body brow bcost bnext body_ok)
    as [_ [_ exact_body]].
  exists brow, bcost, bnext,
    (SLet (SBind source_name MM (TVec count (sty item))) source
      (wvec out (wvals count 0 source_name item body))).
  repeat split; assumption.
Qed.

Theorem wcheck_complete : forall inputs source_name count out source item body
    row cost next brow bcost bnext term,
  wbody item out body = Some (out, brow, bcost, bnext) ->
  wterm source_name count out source item body = Some term ->
  pcheck inputs term = Some (TVec count out, row, cost, next) ->
  wcheck inputs source_name count out source item body =
    Some (TVec count out, row, cost, next).
Proof.
  intros inputs source_name count out source item body row cost next
    brow bcost bnext term body_ok built checked.
  unfold wcheck.
  rewrite built, checked, ty_eqb_refl.
  reflexivity.
Qed.