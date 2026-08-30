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

Fixpoint bvals (count pos left_name right_name : nat)
    (first second : sbind) (body : stm) : list stm :=
  match count with
  | O => []
  | S rest =>
      SLet first (SAt pos (SVar left_name))
        (SLet second (SAt pos (SVar right_name)) body) ::
        bvals rest (S pos) left_name right_name first second body
  end.

Fixpoint bvec (out : ty) (values : list stm) : stm :=
  match values with
  | [] => SVnil out
  | value :: rest => SVcons value (bvec out rest)
  end.

Definition bbody (first second : sbind) (out : ty) (body : stm)
    : option chk :=
  if data_b (sty first) && (data_b (sty second) && data_b out) then
    match pcheck [first; second] body with
    | Some (typ, row, cost, next) =>
        if ty_eqb typ out then Some (out, row, cost, next) else None
    | None => None
    end
  else None.

Definition bfit (count : nat) (left right body : stm) : bool :=
  let node_count :=
    fin_nodes left + fin_nodes right + 3 + count * (fin_nodes body + 6) in
  let source_depth :=
    Nat.max (S (fin_depth left)) (2 + fin_depth right) in
  let depth_count :=
    match count with
    | O => Nat.max source_depth 2
    | S _ => Nat.max source_depth (Nat.max 6 (5 + fin_depth body))
    end
  in
  fin_valid left && fin_valid right && fin_valid body &&
    fin_fit node_count depth_count.

Definition bclear (left_name right_name : nat) (left right : stm)
    (first second : sbind) (body : stm) : bool :=
  negb (Nat.eqb left_name right_name ||
    Nat.eqb left_name (sname first) || Nat.eqb left_name (sname second) ||
    Nat.eqb right_name (sname first) || Nat.eqb right_name (sname second) ||
    has left_name left || has left_name right || has left_name body ||
    has right_name left || has right_name right || has right_name body).

Definition bterm (left_name right_name count : nat) (out : ty)
    (left right : stm) (first second : sbind) (body : stm) : option stm :=
  match bbody first second out body with
  | None => None
  | Some _ =>
      if bfit count left right body then
        if bclear left_name right_name left right first second body then
          Some (SLet (SBind left_name MM (TVec count (sty first))) left
            (SLet (SBind right_name MM (TVec count (sty second))) right
              (bvec out
                (bvals count 0 left_name right_name first second body))))
        else None
      else None
  end.

Definition bcheck (inputs : list sbind) (left_name right_name count : nat)
    (out : ty) (left right : stm) (first second : sbind) (body : stm)
    : option chk :=
  match bterm left_name right_name count out left right first second body with
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

Theorem bbody_type : forall first second out body typ row cost next,
  bbody first second out body = Some (typ, row, cost, next) ->
  typ = out.
Proof.
  intros first second out body typ row cost next accepted.
  unfold bbody in accepted.
  destruct (data_b (sty first) && (data_b (sty second) && data_b out));
    try discriminate.
  destruct (pcheck [first; second] body)
    as [[[[got grow] gcost] gnext] |]; try discriminate.
  destruct (ty_eqb got out); try discriminate.
  inversion accepted.
  reflexivity.
Qed.

Theorem bvals_length : forall count pos left_name right_name first second body,
  length (bvals count pos left_name right_name first second body) = count.
Proof.
  induction count as [| count IH];
    intros pos left_name right_name first second body; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Theorem bnodes : forall count pos left_name right_name out first second body,
  fin_nodes
    (bvec out (bvals count pos left_name right_name first second body)) =
  1 + count * (fin_nodes body + 6).
Proof.
  induction count as [| count IH];
    intros pos left_name right_name out first second body; simpl.
  - reflexivity.
  - rewrite IH. nia.
Qed.

Theorem bdepth : forall count pos left_name right_name out first second body,
  fin_depth
    (bvec out (bvals count pos left_name right_name first second body)) =
  match count with
  | O => 0
  | S _ => Nat.max 4 (3 + fin_depth body)
  end.
Proof.
  induction count as [| count IH];
    intros pos left_name right_name out first second body; simpl.
  - reflexivity.
  - destruct count as [| count].
    + reflexivity.
    + rewrite IH.
      change (Nat.max (Nat.max 4 (3 + fin_depth body))
        (Nat.max 4 (3 + fin_depth body)) =
        Nat.max 4 (3 + fin_depth body)).
      apply Nat.max_id.
Qed.

Theorem bout_nodes : forall left_name right_name count out left right
    first second body,
  fin_nodes
    (SLet (SBind left_name MM (TVec count (sty first))) left
      (SLet (SBind right_name MM (TVec count (sty second))) right
        (bvec out
          (bvals count 0 left_name right_name first second body)))) =
  fin_nodes left + fin_nodes right + 3 + count * (fin_nodes body + 6).
Proof.
  intros left_name right_name count out left right first second body.
  simpl.
  rewrite bnodes.
  nia.
Qed.

Theorem bout_depth : forall left_name right_name count out left right
    first second body,
  let source_depth :=
    Nat.max (S (fin_depth left)) (2 + fin_depth right) in
  fin_depth
    (SLet (SBind left_name MM (TVec count (sty first))) left
      (SLet (SBind right_name MM (TVec count (sty second))) right
        (bvec out
          (bvals count 0 left_name right_name first second body)))) =
  match count with
  | O => Nat.max source_depth 2
  | S _ => Nat.max source_depth (Nat.max 6 (5 + fin_depth body))
  end.
Proof.
  intros left_name right_name count out left right first second body.
  simpl.
  rewrite bdepth.
  destruct count as [| count].
  - rewrite Nat.max_0_r, !Nat.succ_max_distr.
    change (Nat.max (S (fin_depth left)) (2 + fin_depth right) =
      Nat.max
        (Nat.max (S (fin_depth left)) (2 + fin_depth right)) 2).
    symmetry.
    apply Nat.max_l.
    apply Nat.le_trans with (2 + fin_depth right).
    + lia.
    + apply Nat.le_max_r.
  - rewrite !Nat.succ_max_distr, Nat.max_assoc.
    reflexivity.
Qed.

Theorem bfit_valid : forall left_name right_name count out left right
    first second body,
  bfit count left right body = true ->
  fin_valid
    (SLet (SBind left_name MM (TVec count (sty first))) left
      (SLet (SBind right_name MM (TVec count (sty second))) right
        (bvec out
          (bvals count 0 left_name right_name first second body)))) = true.
Proof.
  intros left_name right_name count out left right first second body accepted.
  unfold bfit in accepted.
  apply andb_true_iff in accepted as [_ fit_ok].
  unfold fin_valid.
  rewrite bout_nodes, bout_depth.
  exact fit_ok.
Qed.

Theorem bterm_valid : forall left_name right_name count out left right
    first second body term,
  bterm left_name right_name count out left right first second body = Some term ->
  fin_valid term = true.
Proof.
  intros left_name right_name count out left right first second body term built.
  unfold bterm in built.
  destruct (bbody first second out body); try discriminate.
  destruct (bfit count left right body) eqn:fit_ok; try discriminate.
  destruct (bclear left_name right_name left right first second body);
    try discriminate.
  inversion built; subst.
  apply bfit_valid.
  exact fit_ok.
Qed.

Theorem bbody_sound : forall first second out body row cost next,
  bbody first second out body = Some (out, row, cost, next) ->
  data_b (sty first) = true /\
  data_b (sty second) = true /\
  data_b out = true /\
  pcheck [first; second] body = Some (out, row, cost, next).
Proof.
  intros first second out body row cost next accepted.
  unfold bbody in accepted.
  destruct (data_b (sty first) && (data_b (sty second) && data_b out))
    eqn:data_ok; try discriminate.
  apply andb_true_iff in data_ok as [first_ok rest_ok].
  apply andb_true_iff in rest_ok as [second_ok out_ok].
  destruct (pcheck [first; second] body)
    as [[[[typ brow] bcost] bnext] |] eqn:checked; try discriminate.
  destruct (ty_eqb typ out) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  subst.
  inversion accepted; subst.
  repeat split; assumption.
Qed.

Theorem bbody_complete : forall first second out body row cost next,
  data_b (sty first) = true ->
  data_b (sty second) = true ->
  data_b out = true ->
  pcheck [first; second] body = Some (out, row, cost, next) ->
  bbody first second out body = Some (out, row, cost, next).
Proof.
  intros first second out body row cost next
    first_ok second_ok out_ok checked.
  unfold bbody.
  rewrite first_ok, second_ok, out_ok, checked, ty_eqb_refl.
  reflexivity.
Qed.

Theorem bterm_exact : forall left_name right_name count out left right
    first second body row cost next,
  bbody first second out body = Some (out, row, cost, next) ->
  bfit count left right body = true ->
  bclear left_name right_name left right first second body = true ->
  bterm left_name right_name count out left right first second body =
    Some (SLet (SBind left_name MM (TVec count (sty first))) left
      (SLet (SBind right_name MM (TVec count (sty second))) right
        (bvec out
          (bvals count 0 left_name right_name first second body)))).
Proof.
  intros left_name right_name count out left right first second body
    row cost next body_ok fit_ok clear_ok.
  unfold bterm.
  rewrite body_ok, fit_ok, clear_ok.
  reflexivity.
Qed.

Theorem bterm_empty : forall left_name right_name out left right
    first second body row cost next,
  bbody first second out body = Some (out, row, cost, next) ->
  bfit 0 left right body = true ->
  bclear left_name right_name left right first second body = true ->
  bterm left_name right_name 0 out left right first second body =
    Some (SLet (SBind left_name MM (TVec 0 (sty first))) left
      (SLet (SBind right_name MM (TVec 0 (sty second))) right (SVnil out))).
Proof.
  intros left_name right_name out left right first second body
    row cost next body_ok fit_ok clear_ok.
  rewrite (bterm_exact left_name right_name 0 out left right first second body
    row cost next body_ok fit_ok clear_ok).
  reflexivity.
Qed.

Theorem bcheck_type : forall inputs left_name right_name count out left right
    first second body typ row cost next,
  bcheck inputs left_name right_name count out left right first second body =
    Some (typ, row, cost, next) ->
  typ = TVec count out.
Proof.
  intros inputs left_name right_name count out left right first second body
    typ row cost next accepted.
  unfold bcheck in accepted.
  destruct (bterm left_name right_name count out left right first second body)
    as [term |]; try discriminate.
  destruct (pcheck inputs term) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (TVec count out)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  reflexivity.
Qed.

Theorem bcheck_sound : forall inputs left_name right_name count out left right
    first second body typ row cost next,
  bcheck inputs left_name right_name count out left right first second body =
    Some (typ, row, cost, next) ->
  exists brow bcost bnext term,
    bbody first second out body = Some (out, brow, bcost, bnext) /\
    bfit count left right body = true /\
    bterm left_name right_name count out left right first second body =
      Some term /\
    pcheck inputs term = Some (TVec count out, row, cost, next) /\
    typ = TVec count out.
Proof.
  intros inputs left_name right_name count out left right first second body
    typ row cost next accepted.
  unfold bcheck in accepted.
  destruct (bterm left_name right_name count out left right first second body)
    as [term |] eqn:built; try discriminate.
  unfold bterm in built.
  destruct (bbody first second out body)
    as [[[[btyp brow] bcost] bnext] |] eqn:body_ok; try discriminate.
  destruct (bfit count left right body) eqn:fit_ok; try discriminate.
  destruct (bclear left_name right_name left right first second body);
    try discriminate.
  destruct (pcheck inputs term) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (TVec count out)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  inversion built; subst.
  pose proof (bbody_type first second out body btyp brow bcost bnext body_ok)
    as body_type.
  subst btyp.
  exists brow, bcost, bnext,
    (SLet (SBind left_name MM (TVec count (sty first))) left
      (SLet (SBind right_name MM (TVec count (sty second))) right
        (bvec out
          (bvals count 0 left_name right_name first second body)))).
  repeat split; assumption.
Qed.

Theorem bcheck_complete : forall inputs left_name right_name count out
    left right first second body row cost next brow bcost bnext term,
  bbody first second out body = Some (out, brow, bcost, bnext) ->
  bterm left_name right_name count out left right first second body = Some term ->
  pcheck inputs term = Some (TVec count out, row, cost, next) ->
  bcheck inputs left_name right_name count out left right first second body =
    Some (TVec count out, row, cost, next).
Proof.
  intros inputs left_name right_name count out left right first second body
    row cost next brow bcost bnext term body_ok built checked.
  unfold bcheck.
  rewrite built, checked, ty_eqb_refl.
  reflexivity.
Qed.