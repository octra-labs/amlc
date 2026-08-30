(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Require Import Lim.
Require Import Uni.
Require Import Dec.

Import ListNotations.

Record rlim : Type := Rlim {
  rnat : nat;
  rstr : nat;
  rtext : nat;
  rty_depth : nat;
  rty_nodes : nat;
  rtm_depth : nat;
  rtm_nodes : nat;
  rinputs : nat;
  rfuel : nat;
  rname : nat;
  rtag : nat
}.

Definition local : rlim :=
  Rlim 1000000 16777211 1024 256 4096 4096 100000 4096 1000000 64 12.

Definition posb (value : nat) : bool := negb (Nat.eqb value 0).

Definition limits_b (value : rlim) : bool :=
  posb (rnat value)
    && posb (rstr value)
    && posb (rtext value)
    && posb (rty_depth value)
    && posb (rty_nodes value)
    && posb (rtm_depth value)
    && posb (rtm_nodes value)
    && posb (rinputs value)
    && posb (rfuel value)
    && posb (rname value)
    && posb (rtag value)
    && Nat.leb (rnat value) (rstr value)
    && Nat.leb (rtext value) (rstr value)
    && Nat.leb (rty_depth value) (rtm_depth value)
    && Nat.leb (rty_nodes value) (rtm_nodes value)
    && Nat.leb (rinputs value) (rtm_nodes value)
    && Nat.leb (rfuel value) (rnat value)
    && Nat.leb (rname value) (rtext value)
    && Nat.leb (rtag value) (rnat value).

Definition limits_eqb (left right : rlim) : bool :=
  Nat.eqb (rnat left) (rnat right)
    && Nat.eqb (rstr left) (rstr right)
    && Nat.eqb (rtext left) (rtext right)
    && Nat.eqb (rty_depth left) (rty_depth right)
    && Nat.eqb (rty_nodes left) (rty_nodes right)
    && Nat.eqb (rtm_depth left) (rtm_depth right)
    && Nat.eqb (rtm_nodes left) (rtm_nodes right)
    && Nat.eqb (rinputs left) (rinputs right)
    && Nat.eqb (rfuel left) (rfuel right)
    && Nat.eqb (rname left) (rname right)
    && Nat.eqb (rtag left) (rtag right).

Theorem limits_eqb_eq : forall left right,
  limits_eqb left right = true -> left = right.
Proof.
  intros [ln ls lx ltd ltn lmd lmn li lf lname ltag]
    [rn rs rx rtd rtn rmd rmn ri rf rname rtag] H.
  unfold limits_eqb in H. simpl in H.
  repeat rewrite andb_true_iff in H.
  repeat rewrite Nat.eqb_eq in H.
  repeat match goal with
  | Hpair : _ /\ _ |- _ => destruct Hpair
  end.
  subst. reflexivity.
Qed.

Theorem limits_eqb_refl : forall value,
  limits_eqb value value = true.
Proof.
  intros value. unfold limits_eqb.
  repeat rewrite Nat.eqb_refl. reflexivity.
Qed.

Record rid : Type := Rid {
  rver : nat;
  rlimv : rlim
}.

Definition rid_vals (value : rid) : list nat :=
  rver value
    :: rnat (rlimv value)
    :: rstr (rlimv value)
    :: rtext (rlimv value)
    :: rty_depth (rlimv value)
    :: rty_nodes (rlimv value)
    :: rtm_depth (rlimv value)
    :: rtm_nodes (rlimv value)
    :: rinputs (rlimv value)
    :: rfuel (rlimv value)
    :: rname (rlimv value)
    :: rtag (rlimv value)
    :: nil.

Definition rid_eqb (left right : rid) : bool :=
  Nat.eqb (rver left) (rver right)
    && limits_eqb (rlimv left) (rlimv right).

Theorem rid_eqb_eq : forall left right,
  rid_eqb left right = true -> left = right.
Proof.
  intros [lv ll] [rv rl] H. unfold rid_eqb in H. simpl in H.
  rewrite andb_true_iff in H. destruct H as [Hver Hlim].
  apply Nat.eqb_eq in Hver. apply limits_eqb_eq in Hlim.
  subst. reflexivity.
Qed.

Theorem rid_eqb_refl : forall value,
  rid_eqb value value = true.
Proof.
  intros value. unfold rid_eqb.
  rewrite Nat.eqb_refl, limits_eqb_refl. reflexivity.
Qed.

Record rule : Type := Rule {
  rrid : rid;
  ract : nat
}.

Definition rule_b (value : rule) : bool :=
  posb (rver (rrid value)) && limits_b (rlimv (rrid value)).

Fixpoint has_id (id : rid) (values : list rule) : bool :=
  match values with
  | [] => false
  | value :: rest => rid_eqb id (rrid value) || has_id id rest
  end.

Fixpoint has_epoch (epoch : nat) (values : list rule) : bool :=
  match values with
  | [] => false
  | value :: rest => Nat.eqb epoch (ract value) || has_epoch epoch rest
  end.

Fixpoint unique_b (values : list rule) : bool :=
  match values with
  | [] => true
  | value :: rest =>
      rule_b value
        && negb (has_id (rrid value) rest)
        && negb (has_epoch (ract value) rest)
        && unique_b rest
  end.

Definition schedule_b (values : list rule) : bool :=
  Nat.leb (length values) (rinputs local) && unique_b values.

Definition active (epoch : nat) (value : rule) : bool :=
  Nat.leb (ract value) epoch.

Definition newer (left right : rule) : rule :=
  if Nat.leb (ract left) (ract right) then right else left.

Fixpoint rsel (epoch : nat) (values : list rule) : option rule :=
  match values with
  | [] => None
  | value :: rest =>
      match active epoch value, rsel epoch rest with
      | false, found => found
      | true, None => Some value
      | true, Some found => Some (newer found value)
      end
  end.

Lemma newer_in : forall left right,
  newer left right = left \/ newer left right = right.
Proof.
  intros left right. unfold newer.
  destruct (Nat.leb (ract left) (ract right)); auto.
Qed.

Lemma newer_ge_left : forall left right,
  ract left <= ract (newer left right).
Proof.
  intros left right. unfold newer.
  destruct (Nat.leb (ract left) (ract right)) eqn:Hle; simpl.
  - apply Nat.leb_le. exact Hle.
  - apply Nat.le_refl.
Qed.

Lemma newer_ge_right : forall left right,
  ract right <= ract (newer left right).
Proof.
  intros left right. unfold newer.
  destruct (Nat.leb (ract left) (ract right)) eqn:Hle; simpl.
  - apply Nat.le_refl.
  - apply Nat.lt_le_incl. apply Nat.leb_gt. exact Hle.
Qed.

Lemma newer_active : forall epoch left right,
  active epoch left = true ->
  active epoch right = true ->
  active epoch (newer left right) = true.
Proof.
  intros epoch left right Hleft Hright. unfold newer.
  destruct (Nat.leb (ract left) (ract right)); assumption.
Qed.

Theorem rsel_in : forall epoch values out,
  rsel epoch values = Some out -> In out values.
Proof.
  induction values as [|head rest IH]; intros out Hsel.
  - discriminate.
  - simpl in Hsel.
    destruct (active epoch head) eqn:Hhead;
      destruct (rsel epoch rest) as [found|] eqn:Hrest;
      simpl in Hsel.
    + inversion Hsel; subst out.
      destruct (newer_in found head) as [Heq|Heq].
      * rewrite Heq. right. apply IH. reflexivity.
      * rewrite Heq. left. reflexivity.
    + inversion Hsel; subst out. left. reflexivity.
    + inversion Hsel; subst out. right. apply IH. reflexivity.
    + discriminate.
Qed.

Theorem rsel_active : forall epoch values out,
  rsel epoch values = Some out -> active epoch out = true.
Proof.
  induction values as [|head rest IH]; intros out Hsel.
  - discriminate.
  - simpl in Hsel.
    destruct (active epoch head) eqn:Hhead;
      destruct (rsel epoch rest) as [found|] eqn:Hrest;
      simpl in Hsel.
    + inversion Hsel; subst out. apply newer_active.
      * apply IH. reflexivity.
      * exact Hhead.
    + inversion Hsel; subst out. exact Hhead.
    + inversion Hsel; subst out. apply IH. reflexivity.
    + discriminate.
Qed.

Theorem rsel_some : forall epoch values item,
  In item values -> active epoch item = true ->
  exists out, rsel epoch values = Some out.
Proof.
  induction values as [|head rest IH]; intros item Hin Hactive.
  - inversion Hin.
  - destruct Hin as [Heq|Hin].
    + subst item. simpl. rewrite Hactive.
      destruct (rsel epoch rest) as [found|].
      * exists (newer found head). reflexivity.
      * exists head. reflexivity.
    + destruct (IH item Hin Hactive) as [found Hfound].
      simpl. rewrite Hfound. destruct (active epoch head).
      * exists (newer found head). reflexivity.
      * exists found. reflexivity.
Qed.

Theorem rsel_max : forall epoch values out item,
  rsel epoch values = Some out ->
  In item values ->
  active epoch item = true ->
  ract item <= ract out.
Proof.
  induction values as [|head rest IH]; intros out item Hsel Hin Hactive.
  - inversion Hin.
  - simpl in Hsel.
    destruct (active epoch head) eqn:Hhead;
      destruct (rsel epoch rest) as [found|] eqn:Hrest;
      simpl in Hsel.
    + inversion Hsel; subst out. destruct Hin as [Heq|Hin].
      * subst item. apply newer_ge_right.
      * eapply Nat.le_trans.
        -- eapply IH; eauto.
        -- apply newer_ge_left.
    + inversion Hsel; subst out. destruct Hin as [Heq|Hin].
      * subst item. apply Nat.le_refl.
      * destruct (rsel_some epoch rest item Hin Hactive) as [found Hfound].
        rewrite Hrest in Hfound. discriminate.
    + inversion Hsel; subst out. destruct Hin as [Heq|Hin].
      * subst item. rewrite Hactive in Hhead. discriminate.
      * eapply IH; eauto.
    + discriminate.
Qed.

Definition supported (value : rule) : bool :=
  limits_eqb (rlimv (rrid value)) local.

Definition rcheck (rules : list rule) (epoch : nat) (gamma : ctx) (term : tm)
    : option (rid * chk) :=
  match rsel epoch rules with
  | Some value =>
      if supported value then
        match Lim.acceptb gamma term with
        | Some checked => Some (rrid value, checked)
        | None => None
        end
      else None
  | None => None
  end.

Theorem rcheck_sound : forall rules epoch gamma term id typ row cost next,
  rcheck rules epoch gamma term = Some (id, (typ, row, cost, next)) ->
  check gamma term typ row cost next.
Proof.
  intros rules epoch gamma term id typ row cost next Hcheck.
  unfold rcheck in Hcheck.
  destruct (rsel epoch rules) as [value|] eqn:Hsel; try discriminate.
  destruct (supported value) eqn:Hsupport; try discriminate.
  destruct (Lim.acceptb gamma term) as [checked|] eqn:Haccept; try discriminate.
  inversion Hcheck; subst. eapply Lim.acceptb_sound. exact Haccept.
Qed.

Theorem rcheck_active : forall rules epoch gamma term id checked,
  rcheck rules epoch gamma term = Some (id, checked) ->
  exists value,
    rsel epoch rules = Some value
      /\ rrid value = id
      /\ active epoch value = true.
Proof.
  intros rules epoch gamma term id checked Hcheck.
  unfold rcheck in Hcheck.
  destruct (rsel epoch rules) as [value|] eqn:Hsel; try discriminate.
  destruct (supported value) eqn:Hsupport; try discriminate.
  destruct (Lim.acceptb gamma term) as [found|] eqn:Haccept; try discriminate.
  inversion Hcheck; subst. exists value. repeat split; auto.
  eapply rsel_active. exact Hsel.
Qed.

Definition rrun (rules : list rule) (epoch : nat) (sigma : env) (term : tm)
    : option (rid * ans) :=
  match rsel epoch rules with
  | Some value =>
      if supported value then
        Some (rrid value, Lim.runb (rfuel (rlimv (rrid value))) sigma term)
      else None
  | None => None
  end.

Theorem rrun_active : forall rules epoch sigma term id answer,
  rrun rules epoch sigma term = Some (id, answer) ->
  exists value,
    rsel epoch rules = Some value
      /\ rrid value = id
      /\ active epoch value = true.
Proof.
  intros rules epoch sigma term id answer Hrun.
  unfold rrun in Hrun.
  destruct (rsel epoch rules) as [value|] eqn:Hsel; try discriminate.
  destruct (supported value) eqn:Hsupport; try discriminate.
  inversion Hrun; subst. exists value. repeat split; auto.
  eapply rsel_active. exact Hsel.
Qed.