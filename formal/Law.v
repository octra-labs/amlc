(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.

Require Import Lim.
Require Import Idx.
Require Import Low.

Import ListNotations.

Record law : Type := Law {
  lrel : irel;
  lleft : ix;
  lright : ix
}.

Definition law_b (item : law) : bool :=
  ix_b (lleft item) && ix_b (lright item).

Definition laws_b (items : list law) : bool :=
  Nat.leb (length items) pmax && forallb law_b items.

Definition lhold (env : ienv) (item : law) : option unit :=
  match ihold env (lrel item) (lleft item) (lright item) with
  | Some true => Some tt
  | _ => None
  end.

Fixpoint lholds (env : ienv) (items : list law) : option unit :=
  match items with
  | [] => Some tt
  | item :: rest =>
      match lhold env item, lholds env rest with
      | Some tt, Some tt => Some tt
      | _, _ => None
      end
  end.

Definition lawP (env : ienv) (item : law) : Prop :=
  match lrel item with
  | IEq => exists value,
      ieval env (lleft item) = Some value /\
      ieval env (lright item) = Some value
  | ILe => exists lhs rhs,
      ieval env (lleft item) = Some lhs /\
      ieval env (lright item) = Some rhs /\ lhs <= rhs
  end.

Inductive lawsR (env : ienv) : list law -> Prop :=
| LRNil : lawsR env []
| LRCons : forall item rest,
    lawP env item ->
    lawsR env rest ->
    lawsR env (item :: rest).

Theorem lhold_sound : forall env item,
  lhold env item = Some tt -> lawP env item.
Proof.
  intros env item accepted.
  unfold lhold in accepted.
  destruct (ihold env (lrel item) (lleft item) (lright item))
    as [answer |] eqn:held; try discriminate.
  destruct answer; try discriminate.
  apply ihold_true. exact held.
Qed.

Theorem lhold_complete : forall env item,
  lawP env item -> lhold env item = Some tt.
Proof.
  intros env item proven.
  unfold lhold.
  apply ihold_true in proven.
  rewrite proven. reflexivity.
Qed.

Theorem lholds_sound : forall env items,
  lholds env items = Some tt -> lawsR env items.
Proof.
  intros env items.
  induction items as [|item rest IH]; intros accepted; simpl in accepted.
  - constructor.
  - destruct (lhold env item) as [[] |] eqn:one; try discriminate.
    destruct (lholds env rest) as [[] |] eqn:more in accepted;
      try discriminate.
    constructor.
    + eapply lhold_sound. exact one.
    + apply IH. exact more.
Qed.

Theorem lholds_complete : forall env items,
  lawsR env items -> lholds env items = Some tt.
Proof.
  intros env items proven.
  induction proven; simpl.
  - reflexivity.
  - rewrite lhold_complete by exact H. rewrite IHproven. reflexivity.
Qed.