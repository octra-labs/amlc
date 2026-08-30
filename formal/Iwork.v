(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.ZArith.

Inductive iop : Type :=
| IAdd : iop
| ISub : iop
| IMul : iop
| IDiv : iop
| IMod : iop
| INeg : iop
| IAbs : iop.

Inductive mode : Type := Prior | Active.

Inductive answer : Type :=
| Value : Z -> answer
| Reject : answer.

Fixpoint pbits (value : positive) : nat :=
  match value with
  | xH => 1
  | xO rest | xI rest => S (pbits rest)
  end.

Definition bits (value : Z) : nat :=
  match value with
  | Z0 => 1
  | Zpos raw | Zneg raw => pbits raw
  end.

Definition cells (value : Z) : nat :=
  S ((bits value - 1) / 64).

Definition fixed (op : iop) : nat :=
  match op with
  | IAdd | ISub | IMul => 3
  | IDiv | IMod | INeg | IAbs => 5
  end.

Definition variable (op : iop) (left right : Z) : nat :=
  match op with
  | IAdd | ISub => Nat.max (cells left) (cells right)
  | IMul | IDiv | IMod => cells left * cells right
  | INeg | IAbs => cells left
  end.

Definition cost (selected : mode) (op : iop) (left right : Z) : nat :=
  match selected with
  | Prior => fixed op
  | Active => fixed op + variable op left right
  end.

Definition select (activate : option Z) (epoch : Z) : mode :=
  match activate with
  | Some first =>
      if (0 <=? first)%Z && (first <=? epoch)%Z then Active else Prior
  | None => Prior
  end.

Definition eval (op : iop) (left right : Z) : answer :=
  match op with
  | IAdd => Value (Z.add left right)
  | ISub => Value (Z.sub left right)
  | IMul => Value (Z.mul left right)
  | IDiv => if Z.eqb right 0 then Reject else Value (Z.quot left right)
  | IMod => if Z.eqb right 0 then Reject else Value (Z.rem left right)
  | INeg => Value (Z.opp left)
  | IAbs => Value (Z.abs left)
  end.

Lemma pbits_positive : forall value, 0 < pbits value.
Proof.
  induction value; simpl; lia.
Qed.

Lemma bits_positive : forall value, 0 < bits value.
Proof.
  intros [|value|value]; simpl.
  - lia.
  - apply pbits_positive.
  - apply pbits_positive.
Qed.

Lemma cells_positive : forall value, 0 < cells value.
Proof.
  intros value.
  unfold cells.
  lia.
Qed.

Lemma fixed_positive : forall op, 0 < fixed op.
Proof.
  intros []; simpl; lia.
Qed.

Theorem cost_at_least_fixed : forall selected op left right,
  fixed op <= cost selected op left right.
Proof.
  intros [] op left right; simpl; lia.
Qed.

Theorem cost_positive : forall selected op left right,
  0 < cost selected op left right.
Proof.
  intros selected op left right.
  pose proof (fixed_positive op).
  pose proof (cost_at_least_fixed selected op left right).
  lia.
Qed.

Theorem select_none : forall epoch,
  select None epoch = Prior.
Proof.
  reflexivity.
Qed.

Theorem select_negative : forall first epoch,
  (first < 0)%Z -> select (Some first) epoch = Prior.
Proof.
  intros first epoch negative.
  unfold select.
  assert ((0 <=? first)%Z = false) as first_negative.
  {
    apply Z.leb_gt.
    exact negative.
  }
  rewrite first_negative.
  reflexivity.
Qed.

Theorem select_before : forall first epoch,
  (0 <= first)%Z -> (epoch < first)%Z ->
  select (Some first) epoch = Prior.
Proof.
  intros first epoch first_ok before.
  unfold select.
  assert ((0 <=? first)%Z = true) as first_valid.
  {
    apply Z.leb_le.
    exact first_ok.
  }
  assert ((first <=? epoch)%Z = false) as epoch_before.
  {
    apply Z.leb_gt.
    exact before.
  }
  rewrite first_valid, epoch_before.
  reflexivity.
Qed.

Theorem select_at : forall first,
  (0 <= first)%Z -> select (Some first) first = Active.
Proof.
  intros first first_ok.
  unfold select.
  assert ((0 <=? first)%Z = true) as first_valid.
  {
    apply Z.leb_le.
    exact first_ok.
  }
  rewrite first_valid.
  rewrite Z.leb_refl.
  reflexivity.
Qed.

Theorem select_after : forall first epoch,
  (0 <= first <= epoch)%Z -> select (Some first) epoch = Active.
Proof.
  intros first epoch [first_ok after].
  unfold select.
  assert ((0 <=? first)%Z = true) as first_valid.
  {
    apply Z.leb_le.
    exact first_ok.
  }
  assert ((first <=? epoch)%Z = true) as epoch_after.
  {
    apply Z.leb_le.
    exact after.
  }
  rewrite first_valid, epoch_after.
  reflexivity.
Qed.

Theorem add_cost_commutative : forall selected left right,
  cost selected IAdd left right = cost selected IAdd right left.
Proof.
  intros [] left right.
  - reflexivity.
  - change (3 + Nat.max (cells left) (cells right) =
      3 + Nat.max (cells right) (cells left)).
    rewrite Nat.max_comm.
    reflexivity.
Qed.

Theorem mul_cost_commutative : forall selected left right,
  cost selected IMul left right = cost selected IMul right left.
Proof.
  intros [] left right.
  - reflexivity.
  - change (3 + cells left * cells right = 3 + cells right * cells left).
    rewrite Nat.mul_comm.
    reflexivity.
Qed.

Theorem div_zero : forall left,
  eval IDiv left 0 = Reject.
Proof.
  reflexivity.
Qed.

Theorem mod_zero : forall left,
  eval IMod left 0 = Reject.
Proof.
  reflexivity.
Qed.

Theorem div_nonzero : forall left right : Z,
  right <> 0%Z -> eval IDiv left right = Value (Z.quot left right).
Proof.
  intros left right nonzero.
  unfold eval.
  destruct (Z.eqb right 0) eqn:zero.
  - apply Z.eqb_eq in zero.
    contradiction.
  - reflexivity.
Qed.

Theorem mod_nonzero : forall left right : Z,
  right <> 0%Z -> eval IMod left right = Value (Z.rem left right).
Proof.
  intros left right nonzero.
  unfold eval.
  destruct (Z.eqb right 0) eqn:zero.
  - apply Z.eqb_eq in zero.
    contradiction.
  - reflexivity.
Qed.