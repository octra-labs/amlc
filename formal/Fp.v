(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Local Open Scope Z_scope.

Definition p : Z := 2 ^ 127 - 1.

Definition norm (value : Z) : Z := value mod p.

Definition valid (value : Z) : bool :=
  (0 <=? value) && (value <? p).

Definition add (left right : Z) : Z := norm (left + right).

Definition mul (left right : Z) : Z := norm (left * right).

Lemma p_pos : 0 < p.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma p_nz : p <> 0.
Proof.
  pose proof p_pos. lia.
Qed.

Theorem norm_nonneg : forall value, 0 <= norm value.
Proof.
  intros value. unfold norm.
  pose proof (Z.mod_pos_bound value p p_pos). lia.
Qed.

Theorem norm_lt : forall value, norm value < p.
Proof.
  intros value. unfold norm.
  pose proof (Z.mod_pos_bound value p p_pos). lia.
Qed.

Theorem norm_valid : forall value, valid (norm value) = true.
Proof.
  intros value. unfold valid.
  apply andb_true_iff. split.
  - apply Z.leb_le. apply norm_nonneg.
  - apply Z.ltb_lt. apply norm_lt.
Qed.

Theorem valid_range : forall value,
  valid value = true -> 0 <= value < p.
Proof.
  intros value H. unfold valid in H.
  apply andb_true_iff in H. destruct H as [Hlo Hhi].
  apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi. lia.
Qed.

Theorem norm_fixed : forall value,
  valid value = true -> norm value = value.
Proof.
  intros value H. unfold norm.
  apply Z.mod_small. apply valid_range. exact H.
Qed.

Theorem norm_idem : forall value,
  norm (norm value) = norm value.
Proof.
  intros value. unfold norm.
  apply Z.mod_mod. exact p_nz.
Qed.

Theorem add_valid : forall left right,
  valid (add left right) = true.
Proof.
  intros left right. apply norm_valid.
Qed.

Theorem mul_valid : forall left right,
  valid (mul left right) = true.
Proof.
  intros left right. apply norm_valid.
Qed.

Theorem add_comm : forall left right,
  add left right = add right left.
Proof.
  intros left right. unfold add. f_equal. lia.
Qed.

Theorem mul_comm : forall left right,
  mul left right = mul right left.
Proof.
  intros left right. unfold mul. f_equal. nia.
Qed.

Theorem add_zero : forall value,
  add value 0 = norm value.
Proof.
  intros value. unfold add. f_equal. lia.
Qed.

Theorem mul_one : forall value,
  mul value 1 = norm value.
Proof.
  intros value. unfold mul. f_equal. nia.
Qed.