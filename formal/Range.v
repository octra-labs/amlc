(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.

Inductive sign : Type :=
| Signed
| Unsigned.

Scheme Equality for sign.

Inductive fit_result : Type :=
| Inside : Z -> fit_result
| Outside : Z -> fit_result.

Scheme Equality for fit_result.

Definition valid (bits : nat) : bool :=
  Nat.leb 1 bits && Nat.leb bits 256.

Definition span (bits : nat) : Z :=
  (2 ^ Z.of_nat bits)%Z.

Definition low (kind : sign) (bits : nat) : Z :=
  match kind with
  | Signed => (- span (Nat.pred bits))%Z
  | Unsigned => 0%Z
  end.

Definition high (kind : sign) (bits : nat) : Z :=
  match kind with
  | Signed => (span (Nat.pred bits) - 1)%Z
  | Unsigned => (span bits - 1)%Z
  end.

Definition admits (kind : sign) (bits : nat) (value : Z) : bool :=
  valid bits
  && ((low kind bits <=? value)%Z && (value <=? high kind bits)%Z).

Definition fit (kind : sign) (bits : nat) (value : Z) : fit_result :=
  if admits kind bits value then Inside value else Outside value.

Definition wide (value : Z) : Z := value.

Theorem valid_spec : forall bits,
  valid bits = true <-> 1 <= bits <= 256.
Proof.
  intros bits.
  unfold valid.
  rewrite andb_true_iff, Nat.leb_le, Nat.leb_le.
  tauto.
Qed.

Theorem admits_spec : forall kind bits value,
  admits kind bits value = true <->
  valid bits = true
  /\ (low kind bits <= value <= high kind bits)%Z.
Proof.
  intros kind bits value.
  unfold admits.
  rewrite andb_true_iff, andb_true_iff, Z.leb_le, Z.leb_le.
  tauto.
Qed.

Theorem unsigned_spec : forall bits value,
  valid bits = true ->
  admits Unsigned bits value = true <->
  (0 <= value < span bits)%Z.
Proof.
  intros bits value bits_ok.
  rewrite admits_spec.
  unfold low, high.
  split.
  - intros [_ [nonnegative below]].
    lia.
  - intros [nonnegative below].
    split.
    + exact bits_ok.
    + lia.
Qed.

Theorem signed_spec : forall bits value,
  valid bits = true ->
  admits Signed bits value = true <->
  (- span (Nat.pred bits) <= value < span (Nat.pred bits))%Z.
Proof.
  intros bits value bits_ok.
  rewrite admits_spec.
  unfold low, high.
  split.
  - intros [_ [above below]].
    lia.
  - intros [above below].
    split.
    + exact bits_ok.
    + lia.
Qed.

Theorem fit_inside : forall kind bits value,
  fit kind bits value = Inside value <-> admits kind bits value = true.
Proof.
  intros kind bits value.
  unfold fit.
  destruct (admits kind bits value); split; intros same;
    try reflexivity; discriminate.
Qed.

Theorem fit_outside : forall kind bits value,
  fit kind bits value = Outside value <-> admits kind bits value = false.
Proof.
  intros kind bits value.
  unfold fit.
  destruct (admits kind bits value); split; intros same;
    try reflexivity; discriminate.
Qed.

Theorem wide_exact : forall value,
  wide value = value.
Proof.
  reflexivity.
Qed.