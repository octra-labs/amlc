(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import List.
From Stdlib Require Import ZArith.

Import ListNotations.

Definition read_len (cap : nat) (value : Z) : option nat :=
  if (0 <=? value)%Z && (value <=? Z.of_nat cap)%Z then
    Some (Z.to_nat value)
  else None.

Definition pack {A : Type} (cap : nat) (zero : A)
    (values : list A) : list A :=
  firstn cap values
  ++ repeat zero (cap - Nat.min cap (length values)).

Definition image (A : Type) : Type := nat * list A.

Definition make {A : Type} (cap : nat) (zero : A)
    (values : list A) : image A :=
  (length values, pack cap zero values).

Definition active {A : Type} (value : image A) : list A :=
  firstn (fst value) (snd value).

Definition valid {A : Type} (cap : nat) (zero : A)
    (value : image A) : Prop :=
  fst value <= cap
  /\ length (snd value) = cap
  /\ skipn (fst value) (snd value)
    = repeat zero (cap - fst value).

Definition run {A S : Type} (step : S -> A -> S)
    (value : image A) (seed : S) : S :=
  fold_left step (active value) seed.

Theorem read_len_spec : forall cap value count,
  read_len cap value = Some count <->
  (0 <= value <= Z.of_nat cap)%Z /\ count = Z.to_nat value.
Proof.
  intros cap value count.
  unfold read_len.
  destruct ((0 <=? value)%Z && (value <=? Z.of_nat cap)%Z)
    eqn:accepted.
  - rewrite andb_true_iff, Z.leb_le, Z.leb_le in accepted.
    split.
    + intros same.
      inversion same.
      tauto.
    + intros [_ same].
      subst.
      reflexivity.
  - split.
    + discriminate.
    + intros [[nonnegative below] _].
      rewrite andb_false_iff, Z.leb_gt, Z.leb_gt in accepted.
      lia.
Qed.

Theorem pack_eq : forall A cap (zero : A) values,
  length values <= cap ->
  pack cap zero values = values ++ repeat zero (cap - length values).
Proof.
  intros A cap zero values fits.
  unfold pack.
  rewrite firstn_all2 by exact fits.
  rewrite Nat.min_r by exact fits.
  reflexivity.
Qed.

Theorem pack_length : forall A cap (zero : A) values,
  length (pack cap zero values) = cap.
Proof.
  intros A cap zero values.
  unfold pack.
  rewrite length_app, length_firstn, repeat_length.
  pose proof (Nat.le_min_l cap (length values)).
  lia.
Qed.

Theorem pack_prefix : forall A cap (zero : A) values,
  length values <= cap ->
  firstn (length values) (pack cap zero values) = values.
Proof.
  intros A cap zero values fits.
  rewrite pack_eq by exact fits.
  rewrite firstn_app, firstn_all, Nat.sub_diag.
  simpl.
  rewrite app_nil_r.
  reflexivity.
Qed.

Theorem pack_tail : forall A cap (zero : A) values,
  length values <= cap ->
  skipn (length values) (pack cap zero values)
  = repeat zero (cap - length values).
Proof.
  intros A cap zero values fits.
  rewrite pack_eq by exact fits.
  rewrite skipn_app, skipn_all, Nat.sub_diag.
  simpl.
  reflexivity.
Qed.

Theorem make_valid : forall A cap (zero : A) values,
  length values <= cap -> valid cap zero (make cap zero values).
Proof.
  intros A cap zero values fits.
  unfold valid, make.
  simpl.
  repeat split.
  - exact fits.
  - apply pack_length.
  - apply pack_tail.
    exact fits.
Qed.

Theorem split_zero : forall A cap (zero : A) count values,
  skipn count values = repeat zero (cap - count) ->
  values = firstn count values ++ repeat zero (cap - count).
Proof.
  intros A cap zero count values tail_ok.
  rewrite <- (firstn_skipn count values) at 1.
  rewrite tail_ok.
  reflexivity.
Qed.

Theorem valid_unique : forall A cap (zero : A) value,
  valid cap zero value ->
  value = make cap zero (active value).
Proof.
  intros A cap zero [count values] accepted.
  unfold valid in accepted.
  simpl in accepted.
  destruct accepted as [count_ok [length_ok tail_ok]].
  unfold make, active.
  simpl.
  assert (prefix_length : length (firstn count values) = count).
  {
    rewrite length_firstn, Nat.min_l.
    - reflexivity.
    - lia.
  }
  assert (prefix_ok : length (firstn count values) <= cap) by lia.
  assert (values_eq : values = pack cap zero (firstn count values)).
  {
    rewrite pack_eq by exact prefix_ok.
    rewrite prefix_length.
    apply split_zero with (cap := cap).
    exact tail_ok.
  }
  rewrite prefix_length, <- values_eq.
  reflexivity.
Qed.

Theorem run_make : forall A S cap (zero : A) values
    (step : S -> A -> S) seed,
  length values <= cap ->
  run step (make cap zero values) seed = fold_left step values seed.
Proof.
  intros A S cap zero values step seed fits.
  unfold run, active, make.
  simpl.
  rewrite pack_prefix by exact fits.
  reflexivity.
Qed.