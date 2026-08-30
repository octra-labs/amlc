(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.

Import ListNotations.

Fixpoint dot (row key : list bool) : bool :=
  match row, key with
  | head :: rest, bit :: tail =>
      xorb (andb head bit) (dot rest tail)
  | _, _ => false
  end.

Fixpoint flip (pos : nat) (row : list bool) : list bool :=
  match pos, row with
  | 0, head :: rest => negb head :: rest
  | S next, head :: rest => head :: flip next rest
  | _, _ => row
  end.

Definition noisy (row key : list bool) (err : bool) : bool :=
  xorb (dot row key) err.

Lemma flip_len : forall pos row,
  length (flip pos row) = length row.
Proof.
  induction pos as [|pos IH]; destruct row as [|head rest]; simpl; auto.
Qed.

Lemma flip_nth : forall pos row,
  nth_error (flip pos row) pos = option_map negb (nth_error row pos).
Proof.
  induction pos as [|pos IH]; destruct row as [|head rest]; simpl; auto.
Qed.

Lemma flip_twice : forall pos row,
  flip pos (flip pos row) = row.
Proof.
  induction pos as [|pos IH]; destruct row as [|head rest]; simpl; auto.
  - destruct head; reflexivity.
  - now rewrite IH.
Qed.

Lemma row_at : forall (pos : nat) (row key : list bool),
  length row = length key ->
  nth_error key pos = Some true ->
  exists bit, nth_error row pos = Some bit.
Proof.
  induction pos as [|pos IH].
  - intros row key same found.
    destruct row as [|head rest]; destruct key as [|bit tail];
      simpl in *; try discriminate.
    exists head. reflexivity.
  - intros row key same found.
    destruct row as [|head rest]; destruct key as [|bit tail];
      simpl in *; try discriminate.
    injection same as same.
    eapply IH; eauto.
Qed.

Theorem dot_flip : forall (pos : nat) (row key : list bool) (bit : bool),
  nth_error row pos = Some bit ->
  nth_error key pos = Some true ->
  dot (flip pos row) key = negb (dot row key).
Proof.
  induction pos as [|pos IH]; intros row key bit row_bit key_bit;
    destruct row as [|head rest]; destruct key as [|mark tail];
    simpl in row_bit, key_bit; try discriminate.
  - inversion row_bit. inversion key_bit. subst. simpl.
    destruct bit; destruct (dot rest tail); reflexivity.
  - simpl. rewrite (IH rest tail bit row_bit key_bit).
    destruct head; destruct mark; destruct (dot rest tail); reflexivity.
Qed.

Theorem noisy_flip : forall (pos : nat) (row key : list bool)
    (bit err : bool),
  nth_error row pos = Some bit ->
  nth_error key pos = Some true ->
  noisy (flip pos row) key err = negb (noisy row key err).
Proof.
  intros pos row key bit err row_bit key_bit.
  unfold noisy. rewrite (dot_flip pos row key bit row_bit key_bit).
  destruct (dot row key); destruct err; reflexivity.
Qed.

Theorem hidden_pair : forall (row key : list bool) (pos : nat),
  length row = length key ->
  nth_error key pos = Some true ->
  exists bit,
    nth_error row pos = Some bit /\
    flip pos (flip pos row) = row /\
    flip pos row <> row /\
    forall err, noisy (flip pos row) key err = negb (noisy row key err).
Proof.
  intros row key pos same key_bit.
  destruct (row_at pos row key same key_bit) as [bit row_bit].
  exists bit. split.
  - exact row_bit.
  - split.
    + apply flip_twice.
    + split.
      * intro equal.
        pose proof (dot_flip pos row key bit row_bit key_bit) as changed.
        rewrite equal in changed.
        destruct (dot row key); discriminate.
      * intro err. apply noisy_flip with (bit := bit); assumption.
Qed.

Definition nonzero (key : list bool) : Prop :=
  exists pos, nth_error key pos = Some true.

Corollary hidden_nonzero : forall (row key : list bool),
  length row = length key ->
  nonzero key ->
  exists pos bit,
    nth_error row pos = Some bit /\
    flip pos (flip pos row) = row /\
    flip pos row <> row /\
    forall err, noisy (flip pos row) key err = negb (noisy row key err).
Proof.
  intros row key same [pos key_bit].
  destruct (hidden_pair row key pos same key_bit) as [bit paired].
  exists pos, bit. exact paired.
Qed.