(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import NArith.

Require Import Pbin.
Require Import Sbin.
Require Import Sess.
Require Import Sha.
Require Import Bin.

Import ListNotations.

Definition root_tag : list nat := [65; 77; 76; 50; 82; 79; 79; 84; 1].

Definition bit_at (index : nat) (input : bits) : nat :=
  if nth index input false then 1 else 0.

Definition octet (input : bits) : nat :=
  bit_at 0 input * 128 + bit_at 1 input * 64 +
  bit_at 2 input * 32 + bit_at 3 input * 16 +
  bit_at 4 input * 8 + bit_at 5 input * 4 +
  bit_at 6 input * 2 + bit_at 7 input.

Fixpoint packn (fuel : nat) (input : bits) : list nat :=
  match fuel, input with
  | 0, _ | _, [] => []
  | S rest, _ => octet input :: packn rest (skipn 8 input)
  end.

Definition pack (input : bits) : list nat :=
  packn ((length input + 7) / 8) input.

Definition image (input : bits) : list nat :=
  Sha.be64 (N.of_nat (length input)) ++ pack input.

Definition prior_b (prior : list nat) : bool :=
  Nat.eqb (length prior) 32 && forallb byte_b prior.

Definition link
    (program : bits) (prior : list nat) (state : bits)
    : option (Pbin.program * sview) :=
  match Pbin.dec_prog program, Sbin.dec_view state with
  | Some term, Some view =>
      if prior_b prior then
        if bytes_eqb (sprog (vscope view)) (image program) then
          if bytes_eqb (sroot (vscope view)) prior then Some (term, view)
          else None
        else None
      else None
  | _, _ => None
  end.

Definition frame (program : bits) (prior : list nat) (state : bits)
    : list nat :=
  root_tag ++ image program ++ prior ++ image state.

Definition root (program : bits) (prior : list nat) (state : bits)
    : option (list nat) :=
  match link program prior state with
  | Some _ => Some (Sha.hash (frame program prior state))
  | None => None
  end.

Theorem prior_b_spec : forall prior,
  prior_b prior = true ->
  length prior = 32 /\ forallb byte_b prior = true.
Proof.
  intros prior valid.
  unfold prior_b in valid.
  rewrite andb_true_iff, Nat.eqb_eq in valid.
  exact valid.
Qed.

Theorem link_prog_exact : forall program prior state term view,
  link program prior state = Some (term, view) ->
  Pbin.enc_prog term = Some program.
Proof.
  intros program prior state term view accepted.
  unfold link in accepted.
  destruct (Pbin.dec_prog program) as [found |] eqn:program_ok;
    try discriminate.
  destruct (Sbin.dec_view state) as [seen |] eqn:state_ok;
    try discriminate.
  destruct (prior_b prior); try discriminate.
  destruct (bytes_eqb (sprog (vscope seen)) (image program));
    try discriminate.
  destruct (bytes_eqb (sroot (vscope seen)) prior); try discriminate.
  inversion accepted; subst.
  apply Pbin.prog_encode_decode.
  exact program_ok.
Qed.

Theorem link_state_exact : forall program prior state term view,
  link program prior state = Some (term, view) ->
  Sbin.enc_view view = state.
Proof.
  intros program prior state term view accepted.
  unfold link in accepted.
  destruct (Pbin.dec_prog program) as [found |] eqn:program_ok;
    try discriminate.
  destruct (Sbin.dec_view state) as [seen |] eqn:state_ok;
    try discriminate.
  destruct (prior_b prior); try discriminate.
  destruct (bytes_eqb (sprog (vscope seen)) (image program));
    try discriminate.
  destruct (bytes_eqb (sroot (vscope seen)) prior); try discriminate.
  inversion accepted; subst.
  apply Sbin.view_encode_decode.
  exact state_ok.
Qed.

Theorem link_scope : forall program prior state term view,
  link program prior state = Some (term, view) ->
  sprog (vscope view) = image program /\ sroot (vscope view) = prior.
Proof.
  intros program prior state term view accepted.
  unfold link in accepted.
  destruct (Pbin.dec_prog program) as [found |] eqn:program_ok;
    try discriminate.
  destruct (Sbin.dec_view state) as [seen |] eqn:state_ok;
    try discriminate.
  destruct (prior_b prior); try discriminate.
  destruct (bytes_eqb (sprog (vscope seen)) (image program))
    eqn:program_scope; try discriminate.
  destruct (bytes_eqb (sroot (vscope seen)) prior)
    eqn:root_scope; try discriminate.
  inversion accepted; subst.
  rewrite bytes_eqb_eq in program_scope, root_scope.
  split; assumption.
Qed.

Theorem root_length : forall program prior state digest,
  root program prior state = Some digest -> length digest = 32.
Proof.
  intros program prior state digest accepted.
  unfold root in accepted.
  destruct (link program prior state) as [[term view] |]; try discriminate.
  inversion accepted; subst.
  apply Sha.hash_length.
Qed.

Theorem root_value : forall program prior state digest,
  root program prior state = Some digest ->
  digest = Sha.hash (frame program prior state).
Proof.
  intros program prior state digest accepted.
  unfold root in accepted.
  destruct (link program prior state) as [[term view] |]; try discriminate.
  inversion accepted.
  reflexivity.
Qed.