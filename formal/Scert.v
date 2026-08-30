(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.

Require Import Surf.
Require Import Low.
Require Import Bin.
Require Import Cert.

Definition sissue (rules : list Rule.rule) (epoch : nat)
    (items : list sbind) (body : stm) : option bits :=
  match Low.prog items body with
  | Some core => Cert.issue rules epoch core
  | None => None
  end.

Definition sverifyb (rules : list Rule.rule) (epoch : nat)
    (items : list sbind) (body : stm) (input : bits) : bool :=
  match sissue rules epoch items body with
  | Some exact => bits_eqb exact input
  | None => false
  end.

Theorem issue_verify : forall rules epoch items body input,
  sissue rules epoch items body = Some input ->
  sverifyb rules epoch items body input = true.
Proof.
  intros rules epoch items body input issued.
  unfold sverifyb.
  rewrite issued.
  apply (proj2 (bits_eqb_eq input input)).
  reflexivity.
Qed.

Theorem verify_issue : forall rules epoch items body input,
  sverifyb rules epoch items body input = true ->
  sissue rules epoch items body = Some input.
Proof.
  intros rules epoch items body input verified.
  unfold sverifyb in verified.
  destruct (sissue rules epoch items body) as [exact |] eqn:issued;
    try discriminate.
  apply bits_eqb_eq in verified.
  subst exact.
  reflexivity.
Qed.

Theorem verify_sound : forall rules epoch items body input,
  sverifyb rules epoch items body input = true ->
  exists core value,
    Low.prog items body = Some core
      /\ Cert.dec_cert input = Some value
      /\ Cert.cprog value = core
      /\ Cert.verifyb rules epoch input = true.
Proof.
  intros rules epoch items body input verified.
  pose proof (verify_issue rules epoch items body input verified) as issued.
  unfold sissue in issued.
  destruct (Low.prog items body) as [core |] eqn:lowered; try discriminate.
  pose proof (Cert.issue_decode rules epoch core input issued)
    as [id [typ [row [cost decoded]]]].
  pose proof (Cert.issue_verify rules epoch core input issued) as checked.
  exists core,
    (Cert.Cert core (Rule.rid_vals id) typ (Cert.row_norm row) cost).
  repeat split; try assumption.
Qed.

Theorem verify_unique : forall rules epoch items body left right,
  sverifyb rules epoch items body left = true ->
  sverifyb rules epoch items body right = true ->
  left = right.
Proof.
  intros rules epoch items body left right left_ok right_ok.
  pose proof (verify_issue rules epoch items body left left_ok) as left_issue.
  pose proof (verify_issue rules epoch items body right right_ok) as right_issue.
  rewrite right_issue in left_issue.
  inversion left_issue.
  reflexivity.
Qed.

Theorem verify_prog : forall rules epoch litems ritems left right core input,
  Low.prog litems left = Some core ->
  Low.prog ritems right = Some core ->
  sverifyb rules epoch litems left input =
    sverifyb rules epoch ritems right input.
Proof.
  intros rules epoch litems ritems left right core input left_low right_low.
  unfold sverifyb, sissue.
  rewrite left_low, right_low.
  reflexivity.
Qed.