(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import Bool.
From Stdlib Require Import Arith.

Require Import Surf.

Fixpoint fin_nodes (term : stm) : nat :=
  match term with
  | SK _ _ | SBytes _ | SVnil _ | SVar _ => 1
  | SLet _ value body
  | SPair value body
  | SAdd value body
  | SSub value body
  | SMul value body
  | SDiv value body
  | SMod value body
  | SCat value body
  | SVcat value body
  | SStep value body => 1 + fin_nodes value + fin_nodes body
  | SIf guard yes no => 1 + fin_nodes guard + fin_nodes yes + fin_nodes no
  | SUnpair product _ _ body => 1 + fin_nodes product + fin_nodes body
  | SFst value | SSnd value | SNeg value | SAbs value
  | SInl value _ | SInr _ value
  | SAct _ value | STake _ value | SDrop _ value | SAt _ value
  | SUncons value | SClose value => 1 + fin_nodes value
  | SCase value _ yes _ no =>
      1 + fin_nodes value + fin_nodes yes + fin_nodes no
  | SEq _ lhs rhs => 1 + fin_nodes lhs + fin_nodes rhs
  | SVcons value rest => fin_nodes value + fin_nodes rest
  | SFold _ vector seed _ _ body =>
      1 + fin_nodes vector + fin_nodes seed + fin_nodes body
  end.

Fixpoint fin_depth (term : stm) : nat :=
  match term with
  | SK _ _ | SBytes _ | SVnil _ | SVar _ => 0
  | SLet _ value body
  | SPair value body
  | SAdd value body
  | SSub value body
  | SMul value body
  | SDiv value body
  | SMod value body
  | SCat value body
  | SVcat value body
  | SStep value body => S (Nat.max (fin_depth value) (fin_depth body))
  | SIf guard yes no =>
      S (Nat.max (fin_depth guard)
        (Nat.max (fin_depth yes) (fin_depth no)))
  | SUnpair product _ _ body =>
      S (Nat.max (fin_depth product) (fin_depth body))
  | SFst value | SSnd value | SNeg value | SAbs value
  | SInl value _ | SInr _ value
  | SAct _ value | STake _ value | SDrop _ value | SAt _ value
  | SUncons value | SClose value => S (fin_depth value)
  | SCase value _ yes _ no =>
      S (Nat.max (fin_depth value)
        (Nat.max (fin_depth yes) (fin_depth no)))
  | SEq _ lhs rhs => S (Nat.max (fin_depth lhs) (fin_depth rhs))
  | SVcons value rest => Nat.max (S (fin_depth value)) (fin_depth rest)
  | SFold _ vector seed _ _ body =>
      S (Nat.max (fin_depth vector)
        (Nat.max (fin_depth seed) (fin_depth body)))
  end.

Definition node_max : nat := 100 * 1000.

Definition depth_max : nat := 64 * 64.

Definition fin_fit (node_count depth_count : nat) : bool :=
  Nat.leb node_count node_max && Nat.leb depth_count depth_max.

Definition fin_valid (term : stm) : bool :=
  fin_fit (fin_nodes term) (fin_depth term).

Theorem fin_fit_spec : forall node_count depth_count,
  fin_fit node_count depth_count = true <->
  node_count <= node_max /\ depth_count <= depth_max.
Proof.
  intros node_count depth_count.
  unfold fin_fit.
  rewrite andb_true_iff, !Nat.leb_le.
  reflexivity.
Qed.

Theorem fin_valid_spec : forall term,
  fin_valid term = true <->
  fin_nodes term <= node_max /\ fin_depth term <= depth_max.
Proof.
  intros term.
  unfold fin_valid.
  apply fin_fit_spec.
Qed.