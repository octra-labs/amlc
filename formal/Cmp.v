(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.

Require Import Uni.
Require Import Surf.

Inductive rel : Type :=
| Lt
| Le
| Gt
| Ge.

Scheme Equality for rel.

Definition nonnegative (value : Z) : bool :=
  Z.eqb (Z.abs value) value.

Definition decide (relation : rel) (left right : Z) : bool :=
  match relation with
  | Lt => negb (Z.eqb left right) && nonnegative (right - left)
  | Le => nonnegative (right - left)
  | Gt => negb (Z.eqb left right) && nonnegative (left - right)
  | Ge => nonnegative (left - right)
  end.

Definition term (relation : rel) (left_name right_name delta_name : nat)
    (left right : stm) : stm :=
  let left_var := SVar left_name in
  let right_var := SVar right_name in
  let delta_var := SVar delta_name in
  let delta :=
    match relation with
    | Lt | Le => SSub right_var left_var
    | Gt | Ge => SSub left_var right_var
    end
  in
  let positive := SEq TInt (SAbs delta_var) delta_var in
  let result :=
    match relation with
    | Le | Ge => positive
    | Lt | Gt => SIf (SEq TInt left_var right_var)
        (SK (VBool false) TBool) positive
    end
  in
  SLet (SBind left_name MM TInt) left
    (SLet (SBind right_name MM TInt) right
      (SLet (SBind delta_name MM TInt) delta result)).

Theorem nonnegative_spec : forall value,
  nonnegative value = true <-> (0 <= value)%Z.
Proof.
  intros value.
  unfold nonnegative.
  rewrite Z.eqb_eq.
  split.
  - intros same.
    pose proof (Z.abs_nonneg value).
    lia.
  - intros positive.
    apply Z.abs_eq.
    exact positive.
Qed.

Theorem decide_spec : forall relation left right,
  decide relation left right = true <->
  match relation with
  | Lt => (left < right)%Z
  | Le => (left <= right)%Z
  | Gt => (left > right)%Z
  | Ge => (left >= right)%Z
  end.
Proof.
  intros relation left right.
  destruct relation; unfold decide.
  - rewrite andb_true_iff, Bool.negb_true_iff, Z.eqb_neq,
      nonnegative_spec.
    lia.
  - rewrite nonnegative_spec. lia.
  - rewrite andb_true_iff, Bool.negb_true_iff, Z.eqb_neq,
      nonnegative_spec.
    lia.
  - rewrite nonnegative_spec. lia.
Qed.