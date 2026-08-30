(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Uni.
Require Import Fhe.
Require Import Crypt.
Require Import Host.
Require Import Hop.

Definition ctyp (value : ct) : ty :=
  TEnc (ekey (cty value)) (erem (cty value)).

Definition uval (value : ct) : Uni.value :=
  VEnc (ekey (cty value)) (erem (cty value)) (cval value).

Definition ityp (info : finfo) : ty :=
  TEnc (ekey (ety info)) (erem (ety info)).

Theorem exec_core : forall profile catalog env term out,
  exec profile catalog env term = Some out ->
  ctyp (xct out) = ityp (xinfo out) /\
  hasv (uval (xct out)) (ityp (xinfo out)).
Proof.
  intros profile catalog env term out run.
  pose proof (exec_type profile catalog env term out run) as same.
  pose proof (exec_value profile catalog env term out run) as valid.
  split.
  - unfold ctyp, ityp.
    rewrite same.
    reflexivity.
  - unfold uval, ityp.
    rewrite <- same.
    constructor.
    unfold field, Fp.p.
    apply Fp.valid_range.
    exact valid.
Qed.

Theorem exec_host : forall profile catalog env term out,
  exec profile catalog env term = Some out ->
  Host.typed (ityp (xinfo out)) (uval (xct out)) = true.
Proof.
  intros profile catalog env term out run.
  pose proof (exec_type profile catalog env term out run) as same.
  pose proof (exec_value profile catalog env term out run) as valid.
  unfold Host.typed, ityp, uval.
  rewrite <- same.
  cbn.
  apply andb_true_iff.
  split.
  - apply Nat.eqb_eq. reflexivity.
  - apply andb_true_iff.
    split.
    + apply Nat.eqb_eq. reflexivity.
    + exact valid.
Qed.

Theorem exec_plan : forall profile catalog env term out,
  exec profile catalog env term = Some out ->
  exists plan,
    Hop.lower profile (tenv env) term = Some plan /\
    Hop.hty plan = cty (xct out) /\
    Hop.herase plan = term /\
    Hop.hval profile (tenv env) plan = Some (cty (xct out)).
Proof.
  intros profile catalog env term out run.
  pose proof (exec_check profile catalog env term out run) as checked.
  pose proof (exec_type profile catalog env term out run) as same.
  destruct (Hop.lower_complete _ _ _ _ checked) as [plan [lowered plan_type]].
  pose proof (Hop.lower_erase _ _ _ _ lowered) as erased.
  pose proof (Hop.lower_valid _ _ _ _ lowered) as valid.
  exists plan. split.
  - exact lowered.
  - split.
    + unfold ctyp. rewrite same. exact plan_type.
    + split.
      * exact erased.
      * unfold ctyp. rewrite same. rewrite plan_type in valid. exact valid.
Qed.

Theorem ctyp_data : forall value, data (ctyp value).
Proof.
  intros value.
  exact I.
Qed.

Theorem ctyp_no_eq : forall value, ~ eqty (ctyp value).
Proof.
  intros value equal.
  exact equal.
Qed.