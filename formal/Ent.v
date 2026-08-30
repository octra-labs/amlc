(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.

Require Import Lim.
Require Import Rule.

Record rate : Type := Rate {
  rnum : Z;
  rshift : nat
}.

Record eprof : Type := Eprof {
  ebasis : nat;
  emax : nat;
  ebase : Z;
  eslope : Z;
  er2 : rate;
  er3 : rate
}.

Record eplan : Type := Eplan {
  edepth : nat;
  ecap : Z;
  en2 : Z;
  en3 : Z;
  egroups : Z;
  eedges : Z
}.

Inductive emode : Type :=
| Ebin
| Eint.

Record ebind : Type := Ebind {
  erule : rid;
  emodev : emode;
  eout : eplan
}.

Definition den (value : rate) : Z :=
  Z.pow 2 (Z.of_nat (rshift value)).

Definition rate_b (value : rate) : bool :=
  Z.ltb 0 (rnum value) && Nat.leb (rshift value) 127.

Definition prof_b (value : eprof) : bool :=
  fit (ebasis value) && negb (Nat.eqb (ebasis value) 0)
    && fit (emax value)
    && Z.ltb 0 (ebase value)
    && Z.leb 0 (eslope value)
    && rate_b (er2 value)
    && rate_b (er3 value).

Definition cap (value : eprof) (depth : nat) : Z :=
  ebase value + eslope value * Z.of_nat depth.

Definition scale (value : rate) (amount : Z) : Z :=
  Z.div (amount * rnum value) (den value).

Definition build (value : eprof) (depth : nat) : eplan :=
  let bits := cap value depth in
  let n2 := scale (er2 value) bits in
  let n3 := scale (er3 value) bits in
  Eplan depth bits n2 n3 (n2 + n3) (8 + 2 * n2 + 3 * n3).

Definition plan (value : eprof) (depth : nat) : option eplan :=
  if prof_b value && Nat.leb depth (emax value)
  then Some (build value depth)
  else None.

Definition mode (id : rid) : emode :=
  if Nat.leb 2 (rver id) then Eint else Ebin.

Definition bind (id : rid) (value : eprof) (depth : nat) : option ebind :=
  match plan value depth with
  | Some out => Some (Ebind id (mode id) out)
  | None => None
  end.

Definition bind_at (rules : list rule) (epoch : nat) (value : eprof)
    (depth : nat) : option ebind :=
  match rsel epoch rules with
  | Some selected =>
      if supported selected then bind (rrid selected) value depth else None
  | None => None
  end.

Inductive planR (value : eprof) (depth : nat) : eplan -> Prop :=
| ER :
    prof_b value = true ->
    depth <= emax value ->
    planR value depth (build value depth).

Theorem plan_sound : forall value depth out,
  plan value depth = Some out -> planR value depth out.
Proof.
  intros value depth out H. unfold plan in H.
  destruct (prof_b value && Nat.leb depth (emax value)) eqn:Hv;
    try discriminate.
  inversion H. subst. apply andb_true_iff in Hv as [Hp Hd].
  apply ER; [exact Hp | apply Nat.leb_le; exact Hd].
Qed.

Theorem plan_complete : forall value depth out,
  planR value depth out -> plan value depth = Some out.
Proof.
  intros value depth out H. destruct H as [Hp Hd]. unfold plan.
  rewrite Hp, (proj2 (Nat.leb_le depth (emax value)) Hd). reflexivity.
Qed.

Theorem plan_unique : forall value depth left right,
  planR value depth left -> planR value depth right -> left = right.
Proof.
  intros value depth left right Hl Hr.
  pose proof (plan_complete _ _ _ Hl) as El.
  pose proof (plan_complete _ _ _ Hr) as Er.
  rewrite El in Er. inversion Er. reflexivity.
Qed.

Theorem bind_sound : forall id value depth out,
  bind id value depth = Some out ->
  erule out = id /\ emodev out = mode id /\ plan value depth = Some (eout out).
Proof.
  intros id value depth out H. unfold bind in H.
  destruct (plan value depth) as [found |] eqn:Hplan; try discriminate.
  inversion H. subst. repeat split; reflexivity.
Qed.

Theorem bind_complete : forall id value depth out,
  plan value depth = Some out ->
  bind id value depth = Some (Ebind id (mode id) out).
Proof.
  intros id value depth out H. unfold bind. rewrite H. reflexivity.
Qed.

Theorem bind_at_active : forall rules epoch value depth out,
  bind_at rules epoch value depth = Some out ->
  exists selected,
    rsel epoch rules = Some selected /\
    supported selected = true /\
    active epoch selected = true /\
    erule out = rrid selected /\
    emodev out = mode (rrid selected) /\
    plan value depth = Some (eout out).
Proof.
  intros rules epoch value depth out H. unfold bind_at in H.
  destruct (rsel epoch rules) as [selected |] eqn:Hsel; try discriminate.
  destruct (supported selected) eqn:Hsupport; try discriminate.
  apply bind_sound in H as [Hid [Hmode Hplan]].
  exists selected. repeat split; try assumption.
  eapply rsel_active. exact Hsel.
Qed.

Theorem bind_at_complete : forall rules epoch value depth selected out,
  rsel epoch rules = Some selected ->
  supported selected = true ->
  plan value depth = Some out ->
  bind_at rules epoch value depth =
    Some (Ebind (rrid selected) (mode (rrid selected)) out).
Proof.
  intros rules epoch value depth selected out Hsel Hsupport Hplan.
  unfold bind_at. rewrite Hsel, Hsupport.
  apply bind_complete. exact Hplan.
Qed.

Lemma den_pos : forall value, (0 < den value)%Z.
Proof.
  intros value. unfold den. apply Z.pow_pos_nonneg; lia.
Qed.

Theorem scale_floor : forall value amount,
  (den value * scale value amount <= amount * rnum value <
    den value * (scale value amount + 1))%Z.
Proof.
  intros value amount. pose proof (den_pos value) as Hd.
  unfold scale.
  pose proof (Z.mul_div_le (amount * rnum value) (den value) Hd) as Hl.
  pose proof (Z.div_mod (amount * rnum value) (den value)) as Heq.
  pose proof (Z.mod_pos_bound (amount * rnum value) (den value) Hd) as Hmod.
  assert (Hnz : den value <> 0%Z) by lia.
  specialize (Heq Hnz). split; [exact Hl | lia].
Qed.

Theorem plan_floor : forall value depth out,
  plan value depth = Some out ->
  (den (er2 value) * en2 out <= ecap out * rnum (er2 value) <
      den (er2 value) * (en2 out + 1))%Z /\
  (den (er3 value) * en3 out <= ecap out * rnum (er3 value) <
      den (er3 value) * (en3 out + 1))%Z.
Proof.
  intros value depth out H. apply plan_sound in H. inversion H. subst.
  unfold build. simpl. split; apply scale_floor.
Qed.

Theorem plan_shape : forall value depth out,
  plan value depth = Some out ->
  edepth out = depth /\
  ecap out = cap value depth /\
  egroups out = (en2 out + en3 out)%Z /\
  eedges out = (8 + 2 * en2 out + 3 * en3 out)%Z.
Proof.
  intros value depth out H. apply plan_sound in H. inversion H. subst.
  unfold build. repeat split; reflexivity.
Qed.

Definition prod : eprof :=
  Eprof 337 lim 120%Z 16%Z
    (Rate 4719964527767381%Z 57)
    (Rate 5149052212109869%Z 58).

Theorem prod_valid : prof_b prod = true.
Proof. vm_compute. reflexivity. Qed.

Theorem prod_vals :
  ebasis prod = 337 /\
  emax prod = lim /\
  ebase prod = 120%Z /\
  eslope prod = 16%Z /\
  rnum (er2 prod) = 4719964527767381%Z /\
  rshift (er2 prod) = 57 /\
  den (er2 prod) = 144115188075855872%Z /\
  rnum (er3 prod) = 5149052212109869%Z /\
  rshift (er3 prod) = 58 /\
  den (er3 prod) = 288230376151711744%Z.
Proof. repeat split; reflexivity. Qed.

Theorem prod_zero :
  plan prod 0 = Some (Eplan 0 120 3 2 5 20).
Proof. vm_compute. reflexivity. Qed.

Theorem prod_four :
  plan prod 4 = Some (Eplan 4 184 6 3 9 29).
Proof. vm_compute. reflexivity. Qed.

Theorem prod_4096 :
  plan prod 4096 = Some (Eplan 4096 65656 2150 1172 3322 7824).
Proof. vm_compute. reflexivity. Qed.

Theorem prod_mode_1 :
  bind (Rid 1 local) prod 4 =
    Some (Ebind (Rid 1 local) Ebin (Eplan 4 184 6 3 9 29)).
Proof. unfold bind. rewrite prod_four. reflexivity. Qed.

Theorem prod_mode_2 :
  bind (Rid 2 local) prod 4 =
    Some (Ebind (Rid 2 local) Eint (Eplan 4 184 6 3 9 29)).
Proof. unfold bind. rewrite prod_four. reflexivity. Qed.