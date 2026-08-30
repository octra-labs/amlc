(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import Arith Lia ZArith.

Require Import Uni.

Theorem fuel_eval :
  (forall sigma term out next (ran : evalR sigma term out next),
    forall fuel, rs out <= fuel ->
      run_fuel fuel sigma term = Done out next) /\
  (forall sigma item state body values seed out next
      (ran : foldR sigma item state body values seed out next),
    forall fuel, rs out <= fuel ->
      fold_fuel fuel sigma item state body values seed = Done out next).
Proof.
  apply run_ind.
  - intros sigma value typ fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    apply keep_run.
    exact enough.
  - intros sigma bytes fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    apply keep_run.
    exact enough.
  - intros sigma elem fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    apply keep_run.
    exact enough.
  - intros sigma id value next read fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (takef_run id sigma value next read).
    apply keep_run.
    exact enough.
  - intros sigma id typ value body out next ran body_ih fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (body_ih fuel) by (simpl in enough; lia).
    apply keep_run.
    exact enough.
  - intros sigma id typ value body value_out mid opened body_out prior next
      value_run value_ih opened_run body_run body_ih closed fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (value_ih fuel) by (simpl in enough; lia).
    rewrite (openf_run _ _ _ _ opened_run).
    rewrite (body_ih fuel) by (simpl in enough; lia).
    rewrite (closef_run _ _ _ closed).
    apply keep_run.
    exact enough.
  - intros sigma id typ value body value_out mid opened body_out prior next
      value_run value_ih opened_run body_run body_ih closed fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (value_ih fuel) by (simpl in enough; lia).
    rewrite (openf_run _ _ _ _ opened_run).
    rewrite (body_ih fuel) by (simpl in enough; lia).
    rewrite (closef_run _ _ _ closed).
    apply keep_run.
    exact enough.
  - intros sigma guard yes no guard_out mid body_out next guard_run guard_ih
      guard_value body_run body_ih fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (guard_ih fuel) by (simpl in enough; lia).
    rewrite guard_value.
    cbn.
    rewrite (body_ih fuel) by (simpl in enough; lia).
    apply keep_run.
    exact enough.
  - intros sigma guard yes no guard_out mid body_out next guard_run guard_ih
      guard_value body_run body_ih fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (guard_ih fuel) by (simpl in enough; lia).
    rewrite guard_value.
    cbn.
    rewrite (body_ih fuel) by (simpl in enough; lia).
    apply keep_run.
    exact enough.
  - intros sigma left right left_out mid right_out next left_run left_ih
      right_run right_ih fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (left_ih fuel) by (simpl in enough; lia).
    rewrite (right_ih fuel) by (simpl in enough; lia).
    apply keep_run.
    exact enough.
  - intros sigma pair left right body pair_out mid lv rvv first second
      body_out prior last next pair_run pair_ih pair_value left_open right_open
      body_run body_ih right_close left_close fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (pair_ih fuel) by (simpl in enough; lia).
    rewrite pair_value.
    rewrite (openf_run _ _ _ _ left_open).
    rewrite (openf_run _ _ _ _ right_open).
    rewrite (body_ih fuel) by (simpl in enough; lia).
    rewrite (closef_run _ _ _ right_close).
    rewrite (closef_run _ _ _ left_close).
    apply keep_run.
    exact enough.
  - intros sigma pair pair_out next left right pair_run pair_ih pair_value fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (pair_ih fuel) by (simpl in enough; lia).
    rewrite pair_value.
    apply keep_run.
    exact enough.
  - intros sigma pair pair_out next left right pair_run pair_ih pair_value fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (pair_ih fuel) by (simpl in enough; lia).
    rewrite pair_value.
    apply keep_run.
    exact enough.
  - intros sigma value right out next value_run value_ih fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (value_ih fuel) by (simpl in enough; lia).
    apply keep_run.
    exact enough.
  - intros sigma left value out next value_run value_ih fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (value_ih fuel) by (simpl in enough; lia).
    apply keep_run.
    exact enough.
  - intros sigma value left yes right no value_out mid payload opened body_out
      prior next value_run value_ih value_shape opened_run body_run body_ih
      closed fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (value_ih fuel) by (simpl in enough; lia).
    rewrite value_shape.
    rewrite (openf_run _ _ _ _ opened_run).
    rewrite (body_ih fuel) by (simpl in enough; lia).
    rewrite (closef_run _ _ _ closed).
    apply keep_run.
    exact enough.
  - intros sigma value left yes right no value_out mid payload opened body_out
      prior next value_run value_ih value_shape opened_run body_run body_ih
      closed fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (value_ih fuel) by (simpl in enough; lia).
    rewrite value_shape.
    rewrite (openf_run _ _ _ _ opened_run).
    rewrite (body_ih fuel) by (simpl in enough; lia).
    rewrite (closef_run _ _ _ closed).
    apply keep_run.
    exact enough.
  - intros sigma action body out next body_run body_ih fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (body_ih fuel) by (simpl in enough; lia).
    apply keep_run.
    exact enough.
  - intros sigma left right left_out mid right_out next x y left_run left_ih
      right_run right_ih left_value right_value fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (left_ih fuel) by (simpl in enough; lia).
    rewrite (right_ih fuel) by (simpl in enough; lia).
    rewrite left_value, right_value.
    apply keep_run.
    exact enough.
  - intros sigma left right left_out mid right_out next x y left_run left_ih
      right_run right_ih left_value right_value fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (left_ih fuel) by (simpl in enough; lia).
    rewrite (right_ih fuel) by (simpl in enough; lia).
    rewrite left_value, right_value.
    apply keep_run.
    exact enough.
  - intros sigma left right left_out mid right_out next x y left_run left_ih
      right_run right_ih left_value right_value fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (left_ih fuel) by (simpl in enough; lia).
    rewrite (right_ih fuel) by (simpl in enough; lia).
    rewrite left_value, right_value.
    apply keep_run.
    exact enough.
  - intros sigma left right left_out mid right_out next x y left_run left_ih
      right_run right_ih left_value right_value nonzero fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (left_ih fuel) by (simpl in enough; lia).
    rewrite (right_ih fuel) by (simpl in enough; lia).
    rewrite left_value, right_value.
    assert (zero : Z.eqb y 0 = false) by
      (apply Z.eqb_neq; exact nonzero).
    rewrite zero.
    apply keep_run.
    exact enough.
  - intros sigma left right left_out mid right_out next x y left_run left_ih
      right_run right_ih left_value right_value nonzero fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (left_ih fuel) by (simpl in enough; lia).
    rewrite (right_ih fuel) by (simpl in enough; lia).
    rewrite left_value, right_value.
    assert (zero : Z.eqb y 0 = false) by
      (apply Z.eqb_neq; exact nonzero).
    rewrite zero.
    apply keep_run.
    exact enough.
  - intros sigma value out next number value_run value_ih value_shape fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (value_ih fuel) by (simpl in enough; lia).
    rewrite value_shape.
    apply keep_run.
    exact enough.
  - intros sigma value out next number value_run value_ih value_shape fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (value_ih fuel) by (simpl in enough; lia).
    rewrite value_shape.
    apply keep_run.
    exact enough.
  - intros sigma typ left right left_out mid right_out next left_run left_ih
      right_run right_ih fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (left_ih fuel) by (simpl in enough; lia).
    rewrite (right_ih fuel) by (simpl in enough; lia).
    apply keep_run.
    exact enough.
  - intros sigma left right left_out mid right_out next x y left_run left_ih
      right_run right_ih left_value right_value fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (left_ih fuel) by (simpl in enough; lia).
    rewrite (right_ih fuel) by (simpl in enough; lia).
    rewrite left_value, right_value.
    apply keep_run.
    exact enough.
  - intros sigma len value out next bytes value_run value_ih value_shape accepted
      fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (value_ih fuel) by (simpl in enough; lia).
    rewrite value_shape.
    assert (within : Nat.leb len (length bytes) = true)
      by (apply Nat.leb_le; exact accepted).
    rewrite within.
    apply keep_run.
    exact enough.
  - intros sigma len value out next bytes value_run value_ih value_shape accepted
      fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (value_ih fuel) by (simpl in enough; lia).
    rewrite value_shape.
    assert (within : Nat.leb len (length bytes) = true)
      by (apply Nat.leb_le; exact accepted).
    rewrite within.
    apply keep_run.
    exact enough.
  - intros sigma first rest first_out mid rest_out next values first_run first_ih
      rest_run rest_ih rest_shape fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (first_ih fuel) by (simpl in enough; lia).
    rewrite (rest_ih fuel) by (simpl in enough; lia).
    rewrite rest_shape.
    apply keep_run.
    exact enough.
  - intros sigma left right left_out mid right_out next x y left_run left_ih
      right_run right_ih left_value right_value fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (left_ih fuel) by (simpl in enough; lia).
    rewrite (right_ih fuel) by (simpl in enough; lia).
    rewrite left_value, right_value.
    apply keep_run.
    exact enough.
  - intros sigma index value out next values item value_run value_ih value_shape
      found fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (value_ih fuel) by (simpl in enough; lia).
    rewrite value_shape, found.
    apply keep_run.
    exact enough.
  - intros sigma value out next first rest value_run value_ih value_shape fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (value_ih fuel) by (simpl in enough; lia).
    rewrite value_shape.
    apply keep_run.
    exact enough.
  - intros sigma n vector seed item state body vector_out mid values seed_out outer
      fold_out next vector_run vector_ih vector_shape vector_len seed_run seed_ih
      fold_run fold_ih fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (vector_ih fuel) by (simpl in enough; lia).
    rewrite vector_shape.
    assert (same : Nat.eqb (length values) n = true)
      by (apply Nat.eqb_eq; exact vector_len).
    rewrite same.
    rewrite (seed_ih fuel) by (simpl in enough; lia).
    rewrite (fold_ih fuel) by (simpl in enough; lia).
    apply keep_run.
    exact enough.
  - intros sigma cap value cap_out mid value_out next kind id cap_run cap_ih
      value_run value_ih cap_shape fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (cap_ih fuel) by (simpl in enough; lia).
    rewrite (value_ih fuel) by (simpl in enough; lia).
    rewrite cap_shape.
    apply keep_run.
    exact enough.
  - intros sigma cap out next kind id cap_run cap_ih cap_shape fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [run_fuel].
    rewrite (cap_ih fuel) by (simpl in enough; lia).
    rewrite cap_shape.
    apply keep_run.
    exact enough.
  - intros sigma item state body value fuel enough.
    destruct fuel; reflexivity.
  - intros sigma item state body first rest value opened_item opened_state head
      prior after_state outer tail next item_open state_open body_run body_ih
      state_close item_close tail_run tail_ih fuel enough.
    destruct fuel as [|fuel]; [simpl in enough; lia |].
    cbn [fold_fuel].
    rewrite (openf_run _ _ _ _ item_open).
    rewrite (openf_run _ _ _ _ state_open).
    rewrite (body_ih fuel) by (simpl in enough; lia).
    rewrite (closef_run _ _ _ state_close).
    rewrite (closef_run _ _ _ item_close).
    rewrite (tail_ih fuel) by (simpl in enough; lia).
    apply keep_run.
    exact enough.
Qed.

Theorem fuel_enough : forall gamma term typ row budget next sigma,
  check gamma term typ row budget next ->
  env_ok gamma sigma ->
  (exists out final,
    run_fuel (rsteps budget) sigma term = Done out final) \/
  (exists reason,
    run_fuel (rsteps budget) sigma term = Rejected reason).
Proof.
  exact terminal.
Qed.

Corollary fuel_not_out : forall gamma term typ row budget next sigma,
  check gamma term typ row budget next ->
  env_ok gamma sigma ->
  run_fuel (rsteps budget) sigma term <> OutOfFuel.
Proof.
  intros gamma term typ row budget next sigma checked matched denied.
  destruct (fuel_enough gamma term typ row budget next sigma checked matched)
    as [[out [final ran]] | [reason ran]].
  - rewrite ran in denied.
    discriminate.
  - rewrite ran in denied.
    discriminate.
Qed.

Corollary fuel_not_stuck : forall gamma term typ row budget next sigma,
  check gamma term typ row budget next ->
  env_ok gamma sigma ->
  run_fuel (rsteps budget) sigma term <> Stuck.
Proof.
  intros gamma term typ row budget next sigma checked matched denied.
  destruct (fuel_enough gamma term typ row budget next sigma checked matched)
    as [[out [final ran]] | [reason ran]].
  - rewrite ran in denied.
    discriminate.
  - rewrite ran in denied.
    discriminate.
Qed.