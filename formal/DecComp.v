(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Require Import Uni.
Require Import Dec.
Require Import DecRel.

Import ListNotations.

Opaque takeb openb closeb.

Theorem checkb_complete : forall gamma term typ row cost next,
  check gamma term typ row cost next ->
  checkb gamma term = Some (typ, row, cost, next).
Proof.
  intros gamma term typ row cost next checked.
  induction checked.
  - cbn.
    rewrite (ktype_complete value typ H H0).
    reflexivity.
  - cbn.
    rewrite (proj2 (bytes_b_spec bytes) H).
    reflexivity.
  - reflexivity.
  - cbn.
    rewrite (takeb_complete id gamma typ next H).
    reflexivity.
  - cbn.
    rewrite IHchecked1, ty_eqb_refl, ctx_eqb_refl.
    rewrite (openb_complete (Bind id M0 typ) gamma opened H).
    rewrite IHchecked2.
    rewrite (closeb_complete (Bind id M0 typ) prior next H0).
    reflexivity.
  - cbn.
    rewrite IHchecked1, ty_eqb_refl.
    rewrite (openb_complete (Bind id M1 typ) mid opened H).
    rewrite IHchecked2.
    rewrite (closeb_complete (Bind id M1 typ) prior next H0).
    reflexivity.
  - cbn.
    rewrite IHchecked1, ty_eqb_refl.
    rewrite (openb_complete (Bind id MM typ) mid opened H).
    rewrite IHchecked2.
    rewrite (closeb_complete (Bind id MM typ) prior next H0).
    reflexivity.
  - cbn.
    rewrite IHchecked1, ty_eqb_refl, IHchecked2, IHchecked3.
    rewrite ty_eqb_refl, ctx_eqb_refl.
    reflexivity.
  - cbn.
    rewrite IHchecked1, IHchecked2.
    reflexivity.
  - cbn.
    rewrite IHchecked1, H, H0.
    repeat rewrite ty_eqb_refl.
    rewrite (openb_complete left mid first H1).
    rewrite (openb_complete right first second H2).
    rewrite IHchecked2.
    rewrite (closeb_complete right prior last H3).
    rewrite (closeb_complete left last next H4).
    reflexivity.
  - cbn.
    rewrite IHchecked.
    rewrite (proj2 (data_b_spec right) H).
    reflexivity.
  - cbn.
    rewrite IHchecked.
    rewrite (proj2 (data_b_spec left) H).
    reflexivity.
  - cbn.
    rewrite IHchecked.
    reflexivity.
  - cbn.
    rewrite IHchecked.
    reflexivity.
  - cbn.
    rewrite IHchecked1, H, H0.
    repeat rewrite ty_eqb_refl.
    rewrite (openb_complete left mid ly H1).
    rewrite (openb_complete right mid ln H3).
    rewrite IHchecked2, IHchecked3.
    rewrite (closeb_complete left py next H2).
    rewrite (closeb_complete right pn next H4).
    rewrite ty_eqb_refl, ctx_eqb_refl.
    reflexivity.
  - cbn.
    rewrite IHchecked.
    reflexivity.
  - cbn.
    rewrite IHchecked1, ty_eqb_refl, IHchecked2, ty_eqb_refl.
    reflexivity.
  - cbn.
    rewrite IHchecked1, ty_eqb_refl, IHchecked2, ty_eqb_refl.
    reflexivity.
  - cbn.
    rewrite IHchecked1, ty_eqb_refl, IHchecked2, ty_eqb_refl.
    reflexivity.
  - cbn.
    rewrite IHchecked1, ty_eqb_refl, IHchecked2, ty_eqb_refl.
    reflexivity.
  - cbn.
    rewrite IHchecked1, ty_eqb_refl, IHchecked2, ty_eqb_refl.
    reflexivity.
  - cbn.
    rewrite IHchecked, ty_eqb_refl.
    reflexivity.
  - cbn.
    rewrite IHchecked, ty_eqb_refl.
    reflexivity.
  - cbn.
    rewrite IHchecked1.
    rewrite (proj2 (eq_b_spec typ) H).
    rewrite IHchecked2, ty_eqb_refl.
    reflexivity.
  - cbn.
    rewrite IHchecked1, IHchecked2.
    reflexivity.
  - cbn.
    rewrite IHchecked.
    assert (accepted : Nat.leb len total = true).
    { apply Nat.leb_le.
      exact H. }
    rewrite accepted.
    reflexivity.
  - cbn.
    rewrite IHchecked.
    assert (accepted : Nat.leb len total = true).
    { apply Nat.leb_le.
      exact H. }
    rewrite accepted.
    reflexivity.
  - cbn.
    rewrite IHchecked1, IHchecked2, ty_eqb_refl.
    reflexivity.
  - cbn.
    rewrite IHchecked1, IHchecked2, ty_eqb_refl.
    reflexivity.
  - destruct len as [|len]; [lia |].
    cbn.
    rewrite IHchecked.
    assert (accepted : Nat.leb index len = true).
    { apply Nat.leb_le.
      lia. }
    rewrite accepted.
    rewrite (proj2 (data_b_spec elem) H0).
    reflexivity.
  - cbn.
    rewrite IHchecked.
    reflexivity.
  - cbn.
    rewrite IHchecked1, Nat.eqb_refl, H, ty_eqb_refl.
    rewrite IHchecked2, H0, ty_eqb_refl.
    rewrite (openb_complete item outer opened_item H1).
    rewrite (openb_complete state opened_item opened_state H2).
    rewrite IHchecked3, ty_eqb_refl.
    rewrite (closeb_complete state prior after_state H3).
    rewrite (closeb_complete item after_state outer H4).
    rewrite ctx_eqb_refl.
    reflexivity.
  - cbn.
    rewrite IHchecked1, IHchecked2.
    reflexivity.
  - cbn.
    rewrite IHchecked.
    reflexivity.
Qed.