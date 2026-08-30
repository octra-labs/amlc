(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Require Import Uni.
Require Import Dec.

Import ListNotations.

Lemma ty_eqb_eq : forall left right,
  ty_eqb left right = true <-> left = right.
Proof.
  intros left right.
  unfold ty_eqb.
  destruct (ty_dec left right) as [same | diff].
  - split; [intros _; exact same | intros _; reflexivity].
  - split; [discriminate | intros same; contradiction].
Qed.

Lemma ty_eqb_refl : forall typ, ty_eqb typ typ = true.
Proof.
  intros typ.
  apply ty_eqb_eq.
  reflexivity.
Qed.

Lemma ctx_eqb_eq : forall left right,
  ctx_eqb left right = true <-> left = right.
Proof.
  intros left right.
  unfold ctx_eqb.
  destruct (ctx_dec left right) as [same | diff].
  - split; [intros _; exact same | intros _; reflexivity].
  - split; [discriminate | intros same; contradiction].
Qed.

Lemma ctx_eqb_refl : forall gamma, ctx_eqb gamma gamma = true.
Proof.
  intros gamma.
  apply ctx_eqb_eq.
  reflexivity.
Qed.

Lemma data_b_spec : forall typ,
  data_b typ = true <-> data typ.
Proof.
  induction typ; simpl.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - destruct n.
    + tauto.
    + exact IHtyp.
  - split; [discriminate | contradiction].
  - tauto.
  - rewrite andb_true_iff, IHtyp1, IHtyp2.
    tauto.
  - rewrite andb_true_iff, IHtyp1, IHtyp2.
    tauto.
Qed.

Lemma eq_b_spec : forall typ,
  eq_b typ = true <-> eqty typ.
Proof.
  induction typ; simpl.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - destruct n.
    + tauto.
    + exact IHtyp.
  - split; [discriminate | contradiction].
  - split; [discriminate | contradiction].
  - rewrite andb_true_iff, IHtyp1, IHtyp2.
    tauto.
  - rewrite andb_true_iff, IHtyp1, IHtyp2.
    tauto.
Qed.

Lemma bytes_b_spec : forall bytes,
  bytes_b bytes = true <-> Forall (fun byte => byte < 256) bytes.
Proof.
  induction bytes as [|byte rest repeat]; simpl.
  - split; intros; constructor.
  - rewrite andb_true_iff, Nat.ltb_lt, repeat.
    split.
    + intros [head tail].
      constructor; assumption.
    + intros accepted.
      inversion accepted; subst.
      split; assumption.
Qed.

Lemma fresh_b_spec : forall id gamma,
  fresh_b id gamma = true <-> fresh id gamma.
Proof.
  intros id gamma.
  unfold fresh_b, fresh.
  split.
  - intros absent present.
    apply Bool.negb_true_iff in absent.
    assert (found : existsb (Nat.eqb id) (ids gamma) = true).
    { apply existsb_exists.
      exists id.
      split; [exact present | apply Nat.eqb_refl]. }
    rewrite absent in found.
    discriminate.
  - intros absent.
    apply Bool.negb_true_iff.
    destruct (existsb (Nat.eqb id) (ids gamma)) eqn:found; [|reflexivity].
    apply existsb_exists in found.
    destruct found as [value [present same]].
    apply Nat.eqb_eq in same.
    subst value.
    contradiction.
Qed.

Lemma takeb_sound : forall id gamma typ next,
  takeb id gamma = Some (typ, next) -> takec id gamma typ next.
Proof.
  intros id gamma.
  induction gamma as [|slot rest repeat]; intros typ next found.
  - discriminate.
  - destruct slot as [sid mode sty live].
    cbn in found.
    destruct (Nat.eqb sid id) eqn:same.
    + apply Nat.eqb_eq in same.
      subst sid.
      destruct mode.
      * discriminate.
      * destruct live; try discriminate.
        inversion found; subst.
        constructor.
      * destruct (data_b sty) eqn:kind; try discriminate.
        inversion found; subst.
        apply TCMany.
        apply data_b_spec.
        exact kind.
    + apply Nat.eqb_neq in same.
      destruct (takeb id rest) as [[tail_ty tail_next] |] eqn:tail; try discriminate.
      inversion found; subst.
      apply TCNext.
      * exact same.
      * apply repeat.
        reflexivity.
Qed.

Lemma takeb_complete : forall id gamma typ next,
  takec id gamma typ next -> takeb id gamma = Some (typ, next).
Proof.
  intros id gamma typ next taken.
  induction taken.
  - cbn.
    rewrite Nat.eqb_refl.
    reflexivity.
  - cbn.
    rewrite Nat.eqb_refl.
    rewrite (proj2 (data_b_spec typ) H).
    reflexivity.
  - destruct head as [sid mode sty live].
    cbn in *.
    assert (different : Nat.eqb sid id = false).
    { apply Nat.eqb_neq.
      exact H. }
    rewrite different, IHtaken.
    reflexivity.
Qed.

Lemma openb_sound : forall binder gamma next,
  openb binder gamma = Some next -> openc binder gamma next.
Proof.
  intros [id mode typ] gamma next found.
  unfold openb in found.
  cbn in found.
  destruct (fresh_b id gamma) eqn:is_fresh; try discriminate.
  apply fresh_b_spec in is_fresh.
  destruct mode.
  - destruct (data_b typ) eqn:is_data; try discriminate.
    inversion found; subst.
    apply OCZero.
    + apply data_b_spec.
      exact is_data.
    + exact is_fresh.
  - inversion found; subst.
    apply OCOne.
    exact is_fresh.
  - destruct (data_b typ) eqn:is_data; try discriminate.
    inversion found; subst.
    apply OCMany.
    + apply data_b_spec.
      exact is_data.
    + exact is_fresh.
Qed.

Lemma openb_complete : forall binder gamma next,
  openc binder gamma next -> openb binder gamma = Some next.
Proof.
  intros binder gamma next opened.
  induction opened.
  - unfold openb.
    cbn.
    rewrite (proj2 (fresh_b_spec id gamma) H0).
    rewrite (proj2 (data_b_spec typ) H).
    reflexivity.
  - unfold openb.
    cbn.
    rewrite (proj2 (fresh_b_spec id gamma) H).
    reflexivity.
  - unfold openb.
    cbn.
    rewrite (proj2 (fresh_b_spec id gamma) H0).
    rewrite (proj2 (data_b_spec typ) H).
    reflexivity.
Qed.

Lemma closeb_sound : forall binder gamma next,
  closeb binder gamma = Some next -> closec binder gamma next.
Proof.
  intros [id mode typ] gamma next found.
  destruct mode.
  - cbn in found.
    inversion found; subst.
    constructor.
  - destruct gamma as [|slot rest]; try discriminate.
    destruct slot as [sid smode sty live].
    destruct smode; try discriminate.
    destruct live.
    + discriminate.
    + cbn in found.
      destruct (Nat.eqb sid id && ty_eqb sty typ) eqn:same; try discriminate.
      apply andb_true_iff in same.
      destruct same as [same_id same_ty].
      apply Nat.eqb_eq in same_id.
      apply ty_eqb_eq in same_ty.
      subst sid sty.
      inversion found; subst.
      constructor.
  - destruct gamma as [|slot rest]; try discriminate.
    destruct slot as [sid smode sty live].
    destruct smode; try discriminate.
    cbn in found.
    destruct (Nat.eqb sid id && ty_eqb sty typ) eqn:same; try discriminate.
    apply andb_true_iff in same.
    destruct same as [same_id same_ty].
    apply Nat.eqb_eq in same_id.
    apply ty_eqb_eq in same_ty.
    subst sid sty.
    inversion found; subst.
    constructor.
Qed.

Lemma closeb_complete : forall binder gamma next,
  closec binder gamma next -> closeb binder gamma = Some next.
Proof.
  intros binder gamma next closed.
  induction closed; cbn.
  - reflexivity.
  - rewrite Nat.eqb_refl, ty_eqb_refl.
    reflexivity.
  - rewrite Nat.eqb_refl, ty_eqb_refl.
    reflexivity.
Qed.

Lemma ktype_sound : forall value typ,
  ktype value typ = true -> base typ /\ hasv value typ.
Proof.
  intros value typ accepted.
  destruct value, typ; cbn in accepted; try discriminate;
    split; constructor.
Qed.

Lemma ktype_complete : forall value typ,
  base typ -> hasv value typ -> ktype value typ = true.
Proof.
  intros value typ scalar typed.
  inversion scalar; subst; inversion typed; reflexivity.
Qed.

Opaque takeb openb closeb.