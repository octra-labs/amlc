(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import String.

Require Import Uni.
Require Import Comp.
Require Import Src.
Require Import Rval.

Import ListNotations.

Inductive lit : Type :=
| LBool : bool -> lit
| LInt : Z -> lit
| LBytes : list nat -> lit
| LData : Rval.rval -> lit.

Definition lty (value : lit) : ty :=
  match value with
  | LBool _ => TBool
  | LInt _ => TInt
  | LBytes raw => TBytes (List.length raw)
  | LData item => Rval.rtyp item
  end.

Definition octet_b (value : nat) : bool := Nat.ltb value 256.

Definition data_of (typ : ty) (value : value) : option lit :=
  let item := Rval.RVal typ value in
  if Rval.rval_b item then Some (LData item) else None.

Definition lit_of (typ : ty) (value : value) : option lit :=
  match typ with
  | TBool =>
      match value with
      | VBool flag => Some (LBool flag)
      | _ => None
      end
  | TInt =>
      match value with
      | VInt number => Some (LInt number)
      | _ => None
      end
  | TBytes size =>
      match value with
      | VBytes raw =>
          if Nat.eqb size (List.length raw) && forallb octet_b raw
          then Some (LBytes raw)
          else None
      | _ => None
      end
  | _ => data_of typ value
  end.

Definition emit (image : Comp.image) : option lit :=
  match Comp.iins image, Comp.irow image with
  | [], [] =>
      match run_fuel (rsteps (Comp.icost image)) [] (Comp.iterm image) with
      | Done out final =>
          match final, rp out with
          | [], [] => lit_of (Comp.ityp image) (rv out)
          | _, _ => None
          end
      | Rejected _ | OutOfFuel | Stuck => None
      end
  | _, _ => None
  end.

Inductive rep : ty -> value -> lit -> Prop :=
| RBool : forall flag, rep TBool (VBool flag) (LBool flag)
| RInt : forall number, rep TInt (VInt number) (LInt number)
| RBytes : forall raw,
    Forall (fun value => value < 256) raw ->
    rep (TBytes (List.length raw)) (VBytes raw) (LBytes raw)
| RData : forall item,
    Rval.rval_b item = true ->
    rep (Rval.rtyp item) (Rval.rvalue item) (LData item).

Lemma data_of_sound : forall typ value out,
  data_of typ value = Some out -> rep typ value out.
Proof.
  intros typ value out accepted.
  unfold data_of in accepted.
  destruct (Rval.rval_b (Rval.RVal typ value)) eqn:valid; try discriminate.
  inversion accepted; subst out.
  change
    (rep (Rval.rtyp (Rval.RVal typ value))
      (Rval.rvalue (Rval.RVal typ value)) (LData (Rval.RVal typ value))).
  apply RData.
  exact valid.
Qed.

Lemma octets_forall : forall raw,
  forallb octet_b raw = true -> Forall (fun value => value < 256) raw.
Proof.
  induction raw as [|value rest IH]; simpl.
  - intros _.
    constructor.
  - rewrite andb_true_iff.
    intros [head tail].
    constructor.
    + apply Nat.ltb_lt.
      exact head.
    + apply IH.
      exact tail.
Qed.

Theorem lit_of_sound : forall typ value out,
  lit_of typ value = Some out -> rep typ value out.
Proof.
  intros typ value out accepted.
  destruct typ; cbn [lit_of] in accepted.
  - eapply data_of_sound. exact accepted.
  - destruct value; try discriminate. inversion accepted; constructor.
  - destruct value; try discriminate. inversion accepted; constructor.
  - destruct value; try discriminate.
    destruct (Nat.eqb n (List.length l) && forallb octet_b l) eqn:valid;
        try discriminate.
      inversion accepted; subst out.
      rewrite andb_true_iff in valid.
      destruct valid as [size bytes].
      apply Nat.eqb_eq in size.
      subst n.
      constructor.
      apply octets_forall.
      exact bytes.
  - eapply data_of_sound. exact accepted.
  - eapply data_of_sound. exact accepted.
  - eapply data_of_sound. exact accepted.
  - eapply data_of_sound. exact accepted.
  - eapply data_of_sound. exact accepted.
Qed.

Theorem rep_type : forall typ value out,
  rep typ value out -> typ = lty out.
Proof.
  intros typ value out represented.
  destruct represented; reflexivity.
Qed.

Theorem emit_sound : forall image value,
  emit image = Some value ->
  Comp.iins image = [] /\
  Comp.irow image = [] /\
  exists out,
    run_fuel (rsteps (Comp.icost image)) [] (Comp.iterm image) = Done out [] /\
    rp out = [] /\
    rep (Comp.ityp image) (rv out) value.
Proof.
  intros image value accepted.
  unfold emit in accepted.
  destruct (Comp.iins image) as [|input inputs] eqn:no_inputs;
    try discriminate.
  destruct (Comp.irow image) as [|action row] eqn:no_effects;
    try discriminate.
  destruct (run_fuel (rsteps (Comp.icost image)) [] (Comp.iterm image))
    as [out final | reason | |] eqn:ran; try discriminate.
  destruct final as [|slot final]; try discriminate.
  destruct (rp out) as [|action plan] eqn:no_plan; try discriminate.
  repeat split; try assumption.
  exists out.
  repeat split; try assumption.
  apply lit_of_sound.
  exact accepted.
Qed.

Theorem emit_complete : forall image out value,
  Comp.iins image = [] ->
  Comp.irow image = [] ->
  run_fuel (rsteps (Comp.icost image)) [] (Comp.iterm image) = Done out [] ->
  rp out = [] ->
  lit_of (Comp.ityp image) (rv out) = Some value ->
  emit image = Some value.
Proof.
  intros image out value no_inputs no_effects ran no_plan represented.
  unfold emit.
  rewrite no_inputs, no_effects, ran, no_plan.
  exact represented.
Qed.

Theorem emit_unique : forall image left right,
  emit image = Some left -> emit image = Some right -> left = right.
Proof.
  intros image left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Theorem source_emit_checked : forall source image value,
  Src.compile source = Some image ->
  emit image = Some value ->
  Comp.iins image = [] /\
  Comp.irow image = [] /\
  exists out,
    run_fuel (rsteps (Comp.icost image)) [] (Comp.iterm image) = Done out [] /\
    rp out = [] /\
    rep (Comp.ityp image) (rv out) value.
Proof.
  intros source image value compiled emitted.
  apply emit_sound.
  exact emitted.
Qed.

Definition source_emit (source : string) : option lit :=
  match Src.compile source with
  | Some image => emit image
  | None => None
  end.

Theorem source_emit_sound : forall source value,
  source_emit source = Some value ->
  exists image,
    Src.compile source = Some image /\
    emit image = Some value.
Proof.
  intros source value accepted.
  unfold source_emit in accepted.
  destruct (Src.compile source) as [image |] eqn:compiled; try discriminate.
  exists image.
  split.
  - reflexivity.
  - exact accepted.
Qed.

Theorem source_emit_unique : forall source left right,
  source_emit source = Some left -> source_emit source = Some right ->
  left = right.
Proof.
  intros source left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.