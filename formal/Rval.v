(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Uni.
Require Import Dec.
Require Import Lim.
Require Import Rule.
Require Import Bin.
Require Import Ser.
Require Import Host.
Require Import Feed.
Require Import Sess.

Import ListNotations.

Record rval : Type := RVal {
  rtyp : ty;
  rvalue : value
}.

Definition rval_dec (left right : rval) : {left = right} + {left <> right}.
Proof.
  decide equality.
  - apply value_eq_dec.
  - apply ty_dec.
Defined.

Definition rval_eqb (left right : rval) : bool :=
  if rval_dec left right then true else false.

Lemma rval_eqb_refl : forall item, rval_eqb item item = true.
Proof.
  intros item.
  unfold rval_eqb.
  destruct (rval_dec item item); try contradiction.
  reflexivity.
Qed.

Lemma rval_eqb_eq : forall left right,
  rval_eqb left right = true -> left = right.
Proof.
  intros left right same.
  unfold rval_eqb in same.
  destruct (rval_dec left right); try discriminate.
  exact e.
Qed.

Fixpoint plain_b (typ : ty) : bool :=
  match typ with
  | TUnit | TBool | TInt | TBytes _ => true
  | TVec _ elem => plain_b elem
  | TPair lhs rhs | TSum lhs rhs => plain_b lhs && plain_b rhs
  | TCap _ | TEnc _ _ => false
  end.

Definition root_b (typ : ty) : bool :=
  match typ with
  | TUnit | TVec _ _ | TPair _ _ | TSum _ _ => true
  | TBool | TInt | TBytes _ | TCap _ | TEnc _ _ => false
  end.

Definition rval_b (item : rval) : bool :=
  root_b (rtyp item) && plain_b (rtyp item) && ty_b (rtyp item) &&
  value_b (rvalue item) && Host.typed (rtyp item) (rvalue item) &&
  Host.shape (rvalue item).

Definition rval_code (item : rval) : code :=
  CTag 0 (CCons (ty_code (rtyp item))
    (CCons (value_code (rvalue item)) CNil)).

Definition rval_get (input : code) : option rval :=
  match input with
  | CTag 0 (CCons typ (CCons value CNil)) =>
      match ty_get typ, value_get value with
      | Some out_ty, Some out_value =>
          let item := RVal out_ty out_value in
          if rval_b item then Some item else None
      | _, _ => None
      end
  | _ => None
  end.

Lemma rval_get_code : forall item,
  rval_b item = true -> rval_get (rval_code item) = Some item.
Proof.
  intros [typ value] valid.
  unfold rval_get, rval_code.
  simpl.
  rewrite ty_get_code, value_get_code.
  rewrite valid.
  reflexivity.
Qed.

Definition rval_bits (item : rval) : bits :=
  Ser.enc rval_code item.

Definition rval_file (item : rval) : list nat :=
  [65; 82; 49; 10] ++ map Feed.bit_octet (rval_bits item).

Definition file_bits (input : list nat) : option bits :=
  match input with
  | 65 :: 82 :: 49 :: 10 :: rest => Feed.octet_bits rest
  | _ => None
  end.

Lemma file_bits_rval : forall item,
  file_bits (rval_file item) = Some (rval_bits item).
Proof.
  intros item.
  change
    (Feed.octet_bits (map Feed.bit_octet (rval_bits item)) =
      Some (rval_bits item)).
  apply Feed.octet_bits_map.
Qed.

Definition rval_fit (item : rval) : bool :=
  rval_b item && Nat.leb (length (rval_file item)) (rstr local).

Definition enc_rval (item : rval) : option (list nat) :=
  if rval_fit item then Some (rval_file item) else None.

Definition dec_rval (input : list nat) : option rval :=
  if Nat.leb (length input) (rstr local) then
    match file_bits input with
    | Some body =>
        match Ser.dec rval_code rval_get body with
        | Some item =>
            if rval_b item && Sess.bytes_eqb (rval_file item) input
            then Some item else None
        | None => None
        end
    | None => None
    end
  else None.

Theorem rval_decode_encode : forall item,
  rval_fit item = true -> dec_rval (rval_file item) = Some item.
Proof.
  intros item valid.
  unfold rval_fit in valid.
  apply andb_true_iff in valid.
  destruct valid as [shape size].
  unfold dec_rval.
  rewrite size, file_bits_rval.
  unfold rval_bits.
  rewrite Ser.dec_enc.
  - rewrite shape, Sess.bytes_eqb_refl.
    reflexivity.
  - apply rval_get_code.
    exact shape.
Qed.

Theorem rval_encode_decode : forall input item,
  dec_rval input = Some item -> enc_rval item = Some input.
Proof.
  intros input item accepted.
  unfold dec_rval in accepted.
  destruct (Nat.leb (length input) (rstr local)) eqn:size; try discriminate.
  destruct (file_bits input) as [body |] eqn:framed; try discriminate.
  destruct (Ser.dec rval_code rval_get body) as [found |] eqn:decoded;
    try discriminate.
  destruct (rval_b found && Sess.bytes_eqb (rval_file found) input)
    eqn:valid; try discriminate.
  inversion accepted; subst found.
  apply andb_true_iff in valid.
  destruct valid as [shape exact].
  apply Sess.bytes_eqb_eq in exact.
  unfold enc_rval, rval_fit.
  rewrite shape, exact, size.
  reflexivity.
Qed.

Theorem rval_decode_valid : forall input item,
  dec_rval input = Some item -> rval_b item = true.
Proof.
  intros input item accepted.
  unfold dec_rval in accepted.
  destruct (Nat.leb (length input) (rstr local)); try discriminate.
  destruct (file_bits input); try discriminate.
  destruct (Ser.dec rval_code rval_get b); try discriminate.
  destruct (rval_b r && Sess.bytes_eqb (rval_file r) input)
    eqn:valid; try discriminate.
  inversion accepted; subst r.
  apply andb_true_iff in valid.
  exact (proj1 valid).
Qed.