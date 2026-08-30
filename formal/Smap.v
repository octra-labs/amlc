(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.

Require Import Bin.
Require Import Ser.
Require Import Rule.
Require Import Lex.

Import ListNotations.

Definition map_max : nat := 4 * rtm_nodes local + 2.

Definition point_b (value : pos) : bool :=
  Nat.leb (p_off value) (rstr local)
    && negb (Nat.eqb (p_line value) 0)
    && Nat.leb (p_line value) (S (rstr local))
    && negb (Nat.eqb (p_col value) 0)
    && Nat.leb (p_col value) (S (rstr local)).

Definition point_le (left right : pos) : bool :=
  Nat.leb (p_off left) (p_off right)
    && (Nat.ltb (p_line left) (p_line right)
      || (Nat.eqb (p_line left) (p_line right)
        && Nat.leb (p_col left) (p_col right))).

Definition span_b (value : span) : bool :=
  point_b (s_first value)
    && point_b (s_last value)
    && point_le (s_first value) (s_last value).

Definition map_b (values : list span) : bool :=
  negb (Nat.eqb (length values) 0)
    && Nat.leb (length values) map_max
    && forallb span_b values.

Definition point_code (value : pos) : Bin.code :=
  CTag 0 (CCons (CNum (p_off value))
    (CCons (CNum (p_line value)) (CCons (CNum (p_col value)) CNil))).

Definition point_get (input : Bin.code) : option pos :=
  match input with
  | CTag 0 (CCons (CNum off)
      (CCons (CNum line) (CCons (CNum col) CNil))) =>
      Some (Pos off line col)
  | _ => None
  end.

Lemma point_get_code : forall value,
  point_get (point_code value) = Some value.
Proof.
  intros [off line col].
  reflexivity.
Qed.

Definition span_code (value : span) : Bin.code :=
  CTag 1 (CCons (point_code (s_first value))
    (CCons (point_code (s_last value)) CNil)).

Definition span_get (input : Bin.code) : option span :=
  match input with
  | CTag 1 (CCons first (CCons last CNil)) =>
      match point_get first, point_get last with
      | Some first_pos, Some last_pos => Some (Span first_pos last_pos)
      | _, _ => None
      end
  | _ => None
  end.

Lemma span_get_code : forall value,
  span_get (span_code value) = Some value.
Proof.
  intros [first last].
  destruct first, last.
  reflexivity.
Qed.

Definition map_code (values : list span) : Bin.code :=
  CTag 2 (list_code span_code values).

Definition map_get (input : Bin.code) : option (list span) :=
  match input with
  | CTag 2 body => list_get span_get body
  | _ => None
  end.

Lemma map_get_code : forall values,
  map_get (map_code values) = Some values.
Proof.
  intros values.
  unfold map_get, map_code.
  apply list_get_code.
  intros value _.
  apply span_get_code.
Qed.

Definition map_bits (values : list span) : bits := Ser.enc map_code values.

Definition map_fit (values : list span) : bool :=
  map_b values && Nat.leb (length (map_bits values)) (rstr local).

Definition enc_map (values : list span) : option bits :=
  if map_fit values then Some (map_bits values) else None.

Definition dec_map (input : bits) : option (list span) :=
  if Nat.leb (length input) (rstr local) then
    match Ser.dec map_code map_get input with
    | Some values => if map_b values then Some values else None
    | None => None
    end
  else None.

Theorem map_decode_encode : forall values,
  map_fit values = true ->
  dec_map (map_bits values) = Some values.
Proof.
  intros values fit.
  unfold map_fit in fit.
  apply andb_true_iff in fit.
  destruct fit as [valid size].
  unfold dec_map.
  rewrite size.
  unfold map_bits.
  rewrite Ser.dec_enc.
  - rewrite valid.
    reflexivity.
  - apply map_get_code.
Qed.

Theorem map_encode_decode : forall input values,
  dec_map input = Some values ->
  enc_map values = Some input.
Proof.
  intros input values accepted.
  unfold dec_map in accepted.
  destruct (Nat.leb (length input) (rstr local)) eqn:size;
    try discriminate.
  destruct (Ser.dec map_code map_get input) as [found |] eqn:decoded;
    try discriminate.
  destruct (map_b found) eqn:valid; try discriminate.
  inversion accepted; subst found.
  pose proof (Ser.enc_dec (list span) map_code map_get input values decoded)
    as exact.
  unfold enc_map, map_fit.
  rewrite valid.
  unfold map_bits.
  rewrite exact, size.
  reflexivity.
Qed.