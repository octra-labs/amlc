(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import BinNums.
From Stdlib Require Import BinPos.
From Stdlib Require Import BinNat.
From Stdlib Require Import NArith.Nnat.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.

Import ListNotations.

Definition bits := list bool.

Fixpoint put_pos (value : positive) : bits :=
  match value with
  | xH => [false; false]
  | xO rest => false :: true :: put_pos rest
  | xI rest => true :: false :: put_pos rest
  end.

Fixpoint get_pos (input : bits) : option (positive * bits) :=
  match input with
  | false :: false :: rest => Some (xH, rest)
  | false :: true :: rest =>
      match get_pos rest with
      | Some (value, tail) => Some (xO value, tail)
      | None => None
      end
  | true :: false :: rest =>
      match get_pos rest with
      | Some (value, tail) => Some (xI value, tail)
      | None => None
      end
  | _ => None
  end.

Lemma get_pos_put : forall value rest,
  get_pos (put_pos value ++ rest) = Some (value, rest).
Proof.
  induction value; intros rest; simpl; rewrite ?IHvalue; reflexivity.
Qed.

Definition put_n (value : N) : bits :=
  match value with
  | N0 => [false; false]
  | Npos rest => false :: true :: put_pos rest
  end.

Definition get_n (input : bits) : option (N * bits) :=
  match input with
  | false :: false :: rest => Some (N0, rest)
  | false :: true :: rest =>
      match get_pos rest with
      | Some (value, tail) => Some (Npos value, tail)
      | None => None
      end
  | _ => None
  end.

Lemma get_n_put : forall value rest,
  get_n (put_n value ++ rest) = Some (value, rest).
Proof.
  intros value rest.
  destruct value; simpl; [reflexivity | rewrite get_pos_put; reflexivity].
Qed.

Definition put_nat (value : nat) : bits := put_n (N.of_nat value).

Definition get_nat (input : bits) : option (nat * bits) :=
  match get_n input with
  | Some (value, rest) => Some (N.to_nat value, rest)
  | None => None
  end.

Lemma get_nat_put : forall value rest,
  get_nat (put_nat value ++ rest) = Some (value, rest).
Proof.
  intros value rest.
  unfold get_nat, put_nat.
  rewrite get_n_put, Nat2N.id.
  reflexivity.
Qed.

Definition put_z (value : Z) : bits :=
  match value with
  | Z0 => [false; false]
  | Zpos rest => false :: true :: put_pos rest
  | Zneg rest => true :: false :: put_pos rest
  end.

Definition get_z (input : bits) : option (Z * bits) :=
  match input with
  | false :: false :: rest => Some (Z0, rest)
  | false :: true :: rest =>
      match get_pos rest with
      | Some (value, tail) => Some (Zpos value, tail)
      | None => None
      end
  | true :: false :: rest =>
      match get_pos rest with
      | Some (value, tail) => Some (Zneg value, tail)
      | None => None
      end
  | _ => None
  end.

Lemma get_z_put : forall value rest,
  get_z (put_z value ++ rest) = Some (value, rest).
Proof.
  intros value rest.
  destruct value; simpl; rewrite ?get_pos_put; reflexivity.
Qed.

Inductive code : Type :=
| CNum : nat -> code
| CInt : Z -> code
| CNil : code
| CCons : code -> code -> code
| CTag : nat -> code -> code.

Fixpoint code_eq_dec (left right : code) : {left = right} + {left <> right}.
Proof.
  decide equality.
  - apply Nat.eq_dec.
  - apply Z.eq_dec.
  - apply Nat.eq_dec.
Defined.

Definition code_eqb (left right : code) : bool :=
  if code_eq_dec left right then true else false.

Lemma code_eqb_eq : forall left right,
  code_eqb left right = true <-> left = right.
Proof.
  intros left right.
  unfold code_eqb.
  destruct (code_eq_dec left right) as [same | diff].
  - split; intros; [exact same | reflexivity].
  - split; intros false.
    + discriminate.
    + contradiction.
Qed.

Fixpoint put_code (value : code) : bits :=
  match value with
  | CNum number => false :: false :: put_nat number
  | CInt number => false :: true :: put_z number
  | CNil => [true; false]
  | CCons first rest => true :: true :: false :: put_code first ++ put_code rest
  | CTag tag body => true :: true :: true :: put_nat tag ++ put_code body
  end.

Fixpoint cdepth (value : code) : nat :=
  match value with
  | CNum _ | CInt _ | CNil => 1
  | CCons first rest => S (Nat.max (cdepth first) (cdepth rest))
  | CTag _ body => S (cdepth body)
  end.

Fixpoint get_code_f (fuel : nat) (input : bits) : option (code * bits) :=
  match fuel with
  | 0 => None
  | S fuel' =>
      match input with
      | false :: false :: rest =>
          match get_nat rest with
          | Some (number, tail) => Some (CNum number, tail)
          | None => None
          end
      | false :: true :: rest =>
          match get_z rest with
          | Some (number, tail) => Some (CInt number, tail)
          | None => None
          end
      | true :: false :: rest => Some (CNil, rest)
      | true :: true :: false :: rest =>
          match get_code_f fuel' rest with
          | Some (first, tail) =>
              match get_code_f fuel' tail with
              | Some (last, final) => Some (CCons first last, final)
              | None => None
              end
          | None => None
          end
      | true :: true :: true :: rest =>
          match get_nat rest with
          | Some (tag, tail) =>
              match get_code_f fuel' tail with
              | Some (body, final) => Some (CTag tag body, final)
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  end.

Lemma get_code_f_put : forall value fuel rest,
  cdepth value <= fuel ->
  get_code_f fuel (put_code value ++ rest) = Some (value, rest).
Proof.
  induction value; intros fuel rest enough; destruct fuel;
    cbn [cdepth] in enough; try lia; cbn [put_code get_code_f app].
  -
    rewrite get_nat_put.
    reflexivity.
  - rewrite get_z_put.
    reflexivity.
  - reflexivity.
  - rewrite <- app_assoc.
    rewrite IHvalue1, IHvalue2; try lia.
    reflexivity.
  - rewrite <- app_assoc, get_nat_put, IHvalue; try lia.
    reflexivity.
Qed.

Lemma cdepth_size : forall value, cdepth value <= length (put_code value).
Proof.
  induction value; simpl; rewrite ?length_app; simpl; lia.
Qed.

Fixpoint bits_eq_dec (left right : bits) : {left = right} + {left <> right}.
Proof.
  decide equality.
  apply Bool.bool_dec.
Defined.

Definition bits_eqb (left right : bits) : bool :=
  if bits_eq_dec left right then true else false.

Lemma bits_eqb_eq : forall left right,
  bits_eqb left right = true <-> left = right.
Proof.
  intros left right.
  unfold bits_eqb.
  destruct (bits_eq_dec left right) as [same | diff].
  - split; intros; [exact same | reflexivity].
  - split; intros false.
    + discriminate.
    + contradiction.
Qed.

Definition get_code (input : bits) : option code :=
  match get_code_f (S (length input)) input with
  | Some (value, []) =>
      if bits_eqb (put_code value) input then Some value else None
  | _ => None
  end.

Theorem get_code_put : forall value,
  get_code (put_code value) = Some value.
Proof.
  intros value.
  unfold get_code.
  assert (enough : cdepth value <= S (length (put_code value))).
  { pose proof (cdepth_size value). lia. }
  pose proof (get_code_f_put value (S (length (put_code value))) [] enough)
    as parsed.
  rewrite app_nil_r in parsed.
  rewrite parsed.
  rewrite (proj2 (bits_eqb_eq (put_code value) (put_code value)) eq_refl).
  reflexivity.
Qed.

Theorem put_code_get : forall input value,
  get_code input = Some value -> put_code value = input.
Proof.
  intros input value accepted.
  unfold get_code in accepted.
  destruct (get_code_f (S (length input)) input) as [[found rest] |];
    try discriminate.
  destruct rest; try discriminate.
  destruct (bits_eqb (put_code found) input) eqn:same; try discriminate.
  inversion accepted; subst.
  apply bits_eqb_eq.
  exact same.
Qed.