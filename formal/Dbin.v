(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import ZArith.ZArith.

Require Import Lim.
Require Import Rule.
Require Import Bin.
Require Import Ser.
Require Import Sess.
Require Import Emit.
Require Import Rval.
Require Import Dbg.

Import ListNotations.

Definition hex_b (value : nat) : bool :=
  (Nat.leb 48 value && Nat.leb value 57)
    || (Nat.leb 97 value && Nat.leb value 102).

Definition digest_b (value : list nat) : bool :=
  Nat.eqb (length value) 64 && forallb hex_b value.

Definition stop_b (value : point) : bool :=
  match value with
  | BPc spot | BLine spot => fit spot
  end.

Definition stop_lt (left right : point) : bool :=
  match left, right with
  | BPc lhs, BPc rhs | BLine lhs, BLine rhs => Nat.ltb lhs rhs
  | BPc _, BLine _ => true
  | BLine _, BPc _ => false
  end.

Fixpoint stops_lt (values : list point) : bool :=
  match values with
  | [] | [_] => true
  | first :: (second :: _ as rest) =>
      stop_lt first second && stops_lt rest
  end.

Definition stops_b (values : list point) : bool :=
  fit (length values) && forallb stop_b values && stops_lt values.

Definition dlit_b (value : lit) : bool :=
  match value with
  | LBool _ | LInt _ => true
  | LBytes raw => Sess.raw_b raw
  | LData item => Rval.rval_fit item
  end.

Definition expect_b (value : option lit) : bool :=
  match value with
  | None => true
  | Some item => dlit_b item
  end.

Definition cfg_b (value : cfg) : bool :=
  negb (Nat.eqb (dcap value) 0) && fit (dcap value)
    && stops_b (dstops value) && expect_b (dexpect value).

Record dstate : Type := DState {
  dsource : list nat;
  dcode : list nat;
  dcfg : cfg;
  dseen : nat;
  dtrace : list nat
}.

Definition dstate_b (value : dstate) : bool :=
  digest_b (dsource value) && digest_b (dcode value)
    && cfg_b (dcfg value) && Nat.ltb (dseen value) (dcap (dcfg value))
    && digest_b (dtrace value).

Definition raw_code (value : list nat) : code := list_code CNum value.
Definition raw_get (input : code) : option (list nat) := list_get num_get input.

Lemma raw_get_code : forall value, raw_get (raw_code value) = Some value.
Proof.
  intros value.
  apply list_get_code.
  intros item _.
  apply num_get_code.
Qed.

Definition stop_code (value : point) : code :=
  match value with
  | BPc spot => CTag 0 (CNum spot)
  | BLine spot => CTag 1 (CNum spot)
  end.

Definition stop_get (input : code) : option point :=
  match input with
  | CTag 0 (CNum spot) => Some (BPc spot)
  | CTag 1 (CNum spot) => Some (BLine spot)
  | _ => None
  end.

Lemma stop_get_code : forall value,
  stop_get (stop_code value) = Some value.
Proof.
  intros value.
  destruct value; reflexivity.
Qed.

Definition dlit_code (value : lit) : code :=
  match value with
  | LBool false => CTag 0 (CNum 0)
  | LBool true => CTag 0 (CNum 1)
  | LInt number => CTag 1 (CInt number)
  | LBytes raw => CTag 2 (raw_code raw)
  | LData item => CTag 3 (raw_code (Rval.rval_file item))
  end.

Definition dlit_get (input : code) : option lit :=
  match input with
  | CTag 0 (CNum 0) => Some (LBool false)
  | CTag 0 (CNum 1) => Some (LBool true)
  | CTag 1 (CInt number) => Some (LInt number)
  | CTag 2 body =>
      match raw_get body with
      | Some raw => Some (LBytes raw)
      | None => None
      end
  | CTag 3 body =>
      match raw_get body with
      | Some raw =>
          match Rval.dec_rval raw with
          | Some item => Some (LData item)
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Lemma dlit_get_code : forall value,
  dlit_b value = true -> dlit_get (dlit_code value) = Some value.
Proof.
  intros value valid.
  destruct value; simpl.
  - destruct b; reflexivity.
  - reflexivity.
  - rewrite raw_get_code.
    reflexivity.
  - rewrite raw_get_code.
    rewrite Rval.rval_decode_encode by exact valid.
    reflexivity.
Qed.

Definition expect_code (value : option lit) : code :=
  match value with
  | None => CTag 0 CNil
  | Some item => CTag 1 (dlit_code item)
  end.

Definition expect_get (input : code) : option (option lit) :=
  match input with
  | CTag 0 CNil => Some None
  | CTag 1 body =>
      match dlit_get body with
      | Some item => Some (Some item)
      | None => None
      end
  | _ => None
  end.

Lemma expect_get_code : forall value,
  expect_b value = true -> expect_get (expect_code value) = Some value.
Proof.
  intros value valid.
  destruct value as [item |]; simpl.
  - rewrite dlit_get_code by exact valid.
    reflexivity.
  - reflexivity.
Qed.

Definition cfg_code (value : cfg) : code :=
  CTag 3 (CCons (CNum (dcap value))
    (CCons (list_code stop_code (dstops value))
      (CCons (expect_code (dexpect value)) CNil))).

Definition cfg_get (input : code) : option cfg :=
  match input with
  | CTag 3 (CCons (CNum cap) (CCons stops (CCons expected CNil))) =>
      match list_get stop_get stops, expect_get expected with
      | Some points, Some result =>
          let value := Config cap points result in
          if cfg_b value then Some value else None
      | _, _ => None
      end
  | _ => None
  end.

Lemma cfg_get_code : forall value,
  cfg_b value = true -> cfg_get (cfg_code value) = Some value.
Proof.
  intros [cap stops expected] valid.
  unfold cfg_get, cfg_code.
  cbn [dcap dstops dexpect].
  rewrite list_get_code.
  - assert (expect_ok : expect_b expected = true).
    {
      unfold cfg_b in valid.
      cbn [dcap dstops dexpect] in valid.
      apply andb_true_iff in valid as [_ expect_ok].
      exact expect_ok.
    }
    rewrite expect_get_code by exact expect_ok.
    change
      ((if cfg_b (Config cap stops expected)
        then Some (Config cap stops expected) else None) =
       Some (Config cap stops expected)).
    rewrite valid.
    reflexivity.
  - intros value _.
    apply stop_get_code.
Qed.

Definition dstate_code (value : dstate) : code :=
  CTag 4 (CCons (raw_code (dsource value))
    (CCons (raw_code (dcode value))
      (CCons (cfg_code (dcfg value))
        (CCons (CNum (dseen value))
          (CCons (raw_code (dtrace value)) CNil))))).

Definition dstate_get (input : code) : option dstate :=
  match input with
  | CTag 4 (CCons source (CCons program (CCons config
      (CCons (CNum seen) (CCons trace CNil))))) =>
      match raw_get source, raw_get program, cfg_get config, raw_get trace with
      | Some source', Some program', Some config', Some trace' =>
          let value := DState source' program' config' seen trace' in
          if dstate_b value then Some value else None
      | _, _, _, _ => None
      end
  | _ => None
  end.

Lemma dstate_get_code : forall value,
  dstate_b value = true -> dstate_get (dstate_code value) = Some value.
Proof.
  intros [source program config seen trace] valid.
  unfold dstate_get, dstate_code.
  cbn [dsource dcode dcfg dseen dtrace] in *.
  rewrite !raw_get_code.
  assert (config_ok : cfg_b config = true).
  {
    unfold dstate_b in valid.
    cbn [dsource dcode dcfg dseen dtrace] in valid.
    apply andb_true_iff in valid as [valid _].
    apply andb_true_iff in valid as [valid _].
    apply andb_true_iff in valid as [_ config_ok].
    exact config_ok.
  }
  rewrite cfg_get_code by exact config_ok.
  change
    ((if dstate_b (DState source program config seen trace)
      then Some (DState source program config seen trace) else None) =
     Some (DState source program config seen trace)).
  rewrite valid.
  reflexivity.
Qed.

Definition dstate_bits (value : dstate) : bits := Ser.enc dstate_code value.

Definition bit_octet (value : bool) : nat := if value then 49 else 48.

Fixpoint octet_bits (input : list nat) : option bits :=
  match input with
  | [] => Some []
  | 48 :: rest =>
      match octet_bits rest with
      | Some bits => Some (false :: bits)
      | None => None
      end
  | 49 :: rest =>
      match octet_bits rest with
      | Some bits => Some (true :: bits)
      | None => None
      end
  | _ => None
  end.

Lemma octet_bits_map : forall input,
  octet_bits (map bit_octet input) = Some input.
Proof.
  induction input as [|value rest IH]; simpl.
  - reflexivity.
  - destruct value; simpl; rewrite IH; reflexivity.
Qed.

Definition dstate_file (value : dstate) : list nat :=
  [67; 68; 49; 10] ++ map bit_octet (dstate_bits value).

Definition file_bits (input : list nat) : option bits :=
  match input with
  | 67 :: 68 :: 49 :: 10 :: rest => octet_bits rest
  | _ => None
  end.

Lemma file_bits_state : forall value,
  file_bits (dstate_file value) = Some (dstate_bits value).
Proof.
  intros value.
  change
    (octet_bits (map bit_octet (dstate_bits value)) =
     Some (dstate_bits value)).
  apply octet_bits_map.
Qed.

Definition dstate_fit (value : dstate) : bool :=
  dstate_b value && Nat.leb (length (dstate_file value)) (rstr local).

Definition enc_dstate (value : dstate) : option (list nat) :=
  if dstate_fit value then Some (dstate_file value) else None.

Definition dec_dstate (input : list nat) : option dstate :=
  if Nat.leb (length input) (rstr local) then
    match file_bits input with
    | Some body =>
        match Ser.dec dstate_code dstate_get body with
        | Some value =>
            if dstate_b value && Sess.bytes_eqb (dstate_file value) input
            then Some value else None
        | None => None
        end
    | None => None
    end
  else None.

Theorem dstate_decode_encode : forall value,
  dstate_fit value = true ->
  dec_dstate (dstate_file value) = Some value.
Proof.
  intros value valid.
  unfold dstate_fit in valid.
  apply andb_true_iff in valid.
  destruct valid as [shape size].
  unfold dec_dstate.
  rewrite size, file_bits_state.
  unfold dstate_bits.
  rewrite Ser.dec_enc.
  - rewrite shape, Sess.bytes_eqb_refl.
    reflexivity.
  - apply dstate_get_code.
    exact shape.
Qed.

Theorem dstate_encode_decode : forall input value,
  dec_dstate input = Some value -> enc_dstate value = Some input.
Proof.
  intros input value accepted.
  unfold dec_dstate in accepted.
  destruct (Nat.leb (length input) (rstr local)) eqn:size; try discriminate.
  destruct (file_bits input) as [body |] eqn:framed; try discriminate.
  destruct (Ser.dec dstate_code dstate_get body) as [found |] eqn:decoded;
    try discriminate.
  destruct (dstate_b found && Sess.bytes_eqb (dstate_file found) input)
    eqn:valid; try discriminate.
  inversion accepted; subst found.
  apply andb_true_iff in valid.
  destruct valid as [shape exact].
  apply Sess.bytes_eqb_eq in exact.
  unfold enc_dstate, dstate_fit.
  rewrite shape, exact, size.
  reflexivity.
Qed.