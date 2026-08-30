(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import ZArith.

Require Import Uni.
Require Import Dec.
Require Import DecComp.
Require Import DecSound.
Require Import Surf.
Require Import Low.

Import ListNotations.

Inductive qmode : Type := QEvery | QSome | QCount | QSum.

Definition clear (name : nat) (source : stm) (item : sbind) (body : stm)
    : bool :=
  negb (Nat.eqb name (sname item) || has name source || has name body).

Definition qtype (mode : qmode) : ty :=
  match mode with
  | QEvery | QSome => TBool
  | QCount | QSum => TInt
  end.

Definition qmark (mode : qmode) : ty :=
  match mode with
  | QEvery | QSome | QCount => TBool
  | QSum => TInt
  end.

Definition qseed (mode : qmode) : stm :=
  match mode with
  | QEvery => SK (VBool true) TBool
  | QSome => SK (VBool false) TBool
  | QCount | QSum => SK (VInt 0%Z) TInt
  end.

Definition qbody (mode : qmode) (state mark : nat) (body : stm) : stm :=
  let marked := SLet (SBind mark MM (qmark mode)) body in
  match mode with
  | QEvery => marked (SIf (SVar state) (SVar mark) (SK (VBool false) TBool))
  | QSome => marked (SIf (SVar state) (SK (VBool true) TBool) (SVar mark))
  | QCount => marked (SIf (SVar mark)
      (SAdd (SVar state) (SK (VInt 1%Z) TInt)) (SVar state))
  | QSum => marked (SAdd (SVar state) (SVar mark))
  end.

Definition qterm (state mark : nat) (mode : qmode) (count : nat) (source : stm)
    (item : sbind) (body : stm) : option stm :=
  if Nat.eqb state mark || negb (clear state source item body)
    || negb (clear mark source item body) then None
  else
    Some (SFold count source (qseed mode) item (SBind state MM (qtype mode))
      (qbody mode state mark body)).

Definition qcheck (inputs : list sbind) (state mark : nat) (mode : qmode)
    (count : nat)
    (source : stm) (item : sbind) (body : stm) : option chk :=
  match qterm state mark mode count source item body with
  | Some term => pcheck inputs term
  | None => None
  end.

Theorem qterm_exact : forall state mark mode count source item body,
  state <> mark ->
  clear state source item body = true ->
  clear mark source item body = true ->
  qterm state mark mode count source item body =
    Some (SFold count source (qseed mode) item (SBind state MM (qtype mode))
      (qbody mode state mark body)).
Proof.
  intros state mark mode count source item body apart state_ok mark_ok.
  unfold qterm.
  apply Nat.eqb_neq in apart.
  rewrite apart, state_ok, mark_ok.
  reflexivity.
Qed.

Theorem qcheck_sound : forall inputs state mark mode count source item body
    typ row cost next,
  qcheck inputs state mark mode count source item body = Some (typ, row, cost, next) ->
  exists term binds core gamma,
    qterm state mark mode count source item body = Some term /\
    prog inputs term = Some (binds, core) /\
    opens [] binds = Some gamma /\
    check gamma core typ row cost next /\
    doneb next = true.
Proof.
  intros inputs state mark mode count source item body typ row cost next accepted.
  unfold qcheck in accepted.
  destruct (qterm state mark mode count source item body) as [term |] eqn:built;
    try discriminate.
  apply pcheck_sound in accepted.
  destruct accepted as [binds [core [gamma [lowered [opened [checked done]]]]]].
  exists term, binds, core, gamma.
  repeat split; assumption.
Qed.

Theorem qcheck_complete : forall inputs state mark mode count source item body
    term binds core gamma typ row cost next,
  qterm state mark mode count source item body = Some term ->
  prog inputs term = Some (binds, core) ->
  opens [] binds = Some gamma ->
  check gamma core typ row cost next ->
  doneb next = true ->
  qcheck inputs state mark mode count source item body =
    Some (typ, row, cost, next).
Proof.
  intros inputs state mark mode count source item body term binds core gamma
    typ row cost next built lowered opened checked done.
  unfold qcheck.
  rewrite built.
  exact (pcheck_complete inputs term binds core gamma typ row cost next
    lowered opened checked done).
Qed.