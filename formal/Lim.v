(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Uni.
Require Import Dec.
Require Import DecComp.
Require Import DecSound.

Import ListNotations.

Definition lim : nat := 1000 * 1000.
Definition fit (value : nat) : bool := Nat.leb value lim.

Fixpoint ty_b (typ : ty) : bool :=
  match typ with
  | TUnit | TBool | TInt => true
  | TBytes len | TCap len => fit len
  | TEnc key rem => fit key && fit rem
  | TVec len elem => fit len && ty_b elem
  | TPair first second | TSum first second => ty_b first && ty_b second
  end.

Fixpoint value_b (value : value) : bool :=
  match value with
  | VUnit | VBool _ | VInt _ => true
  | VBytes bytes => fit (length bytes)
  | VVec values => fit (length values) && forallb value_b values
  | VCap kind id => fit kind && fit id
  | VEnc key rem _ => fit key && fit rem
  | VPair first second => value_b first && value_b second
  | VInl item | VInr item => value_b item
  end.

Definition atom_b (action : atom) : bool :=
  match action with
  | ARead kind | AWrite kind | AEmit kind | AFail kind | AClose kind => fit kind
  end.

Definition bind_b (binder : bind) : bool :=
  fit (bid binder) && ty_b (bty binder).

Fixpoint tm_b (term : tm) : bool :=
  match term with
  | K value typ => value_b value && ty_b typ
  | Bytes bytes => fit (length bytes)
  | Vnil elem => ty_b elem
  | Var id => fit id
  | Let binder value body => bind_b binder && tm_b value && tm_b body
  | If guard yes no => tm_b guard && tm_b yes && tm_b no
  | Pair first second | Add first second | Sub first second
  | Mul first second | Div first second | Mod first second | Cat first second
  | Vcons first second | Vcat first second | Step first second =>
      tm_b first && tm_b second
  | Unpair product first second body =>
      tm_b product && bind_b first && bind_b second && tm_b body
  | Fst value | Snd value | Neg value | Abs value
  | Uncons value | Close value => tm_b value
  | Inl value other => tm_b value && ty_b other
  | Inr other value => ty_b other && tm_b value
  | Case value first yes second no =>
      tm_b value && bind_b first && tm_b yes && bind_b second && tm_b no
  | Act action body => atom_b action && tm_b body
  | Eq typ first second => ty_b typ && tm_b first && tm_b second
  | Cmp _ first second => tm_b first && tm_b second
  | Take len value | Drop len value | At len value => fit len && tm_b value
  | Fold len vector seed item state body =>
      fit len && tm_b vector && tm_b seed && bind_b item && bind_b state
        && tm_b body
  end.

Definition cell_b (cell : cell) : bool :=
  fit (cid cell) && ty_b (cty cell).

Definition ctx_b (gamma : ctx) : bool := forallb cell_b gamma.

Definition slot_b (slot : slot) : bool :=
  fit (sid slot) && ty_b (sty slot) && value_b (sval slot).

Definition env_b (sigma : env) : bool := forallb slot_b sigma.

Definition acceptb (gamma : ctx) (term : tm) : option chk :=
  if ctx_b gamma && tm_b term then checkb gamma term else None.

Definition runb (fuel : nat) (sigma : env) (term : tm) : ans :=
  if env_b sigma && tm_b term then run_fuel fuel sigma term else Stuck.

Theorem acceptb_sound : forall gamma term typ row cost next,
  acceptb gamma term = Some (typ, row, cost, next) ->
  check gamma term typ row cost next.
Proof.
  intros gamma term typ row cost next accepted.
  unfold acceptb in accepted.
  destruct (ctx_b gamma && tm_b term); try discriminate.
  apply checkb_sound.
  exact accepted.
Qed.

Theorem acceptb_complete : forall gamma term typ row cost next,
  ctx_b gamma = true ->
  tm_b term = true ->
  check gamma term typ row cost next ->
  acceptb gamma term = Some (typ, row, cost, next).
Proof.
  intros gamma term typ row cost next gamma_ok term_ok accepted.
  unfold acceptb.
  rewrite gamma_ok, term_ok.
  simpl.
  apply checkb_complete.
  exact accepted.
Qed.

Theorem runb_valid : forall fuel sigma term,
  env_b sigma = true ->
  tm_b term = true ->
  runb fuel sigma term = run_fuel fuel sigma term.
Proof.
  intros fuel sigma term env_ok term_ok.
  unfold runb.
  rewrite env_ok, term_ok.
  reflexivity.
Qed.