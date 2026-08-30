(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List Arith.

Require Import Uni.
Require Import Low.
Require Import Fun.
Require Import Perm.
Require Import Read.

Import ListNotations.

Fixpoint vpeak (items : list vdecl) : nat :=
  match items with
  | [] => 0
  | item :: rest => Nat.max (Fhe.fpeak (vdinfo item)) (vpeak rest)
  end.

Definition total (value : front) (core : res) : res :=
  rmax core (rlevel (vpeak (frveils value))).

Record image : Type := Image {
  isrc : front;
  iins : list bind;
  iterm : tm;
  ityp : ty;
  irow : list atom;
  icost : res;
  ires : res
}.

Definition run (value : front) : option image :=
  match frrest value with
  | [] =>
      if pset_b (frperms value) then
        match Fun.fprog (frbinds value) (frready value) (frbody value) with
        | Some (binds, core) =>
            match Fun.fpcheck (frbinds value) (frready value) (frbody value) with
            | Some (typ, row, cost, _) =>
                if prow (frperms value) row
                then Some (Image value binds core typ row cost
                  (total value cost))
                else None
            | None => None
            end
        | None => None
        end
      else None
  | _ => None
  end.

Definition load (words : vocab) (fuel : nat) (input : list lex)
    : option image :=
  match Read.read words fuel input with
  | Some value => run value
  | None => None
  end.

Theorem run_sound : forall value out,
  run value = Some out ->
  isrc out = value /\
  frrest value = [] /\
  pset_b (frperms value) = true /\
  Fun.fprog (frbinds value) (frready value) (frbody value) =
    Some (iins out, iterm out) /\
  prow (frperms value) (irow out) = true /\
  ires out = total value (icost out) /\
  exists gamma next,
    opens [] (iins out) = Some gamma /\
    check gamma (iterm out) (ityp out) (irow out) (icost out) next /\
    doneb next = true.
Proof.
  intros value out accepted.
  unfold run in accepted.
  destruct (frrest value) as [| first rest] eqn:empty; try discriminate.
  destruct (pset_b (frperms value)) eqn:rights; try discriminate.
  destruct (Fun.fprog (frbinds value) (frready value) (frbody value))
    as [[binds core] |] eqn:lowered; try discriminate.
  destruct (Fun.fpcheck (frbinds value) (frready value) (frbody value))
    as [[[[typ row] cost] next] |] eqn:checked; try discriminate.
  destruct (prow (frperms value) row) eqn:allowed; try discriminate.
  inversion accepted; subst out.
  apply Fun.fpcheck_sound in checked.
  destruct checked as [found_binds [found_core [gamma
    [found [opened [typed done]]]]]].
  rewrite lowered in found.
  inversion found; subst found_binds found_core.
  repeat split; try assumption; try reflexivity.
  exists gamma, next.
  repeat split; assumption.
Qed.

Theorem run_complete : forall value binds core typ row cost next,
  frrest value = [] ->
  pset_b (frperms value) = true ->
  Fun.fprog (frbinds value) (frready value) (frbody value) = Some (binds, core) ->
  Fun.fpcheck (frbinds value) (frready value) (frbody value) =
    Some (typ, row, cost, next) ->
  prow (frperms value) row = true ->
  run value = Some (Image value binds core typ row cost (total value cost)).
Proof.
  intros value binds core typ row cost next empty rights lowered checked allowed.
  unfold run.
  rewrite empty, rights, lowered, checked, allowed.
  reflexivity.
Qed.

Theorem run_depth : forall value out,
  run value = Some out ->
  rdepth (ires out) = Nat.max (rdepth (icost out)) (vpeak (frveils value)).
Proof.
  intros value out accepted.
  destruct (run_sound value out accepted)
    as [_ [_ [_ [_ [_ [same _]]]]]].
  rewrite same.
  unfold total, rmax, rlevel.
  reflexivity.
Qed.

Theorem run_peak : forall value out,
  run value = Some out ->
  vpeak (frveils value) <= rdepth (ires out).
Proof.
  intros value out accepted.
  rewrite (run_depth value out accepted).
  apply Nat.le_max_r.
Qed.

Theorem run_unique : forall value left right,
  run value = Some left ->
  run value = Some right ->
  left = right.
Proof.
  intros value left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Theorem load_sound : forall words fuel input out,
  load words fuel input = Some out ->
  exists value,
    Read.read words fuel input = Some value /\
    run value = Some out.
Proof.
  intros words fuel input out accepted.
  unfold load in accepted.
  destruct (Read.read words fuel input) as [value |] eqn:read; try discriminate.
  exists value.
  split.
  - reflexivity.
  - exact accepted.
Qed.

Theorem load_complete : forall words fuel input value out,
  Read.read words fuel input = Some value ->
  run value = Some out ->
  load words fuel input = Some out.
Proof.
  intros words fuel input value out read accepted.
  unfold load.
  rewrite read.
  exact accepted.
Qed.

Theorem load_unique : forall words fuel input left right,
  load words fuel input = Some left ->
  load words fuel input = Some right ->
  left = right.
Proof.
  intros words fuel input left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.