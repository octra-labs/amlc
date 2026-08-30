(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.

Require Import Text.
Require Import Uni.
Require Import Low.
Require Import Read.
Require Import Comp.
Require Import Perm.
Require Import Lex.

Import ListNotations.
Open Scope string_scope.

Fixpoint text_at (raw : string) (acc : nat) : nat :=
  match raw with
  | EmptyString => acc
  | String value rest => text_at rest (acc * 257 + S (Lex.code value))
  end.

Definition text (raw : string) : nat := text_at raw 0.

Definition name (raw : string) : nat := 2 * text raw.

Fixpoint octets_at (raw : string) (acc : list nat) : list nat :=
  match raw with
  | EmptyString => rev acc
  | String value rest => octets_at rest (Lex.code value :: acc)
  end.

Definition octets (raw : string) : list nat := octets_at raw [].

Definition one (value : Lex.item) : Read.lex :=
  match Lex.i_tok value, Lex.i_pay value with
  | TName, Lex.PName raw => Read.LName (name raw)
  | TNat, Lex.PNat raw => Read.LNat raw
  | THex, Lex.PHex raw => Read.LHex (octets raw)
  | token, _ => Read.LKey token
  end.

Fixpoint lexes_at (raw : list Lex.item) (acc : list Read.lex)
    : list Read.lex :=
  match raw with
  | [] => rev acc
  | value :: rest => lexes_at rest (one value :: acc)
  end.

Definition lexes (raw : list Lex.item) : list Read.lex := lexes_at raw [].

Fixpoint count_at {A : Type} (raw : list A) (acc : nat) : nat :=
  match raw with
  | [] => acc
  | _ :: rest => count_at rest (S acc)
  end.

Definition count {A : Type} (raw : list A) : nat := count_at raw 0.

Definition words : Read.vocab := Read.Vocab
  (name "veil")
  (name "key")
  (name "add")
  (name "mul")
  (name "renew")
  (name "stage")
  (name "prod")
  (name "param")
  (name "room")
  (name "state")
  (name "terms")
  (name "slots")
  (name "query")
  (name "enc")
  (name "trim").

Definition source (src : string) : option Read.front :=
  match Lex.scan src with
  | Lex.Pass raw =>
      let input := lexes raw in
      Read.read words (S (count input)) input
  | Lex.Fail _ _ => None
  end.

Definition compile (src : string) : option Comp.image :=
  match Lex.scan src with
  | Lex.Pass raw =>
      let input := lexes raw in
      Comp.load words (S (count input)) input
  | Lex.Fail _ _ => None
  end.

Theorem source_sound : forall src value,
  source src = Some value ->
  exists raw,
    Lex.scan src = Lex.Pass raw /\
    Read.read words (S (count (lexes raw))) (lexes raw) = Some value.
Proof.
  intros src value accepted.
  destruct (Lex.scan src) as [raw | cause place] eqn:scanned;
    unfold source in accepted; rewrite scanned in accepted;
    cbn -[Read.read] in accepted.
  - exists raw.
    split.
    + reflexivity.
    + exact accepted.
  - discriminate.
Qed.

Theorem source_complete : forall src raw value,
  Lex.scan src = Lex.Pass raw ->
  Read.read words (S (count (lexes raw))) (lexes raw) = Some value ->
  source src = Some value.
Proof.
  intros src raw value scanned accepted.
  unfold source.
  rewrite scanned.
  cbn -[Read.read].
  exact accepted.
Qed.

Theorem source_unique : forall src left right,
  source src = Some left ->
  source src = Some right ->
  left = right.
Proof.
  intros src left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Theorem compile_sound : forall src value,
  compile src = Some value ->
  exists raw,
    Lex.scan src = Lex.Pass raw /\
    Comp.load words (S (count (lexes raw))) (lexes raw) = Some value.
Proof.
  intros src value accepted.
  destruct (Lex.scan src) as [raw | cause place] eqn:scanned;
    unfold compile in accepted; rewrite scanned in accepted;
    cbn -[Comp.load] in accepted.
  - exists raw.
    split.
    + reflexivity.
    + exact accepted.
  - discriminate.
Qed.

Theorem compile_complete : forall src raw value,
  Lex.scan src = Lex.Pass raw ->
  Comp.load words (S (count (lexes raw))) (lexes raw) = Some value ->
  compile src = Some value.
Proof.
  intros src raw value scanned accepted.
  unfold compile.
  rewrite scanned.
  cbn -[Comp.load].
  exact accepted.
Qed.

Theorem compile_unique : forall src left right,
  compile src = Some left ->
  compile src = Some right ->
  left = right.
Proof.
  intros src left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Theorem compile_checked : forall src out,
  compile src = Some out ->
  frrest (Comp.isrc out) = [] /\
  pset_b (frperms (Comp.isrc out)) = true /\
  Fun.fprog (frbinds (Comp.isrc out)) (frready (Comp.isrc out))
    (frbody (Comp.isrc out)) = Some (Comp.iins out, Comp.iterm out) /\
  prow (frperms (Comp.isrc out)) (Comp.irow out) = true /\
  exists gamma next,
    opens [] (Comp.iins out) = Some gamma /\
    check gamma (Comp.iterm out) (Comp.ityp out) (Comp.irow out)
      (Comp.icost out) next /\
    doneb next = true.
Proof.
  intros src out accepted.
  apply compile_sound in accepted.
  destruct accepted as [raw [_ loaded]].
  apply Comp.load_sound in loaded.
  destruct loaded as [value [_ ran]].
  apply Comp.run_sound in ran.
  destruct ran as [same [empty [rights [lowered [allowed [_ typed]]]]]].
  rewrite same.
  repeat split; assumption.
Qed.