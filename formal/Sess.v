(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import List.

Require Import Lim.

Import ListNotations.

Record scope : Type := Scope {
  schain : list nat;
  sprog : list nat;
  sroot : list nat
}.

Fixpoint bytes_eqb (left right : list nat) : bool :=
  match left, right with
  | [], [] => true
  | first :: left', second :: right' =>
      Nat.eqb first second && bytes_eqb left' right'
  | _, _ => false
  end.

Definition scope_eqb (left right : scope) : bool :=
  bytes_eqb (schain left) (schain right) &&
  bytes_eqb (sprog left) (sprog right) &&
  bytes_eqb (sroot left) (sroot right).

Definition byte_b (value : nat) : bool := Nat.ltb value 256.

Definition raw_b (value : list nat) : bool :=
  fit (length value) && forallb byte_b value.

Definition scope_b (value : scope) : bool :=
  raw_b (schain value) && raw_b (sprog value) && raw_b (sroot value).

Lemma bytes_eqb_refl : forall value, bytes_eqb value value = true.
Proof.
  induction value; simpl; rewrite ?Nat.eqb_refl, ?IHvalue; reflexivity.
Qed.

Lemma bytes_eqb_eq : forall left right,
  bytes_eqb left right = true <-> left = right.
Proof.
  induction left as [|first rest repeat]; intros right; destruct right; simpl.
  - split; intros; reflexivity.
  - split; intros false; discriminate.
  - split; intros false; discriminate.
  - rewrite andb_true_iff, Nat.eqb_eq, repeat.
    split.
    + intros [same_head same_rest]. subst. reflexivity.
    + intros same. inversion same. auto.
Qed.

Lemma scope_eqb_refl : forall value, scope_eqb value value = true.
Proof.
  intros [chain prog root].
  unfold scope_eqb.
  simpl.
  rewrite !bytes_eqb_refl.
  reflexivity.
Qed.

Lemma scope_eqb_eq : forall left right,
  scope_eqb left right = true <-> left = right.
Proof.
  intros [left_chain left_prog left_root] [right_chain right_prog right_root].
  unfold scope_eqb.
  simpl.
  repeat rewrite andb_true_iff.
  repeat rewrite bytes_eqb_eq.
  split.
  - intros [[same_chain same_prog] same_root].
    subst.
    reflexivity.
  - intros same.
    inversion same.
    auto.
Qed.

Record sentry : Type := Entry {
  ekind : nat;
  eid : nat;
  erev : nat;
  elive : bool
}.

Record sview : Type := View {
  vscope : scope;
  ventries : list sentry
}.

Definition entry_b (entry : sentry) : bool :=
  fit (ekind entry) && fit (eid entry) && fit (erev entry).

Definition entry_lt (left right : sentry) : bool :=
  Nat.ltb (ekind left) (ekind right) ||
  (Nat.eqb (ekind left) (ekind right) && Nat.ltb (eid left) (eid right)).

Fixpoint order_b (entries : list sentry) : bool :=
  match entries with
  | [] | [_] => true
  | first :: (second :: _ as rest) =>
      entry_lt first second && order_b rest
  end.

Definition entries_b (entries : list sentry) : bool :=
  fit (length entries) && forallb entry_b entries && order_b entries.

Definition view_b (view : sview) : bool :=
  scope_b (vscope view) && entries_b (ventries view).

Fixpoint entry_get (entries : list sentry) (kind id : nat)
    : option (nat * bool) :=
  match entries with
  | [] => None
  | entry :: rest =>
      if Nat.eqb kind (ekind entry) && Nat.eqb id (eid entry) then
        Some (erev entry, elive entry)
      else entry_get rest kind id
  end.

Record stok : Type := Tok {
  tscope : scope;
  tkind : nat;
  tid : nat;
  trev : nat
}.

Record sstate : Type := State {
  sscope : scope;
  stable : nat -> nat -> option (nat * bool)
}.

Definition realize (view : sview) : sstate :=
  State (vscope view) (entry_get (ventries view)).

Definition sempty (domain : scope) : sstate :=
  State domain (fun _ _ => None).

Definition start (domain : scope) : option sstate :=
  if scope_b domain then Some (sempty domain) else None.

Definition keyb (kind id left right : nat) : bool :=
  Nat.eqb kind left && Nat.eqb id right.

Definition current (state : sstate) (token : stok) : bool :=
  if scope_eqb (sscope state) (tscope token) then
    match stable state (tkind token) (tid token) with
    | Some (rev, true) => Nat.eqb rev (trev token)
    | _ => false
    end
  else false.

Lemma realize_scope : forall view, sscope (realize view) = vscope view.
Proof.
  intros view.
  reflexivity.
Qed.

Lemma realize_slot : forall view kind id,
  stable (realize view) kind id = entry_get (ventries view) kind id.
Proof.
  intros view kind id.
  reflexivity.
Qed.

Theorem realize_current : forall view token,
  current (realize view) token =
    if scope_eqb (vscope view) (tscope token) then
      match entry_get (ventries view) (tkind token) (tid token) with
      | Some (rev, true) => Nat.eqb rev (trev token)
      | _ => false
      end
    else false.
Proof.
  intros view token.
  reflexivity.
Qed.

Theorem view_scope_valid : forall view,
  view_b view = true -> scope_b (vscope view) = true.
Proof.
  intros view valid.
  unfold view_b in valid.
  apply andb_true_iff in valid.
  exact (proj1 valid).
Qed.

Definition put (state : sstate) (token : stok) (live : bool) : sstate :=
  State (sscope state) (fun kind id =>
    if keyb kind id (tkind token) (tid token) then
      Some (trev token, live)
    else stable state kind id).

Definition bump (token : stok) : stok :=
  Tok (tscope token) (tkind token) (tid token) (S (trev token)).

Definition issue (state : sstate) (kind id : nat)
    : option (sstate * stok) :=
  if fit kind && fit id then
    match stable state kind id with
    | None =>
        let token := Tok (sscope state) kind id 0 in
        Some (put state token true, token)
    | Some _ => None
    end
  else None.

Definition take (state : sstate) (token : stok) (keep : bool)
    : option (sstate * option stok) :=
  if current state token then
    if keep then
      if fit (S (trev token)) then
        let fresh := bump token in
        Some (put state fresh true, Some fresh)
      else None
    else Some (put state token false, None)
  else None.

Lemma keyb_same : forall kind id,
  keyb kind id kind id = true.
Proof.
  intros kind id. unfold keyb. rewrite !Nat.eqb_refl. reflexivity.
Qed.

Lemma current_put : forall state token live,
  scope_eqb (sscope state) (tscope token) = true ->
  current (put state token live) token =
    if live then true else false.
Proof.
  intros [ctx table] [domain kind id rev] live scope_ok.
  cbn [sscope tscope] in scope_ok.
  unfold current, put.
  cbn [sscope stable tscope tkind tid trev].
  rewrite scope_ok.
  rewrite keyb_same.
  simpl.
  destruct live; simpl; rewrite ?Nat.eqb_refl; reflexivity.
Qed.

Lemma put_slot : forall state token live,
  stable (put state token live) (tkind token) (tid token) =
    Some (trev token, live).
Proof.
  intros state [domain kind id rev] live. unfold put. simpl.
  rewrite keyb_same. reflexivity.
Qed.

Lemma current_scope : forall state token,
  current state token = true ->
  scope_eqb (sscope state) (tscope token) = true.
Proof.
  intros state token accepted.
  unfold current in accepted.
  destruct (scope_eqb (sscope state) (tscope token)); try discriminate.
  reflexivity.
Qed.

Theorem issue_current : forall state kind id next token,
  issue state kind id = Some (next, token) ->
  current next token = true.
Proof.
  intros state kind id next token H.
  unfold issue in H.
  destruct (fit kind && fit id); try discriminate.
  destruct (stable state kind id); try discriminate.
  inversion H; subst. apply current_put. apply scope_eqb_refl.
Qed.

Theorem issue_again : forall state kind id next token,
  issue state kind id = Some (next, token) ->
  issue next kind id = None.
Proof.
  intros state kind id next token H.
  unfold issue in H.
  destruct (fit kind && fit id) eqn:Hfit; try discriminate.
  destruct (stable state kind id); try discriminate.
  inversion H; subst. unfold issue. rewrite Hfit.
  cbn [stable put tkind tid trev].
  rewrite keyb_same.
  reflexivity.
Qed.

Lemma current_old : forall state token,
  scope_eqb (sscope state) (tscope token) = true ->
  current (put state (bump token) true) token = false.
Proof.
  intros [ctx table] [domain kind id rev] scope_ok.
  cbn [sscope tscope] in scope_ok.
  unfold current, put, bump.
  cbn [sscope stable tscope tkind tid trev].
  rewrite scope_ok.
  rewrite keyb_same.
  simpl. induction rev; simpl; auto.
Qed.

Theorem take_old : forall state token next fresh,
  take state token true = Some (next, Some fresh) ->
  current next token = false.
Proof.
  intros state token next fresh H.
  unfold take in H.
  destruct (current state token) eqn:Hcur.
  - destruct (fit (S (trev token))) eqn:Hfit.
    + inversion H; subst. apply current_old. apply current_scope. exact Hcur.
    + discriminate.
  - discriminate.
Qed.

Theorem take_fresh : forall state token next fresh,
  take state token true = Some (next, Some fresh) ->
  current next fresh = true.
Proof.
  intros state token next fresh H.
  unfold take in H.
  destruct (current state token) eqn:Hcur.
  - destruct (fit (S (trev token))) eqn:Hfit.
    + inversion H; subst. apply current_put.
      change (scope_eqb (sscope state) (tscope token) = true).
      apply current_scope. exact Hcur.
    + discriminate.
  - discriminate.
Qed.

Theorem take_shape : forall state token next fresh,
  take state token true = Some (next, Some fresh) ->
  tscope fresh = tscope token /\
  tkind fresh = tkind token /\
  tid fresh = tid token /\
  trev fresh = S (trev token).
Proof.
  intros state token next fresh H.
  unfold take in H.
  destruct (current state token) eqn:Hcur.
  - destruct (fit (S (trev token))) eqn:Hfit.
    + inversion H; subst. destruct token. simpl. auto.
    + discriminate.
  - discriminate.
Qed.

Theorem take_replay : forall state token next fresh keep,
  take state token true = Some (next, Some fresh) ->
  take next token keep = None.
Proof.
  intros state token next fresh keep H.
  pose proof (take_old state token next fresh H) as Hold.
  unfold take. rewrite Hold. reflexivity.
Qed.

Theorem take_close : forall state token next,
  take state token false = Some (next, None) ->
  current next token = false.
Proof.
  intros state token next H.
  unfold take in H.
  destruct (current state token) eqn:Hcur.
  - inversion H; subst. rewrite current_put.
    + reflexivity.
    + apply current_scope. exact Hcur.
  - discriminate.
Qed.

Theorem take_no_issue : forall state token keep next out,
  take state token keep = Some (next, out) ->
  issue next (tkind token) (tid token) = None.
Proof.
  intros state [domain kind id rev] keep next out H.
  unfold take in H. cbn [tscope tkind tid trev] in H.
  destruct (current state (Tok domain kind id rev)) eqn:Hcur.
  - destruct keep.
    + destruct (fit (S rev)) eqn:Hfit.
      * inversion H; subst. unfold issue. cbn [bump tkind tid].
        destruct (fit kind && fit id) eqn:Hids.
        -- rewrite put_slot. reflexivity.
        -- reflexivity.
      * discriminate.
    + inversion H; subst. unfold issue. cbn [tkind tid].
      destruct (fit kind && fit id) eqn:Hids.
      * rewrite put_slot. reflexivity.
      * reflexivity.
  - discriminate.
Qed.

Theorem foreign_token : forall state token,
  scope_eqb (sscope state) (tscope token) = false ->
  current state token = false.
Proof.
  intros state token differs.
  unfold current.
  rewrite differs.
  reflexivity.
Qed.

Theorem foreign_scope : forall state token,
  sscope state <> tscope token ->
  current state token = false.
Proof.
  intros state token differs.
  apply foreign_token.
  destruct (scope_eqb (sscope state) (tscope token)) eqn:same.
  - apply scope_eqb_eq in same.
    contradiction.
  - reflexivity.
Qed.