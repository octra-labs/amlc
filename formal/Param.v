(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Fhe.

Import ListNotations.

Record fparam : Type := Fparam {
  pid : nat;
  pkey : nat;
  pcap : nat
}.

Definition fcatalog := list fparam.

Fixpoint pid_has (id : nat) (catalog : fcatalog) : bool :=
  match catalog with
  | [] => false
  | item :: rest => Nat.eqb id (pid item) || pid_has id rest
  end.

Fixpoint pcap_has (key cap : nat) (catalog : fcatalog) : bool :=
  match catalog with
  | [] => false
  | item :: rest =>
      (Nat.eqb key (pkey item) && Nat.eqb cap (pcap item))
        || pcap_has key cap rest
  end.

Fixpoint catalog_uniq (catalog : fcatalog) : bool :=
  match catalog with
  | [] => true
  | item :: rest =>
      negb (pid_has (pid item) rest)
        && negb (pcap_has (pkey item) (pcap item) rest)
        && catalog_uniq rest
  end.

Fixpoint catalog_vals_b (catalog : fcatalog) : bool :=
  match catalog with
  | [] => true
  | item :: rest =>
      ffit (pid item) && ffit (pkey item) && ffit (pcap item)
        && catalog_vals_b rest
  end.

Definition catalog_b (catalog : fcatalog) : bool :=
  Nat.leb (length catalog) fcount_max
    && catalog_uniq catalog && catalog_vals_b catalog.

Definition supports (key need : nat) (item : fparam) : bool :=
  Nat.eqb key (pkey item) && Nat.leb need (pcap item).

Definition pmin (first second : fparam) : fparam :=
  if Nat.leb (pcap first) (pcap second) then first else second.

Fixpoint psel (key need : nat) (catalog : fcatalog) : option fparam :=
  match catalog with
  | [] => None
  | item :: rest =>
      match supports key need item, psel key need rest with
      | true, Some found => Some (pmin item found)
      | true, None => Some item
      | false, found => found
      end
  end.

Definition params (catalog : fcatalog) (info : finfo) : option fparam :=
  psel (ekey (ety info)) (fpeak info) catalog.

Theorem pmin_le_first : forall first second,
  pcap (pmin first second) <= pcap first.
Proof.
  intros first second. unfold pmin.
  destruct (Nat.leb (pcap first) (pcap second)) eqn:Hle; simpl.
  - apply Nat.le_refl.
  - apply Nat.lt_le_incl. apply Nat.leb_gt. exact Hle.
Qed.

Theorem pmin_le_second : forall first second,
  pcap (pmin first second) <= pcap second.
Proof.
  intros first second. unfold pmin.
  destruct (Nat.leb (pcap first) (pcap second)) eqn:Hle; simpl.
  - apply Nat.leb_le. exact Hle.
  - apply Nat.le_refl.
Qed.

Theorem pmin_support : forall key need first second,
  supports key need first = true ->
  supports key need second = true ->
  supports key need (pmin first second) = true.
Proof.
  intros key need first second Hfirst Hsecond. unfold pmin.
  destruct (Nat.leb (pcap first) (pcap second)); assumption.
Qed.

Theorem psel_none : forall catalog key need,
  psel key need catalog = None ->
  forall item, In item catalog -> supports key need item = false.
Proof.
  induction catalog as [|head rest IH]; intros key need Hsel item Hin.
  - inversion Hin.
  - simpl in Hsel.
    destruct (supports key need head) eqn:Hhead.
    + destruct (psel key need rest); discriminate.
    + destruct Hin as [Heq | Hin].
      * subst item. exact Hhead.
      * eapply IH; eauto.
Qed.

Theorem psel_sound : forall catalog key need out,
  psel key need catalog = Some out ->
  supports key need out = true.
Proof.
  induction catalog as [|head rest IH]; intros key need out Hsel.
  - discriminate.
  - simpl in Hsel.
    destruct (supports key need head) eqn:Hhead.
    + destruct (psel key need rest) as [found |] eqn:Hrest.
      * inversion Hsel; subst out.
        apply pmin_support; [exact Hhead |].
        eapply IH. exact Hrest.
      * inversion Hsel; subst out. exact Hhead.
    + eapply IH. exact Hsel.
Qed.

Theorem psel_in : forall catalog key need out,
  psel key need catalog = Some out ->
  In out catalog.
Proof.
  induction catalog as [|head rest IH]; intros key need out Hsel.
  - discriminate.
  - simpl in Hsel.
    destruct (supports key need head) eqn:Hhead.
    + destruct (psel key need rest) as [found |] eqn:Hrest.
      * inversion Hsel; subst out. unfold pmin.
        destruct (Nat.leb (pcap head) (pcap found)).
        -- left. reflexivity.
        -- right. eapply IH. exact Hrest.
      * inversion Hsel; subst out. left. reflexivity.
    + right. eapply IH. exact Hsel.
Qed.

Theorem psel_complete : forall catalog key need item,
  In item catalog ->
  supports key need item = true ->
  exists out, psel key need catalog = Some out.
Proof.
  intros catalog key need item Hin Hitem.
  destruct (psel key need catalog) as [out |] eqn:Hsel.
  - exists out. reflexivity.
  - pose proof (psel_none catalog key need Hsel item Hin) as Hnone.
    rewrite Hitem in Hnone. discriminate.
Qed.

Theorem psel_min : forall catalog key need out item,
  psel key need catalog = Some out ->
  In item catalog ->
  supports key need item = true ->
  pcap out <= pcap item.
Proof.
  induction catalog as [|head rest IH]; intros key need out item Hsel Hin Hitem.
  - inversion Hin.
  - simpl in Hsel.
    destruct (supports key need head) eqn:Hhead.
    + destruct (psel key need rest) as [found |] eqn:Hrest.
      * inversion Hsel; subst out.
        destruct Hin as [Heq | Hin].
        -- subst item. apply pmin_le_first.
        -- eapply Nat.le_trans.
           ++ apply pmin_le_second.
           ++ eapply IH; eauto.
      * inversion Hsel; subst out.
        destruct Hin as [Heq | Hin].
        -- subst item. apply Nat.le_refl.
        -- pose proof (psel_none rest key need Hrest item Hin) as Hnone.
           rewrite Hitem in Hnone. discriminate.
    + destruct Hin as [Heq | Hin].
      * subst item. rewrite Hhead in Hitem. discriminate.
      * eapply IH; eauto.
Qed.

Theorem params_sound : forall catalog info out,
  params catalog info = Some out ->
  pkey out = ekey (ety info) /\ fpeak info <= pcap out.
Proof.
  intros catalog info out H.
  unfold params in H.
  pose proof (psel_sound catalog (ekey (ety info)) (fpeak info) out H) as Hsup.
  unfold supports in Hsup.
  destruct (Nat.eqb (ekey (ety info)) (pkey out)) eqn:Hkey;
    try discriminate.
  apply Nat.eqb_eq in Hkey. apply Nat.leb_le in Hsup.
  auto.
Qed.

Theorem params_in : forall catalog info out,
  params catalog info = Some out ->
  In out catalog.
Proof.
  intros catalog info out H.
  unfold params in H. eapply psel_in. exact H.
Qed.

Theorem params_complete : forall catalog info item,
  In item catalog ->
  supports (ekey (ety info)) (fpeak info) item = true ->
  exists out, params catalog info = Some out.
Proof.
  intros catalog info item Hin Hitem.
  unfold params. eapply psel_complete; eauto.
Qed.

Theorem params_min : forall catalog info out item,
  params catalog info = Some out ->
  In item catalog ->
  supports (ekey (ety info)) (fpeak info) item = true ->
  pcap out <= pcap item.
Proof.
  intros catalog info out item Hout Hin Hitem.
  unfold params in Hout.
  eapply psel_min; eauto.
Qed.