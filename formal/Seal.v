(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import String.

Require Import Uni.
Require Import Bin.
Require Import Ser.
Require Import Low.
Require Import Rule.
Require Import Cert.
Require Import Fun.
Require Import Perm.
Require Import Read.
Require Import Comp.
Require Import Src.

Import ListNotations.

Definition bit_code (value : bool) : code :=
  if value then CTag 1 CNil else CTag 0 CNil.

Definition bit_get (input : code) : option bool :=
  match input with
  | CTag 0 CNil => Some false
  | CTag 1 CNil => Some true
  | _ => None
  end.

Lemma bit_get_code : forall value, bit_get (bit_code value) = Some value.
Proof.
  intros value.
  destruct value; reflexivity.
Qed.

Record artifact : Type := Artifact {
  acore : bits;
  ares : res
}.

Definition artifact_code (value : artifact) : code :=
  CTag 0 (CCons (list_code bit_code (acore value))
    (CCons (res_code (ares value)) CNil)).

Definition artifact_get (input : code) : option artifact :=
  match input with
  | CTag 0 (CCons core (CCons used CNil)) =>
      match list_get bit_get core, res_get used with
      | Some core, Some used => Some (Artifact core used)
      | _, _ => None
      end
  | _ => None
  end.

Lemma artifact_get_code : forall value,
  artifact_get (artifact_code value) = Some value.
Proof.
  intros [core used].
  unfold artifact_get, artifact_code.
  rewrite list_get_code, res_get_code.
  - reflexivity.
  - intros value _.
    apply bit_get_code.
Qed.

Definition enc_artifact := enc artifact_code.
Definition dec_artifact := dec artifact_code artifact_get.

Theorem artifact_decode_encode : forall value,
  dec_artifact (enc_artifact value) = Some value.
Proof.
  intros value.
  apply dec_enc.
  apply artifact_get_code.
Qed.

Theorem artifact_encode_decode : forall input value,
  dec_artifact input = Some value -> enc_artifact value = input.
Proof.
  apply enc_dec.
Qed.

Definition src_ok (out : Comp.image) : Prop :=
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

Definition cert_ok (rules : list rule) (epoch : nat)
    (out : Comp.image) (input : bits) : Prop :=
  exists value gamma id raw next selected,
    Cert.dec_cert input = Some value /\
    Cert.cprog value = (Comp.iins out, Comp.iterm out) /\
    opens [] (fst (Cert.cprog value)) = Some gamma /\
    rcheck rules epoch gamma (snd (Cert.cprog value)) =
      Some (id, (Cert.ctyp value, raw, Cert.cres value, next)) /\
    Cert.crule value = rid_vals id /\
    Cert.crow value = Cert.row_norm raw /\
    doneb next = true /\
    check gamma (snd (Cert.cprog value)) (Cert.ctyp value) raw
      (Cert.cres value) next /\
    rsel epoch rules = Some selected /\
    rrid selected = id /\
    active epoch selected = true.

Definition sealed (rules : list rule) (epoch : nat)
    (src : string) (input : bits) : Prop :=
  exists out core,
    Src.compile src = Some out /\
    src_ok out /\
    dec_artifact input = Some (Artifact core (Comp.ires out)) /\
    cert_ok rules epoch out core.

Definition source_seal (rules : list rule) (epoch : nat)
    (src : string) : option bits :=
  match Src.compile src with
  | Some out =>
      match Cert.issue rules epoch (Comp.iins out, Comp.iterm out) with
      | Some core => Some (enc_artifact (Artifact core (Comp.ires out)))
      | None => None
      end
  | None => None
  end.

Definition source_acceptb (rules : list rule) (epoch : nat)
    (src : string) (input : bits) : bool :=
  match source_seal rules epoch src with
  | Some exact => bits_eqb exact input
  | None => false
  end.

Theorem source_seal_sound : forall rules epoch src input,
  source_seal rules epoch src = Some input ->
  exists out core,
    Src.compile src = Some out /\
    Cert.issue rules epoch (Comp.iins out, Comp.iterm out) = Some core /\
    input = enc_artifact (Artifact core (Comp.ires out)) /\
    Cert.verifyb rules epoch core = true.
Proof.
  intros rules epoch src input issued.
  unfold source_seal in issued.
  destruct (Src.compile src) as [out |] eqn:compiled; try discriminate.
  destruct (Cert.issue rules epoch (Comp.iins out, Comp.iterm out))
    as [core |] eqn:certed; try discriminate.
  inversion issued; subst input.
  exists out, core.
  repeat split; try assumption; try reflexivity.
  eapply Cert.issue_verify.
  exact certed.
Qed.

Theorem source_seal_checked : forall rules epoch src input,
  source_seal rules epoch src = Some input ->
  sealed rules epoch src input.
Proof.
  intros rules epoch src input issued.
  pose proof (source_seal_sound rules epoch src input issued)
    as [out [core [compiled [certed [encoded verified]]]]].
  pose proof (Src.compile_checked src out compiled) as checked_src.
  pose proof (Cert.issue_decode rules epoch
    (Comp.iins out, Comp.iterm out) core certed)
    as [made_id [made_ty [made_row [made_cost decoded_exact]]]].
  destruct (Cert.verify_sound rules epoch core verified)
    as [value [gamma [id [raw [next [selected cert]]]]]].
  destruct cert as [decoded cert].
  destruct cert as [opened cert].
  destruct cert as [checked cert].
  destruct cert as [same_id cert].
  destruct cert as [same_row cert].
  destruct cert as [done cert].
  destruct cert as [typed cert].
  destruct cert as [chosen cert].
  destruct cert as [selected_id selected_active].
  rewrite decoded_exact in decoded.
  inversion decoded; subst value.
  exists out, core.
  split.
  - exact compiled.
  - split.
    + exact checked_src.
    + split.
      * rewrite encoded.
        apply artifact_decode_encode.
      * unfold cert_ok.
        exists (Cert.Cert (Comp.iins out, Comp.iterm out)
          (rid_vals made_id) made_ty (Cert.row_norm made_row) made_cost).
        exists gamma.
        exists id.
        exists raw.
        exists next.
        exists selected.
        repeat split; try assumption; reflexivity.
Qed.

Theorem source_seal_unique : forall rules epoch src left right,
  source_seal rules epoch src = Some left ->
  source_seal rules epoch src = Some right ->
  left = right.
Proof.
  intros rules epoch src left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Theorem source_seal_accept : forall rules epoch src input,
  source_seal rules epoch src = Some input ->
  source_acceptb rules epoch src input = true.
Proof.
  intros rules epoch src input issued.
  unfold source_acceptb.
  rewrite issued.
  apply (proj2 (bits_eqb_eq input input)).
  reflexivity.
Qed.

Theorem source_accept_seal : forall rules epoch src input,
  source_acceptb rules epoch src input = true ->
  source_seal rules epoch src = Some input.
Proof.
  intros rules epoch src input accepted.
  unfold source_acceptb in accepted.
  destruct (source_seal rules epoch src) as [exact |] eqn:issued;
    try discriminate.
  apply bits_eqb_eq in accepted.
  subst exact.
  reflexivity.
Qed.

Theorem source_accept_checked : forall rules epoch src input,
  source_acceptb rules epoch src input = true ->
  sealed rules epoch src input.
Proof.
  intros rules epoch src input accepted.
  apply source_accept_seal in accepted.
  eapply source_seal_checked.
  exact accepted.
Qed.

Theorem source_accept_unique : forall rules epoch src left right,
  source_acceptb rules epoch src left = true ->
  source_acceptb rules epoch src right = true ->
  left = right.
Proof.
  intros rules epoch src left right lhs rhs.
  apply source_accept_seal in lhs.
  apply source_accept_seal in rhs.
  eapply source_seal_unique; eassumption.
Qed.