(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.

Require Import Rule.
Require Import Proj.
Require Import Pimg.
Require Import Bin.
Require Import Ser.
Require Import Seal.
Require Import Smap.
Require Import Live.
Require Import Feed.

Import ListNotations.
Open Scope string_scope.

Record part : Type := Part {
  part_path : string;
  part_name : string;
  part_octb : string;
  part_seal : bits;
  part_map : bits;
  part_live : bits
}.

Record folio : Type := Folio {
  folio_proj : proj;
  folio_epoch : nat;
  folio_parts : list part
}.

Record origin : Type := Origin {
  osrc : src;
  oroot : root;
  opart : part;
  ofeed : option (list Uni.value);
  ospans : list Lex.span;
  orows : list (list Live.slot)
}.

Fixpoint src_at (path : string) (values : list src) : option src :=
  match values with
  | [] => None
  | value :: rest =>
      if String.eqb path (src_path value) then Some value else src_at path rest
  end.

Fixpoint octets (input : string) : list nat :=
  match input with
  | EmptyString => []
  | String item rest => nat_of_ascii item :: octets rest
  end.

Definition feed_at (input : string) : option (option (list Uni.value)) :=
  if String.eqb input EmptyString then Some None
  else
    match Feed.dec_feed (octets input) with
    | Some values => Some (Some values)
    | None => None
    end.

Definition origin_one (srcs : list src) (root : root) (part : part)
    : option origin :=
  if String.eqb (root_path root) (part_path part)
      && String.eqb (root_name root) (part_name part) then
    match src_at (root_path root) srcs, feed_at (root_feed root),
      Smap.dec_map (part_map part), Live.dec_live (part_live part) with
    | Some source, Some feed, Some spans, Some rows =>
        Some (Origin source root part feed spans rows)
    | _, _, _, _ => None
    end
  else None.

Fixpoint origins_at (srcs : list src) (roots : list root) (parts : list part)
    : option (list origin) :=
  match roots, parts with
  | [], [] => Some []
  | root :: root_rest, part :: part_rest =>
      match origin_one srcs root part,
        origins_at srcs root_rest part_rest with
      | Some first, Some rest => Some (first :: rest)
      | _, _ => None
      end
  | _, _ => None
  end.

Definition origins (value : folio) : option (list origin) :=
  origins_at (proj_srcs (folio_proj value))
    (proj_roots (folio_proj value)) (folio_parts value).

Definition origin_b (value : folio) : bool :=
  match origins value with
  | Some _ => true
  | None => false
  end.

Lemma src_at_path : forall path values source,
  src_at path values = Some source -> src_path source = path.
Proof.
  intros path values.
  induction values as [|value rest IH]; intros source found; simpl in found.
  - discriminate.
  - destruct (String.eqb path (src_path value)) eqn:same.
    + inversion found; subst source.
      apply String.eqb_eq in same.
      symmetry.
      exact same.
    + apply IH.
      exact found.
Qed.

Lemma feed_at_none : forall input,
  feed_at input = Some None -> input = EmptyString.
Proof.
  intros input found.
  unfold feed_at in found.
  destruct (String.eqb input EmptyString) eqn:empty.
  - apply String.eqb_eq.
    exact empty.
  - destruct (Feed.dec_feed (octets input)); discriminate.
Qed.

Lemma feed_at_some : forall input values,
  feed_at input = Some (Some values) ->
  Feed.dec_feed (octets input) = Some values.
Proof.
  intros input values found.
  unfold feed_at in found.
  destruct (String.eqb input EmptyString) eqn:empty; try discriminate.
  destruct (Feed.dec_feed (octets input)) as [decoded |] eqn:feed;
    try discriminate.
  inversion found; subst decoded.
  reflexivity.
Qed.

Theorem origin_one_exact : forall srcs root part out,
  origin_one srcs root part = Some out ->
  String.eqb (root_path root) (part_path part)
      && String.eqb (root_name root) (part_name part) = true /\
  src_at (root_path root) srcs = Some (osrc out) /\
  feed_at (root_feed root) = Some (ofeed out) /\
  Smap.dec_map (part_map part) = Some (ospans out) /\
  Live.dec_live (part_live part) = Some (orows out) /\
  oroot out = root /\
  opart out = part /\
  src_path (osrc out) = root_path root.
Proof.
  intros srcs root part out accepted.
  unfold origin_one in accepted.
  destruct
    (String.eqb (root_path root) (part_path part)
      && String.eqb (root_name root) (part_name part))
    eqn:aligned; try discriminate.
  destruct (src_at (root_path root) srcs) as [source |] eqn:source_ok;
    try discriminate.
  destruct (feed_at (root_feed root)) as [feed |] eqn:feed_ok;
    try discriminate.
  destruct (Smap.dec_map (part_map part)) as [spans |] eqn:map_ok;
    try discriminate.
  destruct (Live.dec_live (part_live part)) as [rows |] eqn:live_ok;
    try discriminate.
  inversion accepted; subst out.
  repeat split; try assumption; try reflexivity.
  eapply src_at_path.
  exact source_ok.
Qed.

Theorem origin_one_unique : forall srcs root part left right,
  origin_one srcs root part = Some left ->
  origin_one srcs root part = Some right ->
  left = right.
Proof.
  intros srcs root part left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Inductive origins_rel (srcs : list src)
    : list root -> list part -> list origin -> Prop :=
| OriginsEnd : origins_rel srcs [] [] []
| OriginsNext : forall root roots part parts first rest,
    origin_one srcs root part = Some first ->
    origins_rel srcs roots parts rest ->
    origins_rel srcs (root :: roots) (part :: parts) (first :: rest).

Theorem origins_at_sound : forall srcs roots parts out,
  origins_at srcs roots parts = Some out ->
  origins_rel srcs roots parts out.
Proof.
  intros srcs roots.
  induction roots as [|root roots IH]; intros parts out accepted;
    destruct parts as [|part parts]; simpl in accepted; try discriminate.
  - inversion accepted; subst out.
    constructor.
  - destruct (origin_one srcs root part) as [first |] eqn:first_ok;
      try discriminate.
    destruct (origins_at srcs roots parts) as [rest |] eqn:rest_ok;
      try discriminate.
    inversion accepted; subst out.
    constructor.
    + exact first_ok.
    + apply IH.
      exact rest_ok.
Qed.

Theorem origins_rel_order : forall srcs roots parts out,
  origins_rel srcs roots parts out ->
  map oroot out = roots /\ map opart out = parts.
Proof.
  intros srcs roots parts out related.
  induction related.
  - split; reflexivity.
  - destruct IHrelated as [roots_ok parts_ok].
    pose proof (origin_one_exact srcs root part0 first H) as exact.
    destruct exact as [_ [_ [_ [_ [_ [root_ok [part_ok _]]]]]]].
    simpl.
    rewrite roots_ok, parts_ok.
    rewrite root_ok, part_ok.
    split; reflexivity.
Qed.

Theorem origins_exact : forall value out,
  origins value = Some out ->
  origins_rel (proj_srcs (folio_proj value))
    (proj_roots (folio_proj value)) (folio_parts value) out /\
  map oroot out = proj_roots (folio_proj value) /\
  map opart out = folio_parts value.
Proof.
  intros value out accepted.
  unfold origins in accepted.
  pose proof
    (origins_at_sound (proj_srcs (folio_proj value))
      (proj_roots (folio_proj value)) (folio_parts value) out accepted)
    as related.
  pose proof
    (origins_rel_order (proj_srcs (folio_proj value))
      (proj_roots (folio_proj value)) (folio_parts value) out related)
    as order.
  tauto.
Qed.

Theorem origins_unique : forall value left right,
  origins value = Some left -> origins value = Some right -> left = right.
Proof.
  intros value left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Theorem origin_b_total : forall value,
  origin_b value = true -> exists out, origins value = Some out.
Proof.
  intros value accepted.
  unfold origin_b in accepted.
  destruct (origins value) as [out |] eqn:found; try discriminate.
  exists out.
  reflexivity.
Qed.

Definition someb {A : Type} (value : option A) : bool :=
  match value with
  | Some _ => true
  | None => false
  end.

Definition raw_b (value : string) : bool :=
  posb (Proj.size value) && Nat.leb (Proj.size value) (rstr local).

Definition part_b (value : part) : bool :=
  path_b (part_path value)
    && name_b (part_name value)
    && raw_b (part_octb value)
    && someb (Seal.dec_artifact (part_seal value))
    && someb (Smap.dec_map (part_map value))
    && someb (Live.dec_live (part_live value)).

Fixpoint parts_b (roots : list root) (parts : list part) : bool :=
  match roots, parts with
  | [], [] => true
  | root :: root_rest, part :: part_rest =>
      String.eqb (root_path root) (part_path part)
        && String.eqb (root_name root) (part_name part)
        && part_b part
        && parts_b root_rest part_rest
  | _, _ => false
  end.

Definition octb_b (value : target) : bool :=
  match value with
  | TOctb1 => true
  | TOcps1 => false
  end.

Definition shape_b (value : folio) : bool :=
  Pimg.image_b (folio_proj value)
    && octb_b (proj_target (folio_proj value))
    && parts_b (proj_roots (folio_proj value)) (folio_parts value).

Definition bit_code (value : bool) : code :=
  if value then CTag 1 CNil else CTag 0 CNil.

Definition bit_get (input : code) : option bool :=
  match input with
  | CTag 0 CNil => Some false
  | CTag 1 CNil => Some true
  | _ => None
  end.

Lemma bit_get_code : forall value,
  bit_get (bit_code value) = Some value.
Proof.
  intros value.
  destruct value; reflexivity.
Qed.

Definition bits_code (values : bits) : code := list_code bit_code values.
Definition bits_get (input : code) : option bits := list_get bit_get input.

Lemma bits_get_code : forall values,
  bits_get (bits_code values) = Some values.
Proof.
  intros values.
  apply list_get_code.
  intros value _.
  apply bit_get_code.
Qed.

Definition part_code (value : part) : code :=
  CTag 4
    (CCons (Pimg.text_code (part_path value))
      (CCons (Pimg.text_code (part_name value))
        (CCons (Pimg.text_code (part_octb value))
          (CCons (bits_code (part_seal value))
            (CCons (bits_code (part_map value))
              (CCons (bits_code (part_live value)) CNil)))))).

Definition part_get (input : code) : option part :=
  match input with
  | CTag 4
      (CCons path
        (CCons name
          (CCons octb
            (CCons seal (CCons map (CCons live CNil)))))) =>
      match Pimg.text_get path, Pimg.text_get name, Pimg.text_get octb,
        bits_get seal, bits_get map, bits_get live with
      | Some path', Some name', Some octb', Some seal', Some map', Some live' =>
          Some (Part path' name' octb' seal' map' live')
      | _, _, _, _, _, _ => None
      end
  | _ => None
  end.

Lemma part_get_code : forall value,
  part_get (part_code value) = Some value.
Proof.
  intros [path name octb seal map live].
  simpl.
  rewrite Pimg.text_get_code, Pimg.text_get_code, Pimg.text_get_code.
  rewrite bits_get_code, bits_get_code, bits_get_code.
  reflexivity.
Qed.

Definition folio_code (value : folio) : code :=
  CTag 5
    (CCons (Pimg.proj_code (folio_proj value))
      (CCons (CNum (folio_epoch value))
        (CCons (list_code part_code (folio_parts value)) CNil))).

Definition folio_shape (input : code) : option folio :=
  match input with
  | CTag 5 (CCons project (CCons (CNum epoch) (CCons parts CNil))) =>
      match Pimg.proj_get project, list_get part_get parts with
      | Some project', Some parts' => Some (Folio project' epoch parts')
      | _, _ => None
      end
  | _ => None
  end.

Lemma folio_shape_code : forall value,
  Pimg.image_b (folio_proj value) = true ->
  folio_shape (folio_code value) = Some value.
Proof.
  intros [project epoch parts] project_ok.
  simpl in project_ok |- *.
  rewrite Pimg.proj_get_code, list_get_code.
  - reflexivity.
  - intros value _.
    apply part_get_code.
  - exact project_ok.
Qed.

Definition folio_get (input : code) : option folio :=
  match folio_shape input with
  | Some value => if shape_b value then Some value else None
  | None => None
  end.

Definition folio_bits (value : folio) : bits := Ser.enc folio_code value.

Definition folio_fit (value : folio) : bool :=
  shape_b value && Nat.leb (List.length (folio_bits value)) (rstr local).

Definition enc_folio (value : folio) : option bits :=
  if folio_fit value then Some (folio_bits value) else None.

Definition dec_folio (input : bits) : option folio :=
  if Nat.leb (List.length input) (rstr local) then
    Ser.dec folio_code folio_get input
  else None.

Lemma folio_project : forall value,
  shape_b value = true -> Pimg.image_b (folio_proj value) = true.
Proof.
  intros value accepted.
  unfold shape_b in accepted.
  repeat rewrite andb_true_iff in accepted.
  tauto.
Qed.

Lemma folio_get_code : forall value,
  shape_b value = true -> folio_get (folio_code value) = Some value.
Proof.
  intros value accepted.
  unfold folio_get.
  rewrite folio_shape_code, accepted.
  - reflexivity.
  - apply folio_project.
    exact accepted.
Qed.

Theorem folio_decode_encode : forall value,
  folio_fit value = true -> dec_folio (folio_bits value) = Some value.
Proof.
  intros value fit.
  unfold folio_fit in fit.
  apply andb_true_iff in fit.
  destruct fit as [valid size].
  unfold dec_folio.
  rewrite size.
  unfold folio_bits.
  rewrite Ser.dec_enc.
  - reflexivity.
  - apply folio_get_code.
    exact valid.
Qed.

Theorem folio_encode_decode : forall input value,
  dec_folio input = Some value -> enc_folio value = Some input.
Proof.
  intros input value accepted.
  unfold dec_folio in accepted.
  destruct (Nat.leb (List.length input) (rstr local)) eqn:size;
    try discriminate.
  assert (valid : shape_b value = true).
  {
    unfold Ser.dec in accepted.
    destruct (get_code input) as [shape |] eqn:shape_ok; try discriminate.
    destruct (folio_get shape) as [found |] eqn:value_ok; try discriminate.
    destruct (code_eqb (folio_code found) shape) eqn:exact; try discriminate.
    inversion accepted; subst found.
    unfold folio_get in value_ok.
    destruct (folio_shape shape) as [seen |] eqn:seen_ok; try discriminate.
    destruct (shape_b seen) eqn:seen_valid; try discriminate.
    inversion value_ok; subst seen.
    exact seen_valid.
  }
  pose proof
    (Ser.enc_dec folio folio_code folio_get input value accepted) as exact.
  unfold enc_folio, folio_fit, folio_bits.
  rewrite valid, exact, size.
  reflexivity.
Qed.

Theorem folio_roots : forall value,
  shape_b value = true ->
  parts_b (proj_roots (folio_proj value)) (folio_parts value) = true.
Proof.
  intros value accepted.
  unfold shape_b in accepted.
  repeat rewrite andb_true_iff in accepted.
  tauto.
Qed.