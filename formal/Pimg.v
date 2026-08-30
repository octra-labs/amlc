(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.

Require Import Proj.
Require Import Bin.
Require Import Ser.
Require Import Rule.

Import ListNotations.
Open Scope string_scope.

Lemma ascii_small : forall item,
  Nat.ltb (nat_of_ascii item) 256 = true.
Proof.
  intros [a b c d e f g h].
  destruct a, b, c, d, e, f, g, h; reflexivity.
Qed.

Fixpoint text_code (value : string) : code :=
  match value with
  | EmptyString => CNil
  | String item rest => CCons (CNum (nat_of_ascii item)) (text_code rest)
  end.

Fixpoint text_get (input : code) : option string :=
  match input with
  | CNil => Some EmptyString
  | CCons (CNum item) rest =>
      if Nat.ltb item 256 then
        match text_get rest with
        | Some value => Some (String (ascii_of_nat item) value)
        | None => None
        end
      else None
  | _ => None
  end.

Lemma text_get_code : forall value,
  text_get (text_code value) = Some value.
Proof.
  induction value as [|item rest IH]; simpl.
  - reflexivity.
  - rewrite ascii_small, IH, ascii_nat_embedding.
    reflexivity.
Qed.

Definition rid_code (value : rid) : code :=
  CTag 0 (list_code CNum (rid_vals value)).

Definition rid_shape (input : code) : option rid :=
  match input with
  | CTag 0
      (CCons (CNum ver)
        (CCons (CNum nat)
          (CCons (CNum str)
            (CCons (CNum text)
              (CCons (CNum ty_depth)
                (CCons (CNum ty_nodes)
                  (CCons (CNum tm_depth)
                    (CCons (CNum tm_nodes)
                      (CCons (CNum inputs)
                        (CCons (CNum fuel)
                          (CCons (CNum name)
                            (CCons (CNum tag) CNil)))))))))))) =>
      Some (Rid ver
        (Rlim nat str text ty_depth ty_nodes tm_depth tm_nodes inputs fuel
          name tag))
  | _ => None
  end.

Definition rid_image_b (value : rid) : bool :=
  rid_b value && Nat.leb (rver value) (rnat local).

Definition rid_get (input : code) : option rid :=
  match rid_shape input with
  | Some value => if rid_image_b value then Some value else None
  | None => None
  end.

Lemma rid_shape_code : forall value,
  rid_shape (rid_code value) = Some value.
Proof.
  intros [ver limits].
  destruct limits.
  reflexivity.
Qed.

Lemma rid_get_code : forall value,
  rid_image_b value = true ->
  rid_get (rid_code value) = Some value.
Proof.
  intros value valid.
  unfold rid_get.
  rewrite rid_shape_code, valid.
  reflexivity.
Qed.

Definition target_code (value : target) : code :=
  match value with
  | TOctb1 => CTag 0 CNil
  | TOcps1 => CTag 1 CNil
  end.

Definition target_get (input : code) : option target :=
  match input with
  | CTag 0 CNil => Some TOctb1
  | CTag 1 CNil => Some TOcps1
  | _ => None
  end.

Lemma target_get_code : forall value,
  target_get (target_code value) = Some value.
Proof.
  intros value.
  destruct value; reflexivity.
Qed.

Definition src_code (value : src) : code :=
  CTag 1 (CCons (text_code (src_path value))
    (CCons (text_code (src_body value))
      (CCons (list_code text_code (src_deps value)) CNil))).

Definition src_get (input : code) : option src :=
  match input with
  | CTag 1 (CCons path (CCons body (CCons deps CNil))) =>
      match text_get path, text_get body, list_get text_get deps with
      | Some path', Some body', Some deps' => Some (Src path' body' deps')
      | _, _, _ => None
      end
  | _ => None
  end.

Lemma src_get_code : forall value,
  src_get (src_code value) = Some value.
Proof.
  intros [path body deps].
  simpl.
  rewrite text_get_code, text_get_code, list_get_code.
  - reflexivity.
  - intros value _.
    apply text_get_code.
Qed.

Definition root_code (value : root) : code :=
  CTag 2 (CCons (text_code (root_path value))
    (CCons (text_code (root_name value))
      (CCons (text_code (root_feed value)) CNil))).

Definition root_get (input : code) : option root :=
  match input with
  | CTag 2 (CCons path (CCons name (CCons feed CNil))) =>
      match text_get path, text_get name, text_get feed with
      | Some path', Some name', Some feed' => Some (Root path' name' feed')
      | _, _, _ => None
      end
  | _ => None
  end.

Lemma root_get_code : forall value,
  root_get (root_code value) = Some value.
Proof.
  intros [path name feed].
  simpl.
  rewrite text_get_code, text_get_code, text_get_code.
  reflexivity.
Qed.

Definition proj_code (value : proj) : code :=
  CTag 3 (CCons (list_code src_code (proj_srcs value))
    (CCons (list_code root_code (proj_roots value))
      (CCons (rid_code (proj_rule value))
        (CCons (target_code (proj_target value)) CNil)))).

Definition proj_shape (input : code) : option proj :=
  match input with
  | CTag 3 (CCons srcs (CCons roots (CCons rule (CCons kind CNil)))) =>
      match list_get src_get srcs, list_get root_get roots,
        rid_get rule, target_get kind with
      | Some srcs', Some roots', Some rule', Some kind' =>
          Some (Proj srcs' roots' rule' kind')
      | _, _, _, _ => None
      end
  | _ => None
  end.

Definition image_b (value : proj) : bool :=
  proj_b value
    && Nat.leb (rver (proj_rule value)) (rnat local)
    && Nat.leb (List.length (put_code (proj_code value))) (rstr local).

Definition proj_get (input : code) : option proj :=
  match proj_shape input with
  | Some value => if image_b value then Some value else None
  | None => None
  end.

Lemma proj_shape_code : forall value,
  rid_image_b (proj_rule value) = true ->
  proj_shape (proj_code value) = Some value.
Proof.
  intros [srcs roots rule kind] rule_ok.
  simpl in rule_ok |- *.
  rewrite list_get_code, list_get_code, rid_get_code, target_get_code.
  - reflexivity.
  - exact rule_ok.
  - intros value _.
    apply root_get_code.
  - intros value _.
    apply src_get_code.
Qed.

Lemma image_rid : forall value,
  image_b value = true -> rid_image_b (proj_rule value) = true.
Proof.
  intros value valid.
  unfold image_b in valid.
  repeat rewrite andb_true_iff in valid.
  destruct valid as [[project version] size].
  unfold rid_image_b.
  rewrite version, andb_true_r.
  unfold proj_b in project.
  repeat rewrite andb_true_iff in project.
  tauto.
Qed.

Lemma proj_get_code : forall value,
  image_b value = true ->
  proj_get (proj_code value) = Some value.
Proof.
  intros value valid.
  unfold proj_get.
  rewrite proj_shape_code, valid.
  - reflexivity.
  - apply image_rid.
    exact valid.
Qed.

Definition enc_proj (value : proj) : option bits :=
  if image_b value then Some (enc proj_code value) else None.

Definition dec_proj : bits -> option proj := dec proj_code proj_get.

Theorem proj_decode_encode : forall value input,
  enc_proj value = Some input ->
  dec_proj input = Some value.
Proof.
  intros value input encoded.
  unfold enc_proj in encoded.
  destruct (image_b value) eqn:valid; try discriminate.
  inversion encoded; subst input.
  unfold dec_proj.
  apply dec_enc.
  apply proj_get_code.
  exact valid.
Qed.

Theorem proj_encode_decode : forall input value,
  dec_proj input = Some value ->
  enc_proj value = Some input.
Proof.
  intros input value decoded.
  assert (valid : image_b value = true).
  {
    unfold dec_proj, dec in decoded.
    destruct (get_code input) as [shape |] eqn:shape_ok; try discriminate.
    destruct (proj_get shape) as [found |] eqn:value_ok; try discriminate.
    destruct (code_eqb (proj_code found) shape) eqn:exact; try discriminate.
    inversion decoded; subst.
    unfold proj_get in value_ok.
    destruct (proj_shape shape) as [seen |] eqn:seen_ok; try discriminate.
    destruct (image_b seen) eqn:seen_valid; try discriminate.
    inversion value_ok; subst.
    exact seen_valid.
  }
  pose proof (enc_dec proj proj_code proj_get input value decoded) as exact.
  unfold enc_proj.
  rewrite valid, exact.
  reflexivity.
Qed.