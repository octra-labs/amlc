(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.

Require Import Rule.

Import ListNotations.
Open Scope string_scope.

Inductive target : Type :=
| TOctb1
| TOcps1.

Record src : Type := Src {
  src_path : string;
  src_body : string;
  src_deps : list string
}.

Record root : Type := Root {
  root_path : string;
  root_name : string;
  root_feed : string
}.

Record proj : Type := Proj {
  proj_srcs : list src;
  proj_roots : list root;
  proj_rule : rid;
  proj_target : target
}.

Definition code (value : ascii) : nat := nat_of_ascii value.

Definition between (low value high : nat) : bool :=
  Nat.leb low value && Nat.leb value high.

Definition alpha (value : ascii) : bool :=
  let raw := code value in
  between 97 raw 122 || between 65 raw 90 || Nat.eqb raw 95.

Definition digit (value : ascii) : bool :=
  between 48 (code value) 57.

Definition path_char (value : ascii) : bool :=
  alpha value || digit value || Nat.eqb (code value) 45
    || Nat.eqb (code value) 46.

Definition name_char (value : ascii) : bool :=
  alpha value || digit value || Nat.eqb (code value) 45.

Fixpoint size_at (value : string) (acc : nat) : nat :=
  match value with
  | EmptyString => acc
  | String _ rest => size_at rest (S acc)
  end.

Definition size (value : string) : nat := size_at value 0.

Definition seg_b (len : nat) (dots : bool) : bool :=
  posb len && negb (dots && Nat.leb len 2).

Fixpoint path_at (value : string) (len : nat) (dots : bool) : bool :=
  match value with
  | EmptyString => seg_b len dots
  | String item rest =>
      if Nat.eqb (code item) 47 then
        seg_b len dots && path_at rest 0 true
      else
        path_char item
          && path_at rest (S len) (dots && Nat.eqb (code item) 46)
  end.

Definition path_b (value : string) : bool :=
  posb (size value)
    && Nat.leb (size value) (rtext local)
    && path_at value 0 true.

Fixpoint chars_b (pred : ascii -> bool) (value : string) : bool :=
  match value with
  | EmptyString => true
  | String item rest => pred item && chars_b pred rest
  end.

Definition name_b (value : string) : bool :=
  posb (size value)
    && Nat.leb (size value) (rname local)
    && chars_b name_char value.

Definition body_b (value : string) : bool :=
  Nat.leb (size value) (rstr local).

Fixpoint str_has (item : string) (values : list string) : bool :=
  match values with
  | [] => false
  | value :: rest => String.eqb item value || str_has item rest
  end.

Fixpoint str_uniq (values : list string) : bool :=
  match values with
  | [] => true
  | value :: rest => negb (str_has value rest) && str_uniq rest
  end.

Definition deps_b (seen : list string) (values : list string) : bool :=
  Nat.leb (List.length values) (rinputs local)
    && str_uniq values
    && forallb path_b values
    && forallb (fun value => str_has value seen) values.

Definition src_b (seen : list string) (value : src) : bool :=
  path_b (src_path value)
    && body_b (src_body value)
    && negb (str_has (src_path value) seen)
    && deps_b seen (src_deps value).

Fixpoint srcs_b (seen : list string) (values : list src) : bool :=
  match values with
  | [] => true
  | value :: rest =>
      src_b seen value && srcs_b (src_path value :: seen) rest
  end.

Fixpoint src_names (values : list src) : list string :=
  match values with
  | [] => []
  | value :: rest => src_path value :: src_names rest
  end.

Definition root_b (paths used names : list string) (value : root) : bool :=
  str_has (root_path value) paths
    && name_b (root_name value)
    && negb (str_has (root_path value) used)
    && negb (str_has (root_name value) names).

Fixpoint roots_b (paths used names : list string) (values : list root) : bool :=
  match values with
  | [] => true
  | value :: rest =>
      root_b paths used names value
        && roots_b paths (root_path value :: used)
          (root_name value :: names) rest
  end.

Fixpoint strings_size (values : list string) : nat :=
  match values with
  | [] => 0
  | value :: rest => size value + strings_size rest
  end.

Definition src_size (value : src) : nat :=
  size (src_path value) + size (src_body value)
    + strings_size (src_deps value).

Fixpoint srcs_size (values : list src) : nat :=
  match values with
  | [] => 0
  | value :: rest => src_size value + srcs_size rest
  end.

Definition root_size (value : root) : nat :=
  size (root_path value) + size (root_name value) + size (root_feed value).

Fixpoint roots_size (values : list root) : nat :=
  match values with
  | [] => 0
  | value :: rest => root_size value + roots_size rest
  end.

Definition rid_b (value : rid) : bool :=
  posb (rver value)
    && limits_b (rlimv value)
    && limits_eqb (rlimv value) local.

Definition target_b (_ : target) : bool := true.

Definition proj_b (value : proj) : bool :=
  posb (List.length (proj_srcs value))
    && Nat.leb (List.length (proj_srcs value)) (rinputs local)
    && posb (List.length (proj_roots value))
    && Nat.leb (List.length (proj_roots value)) (rinputs local)
    && Nat.leb
      (srcs_size (proj_srcs value) + roots_size (proj_roots value))
      (rstr local)
    && rid_b (proj_rule value)
    && target_b (proj_target value)
    && srcs_b [] (proj_srcs value)
    && roots_b (src_names (proj_srcs value)) [] [] (proj_roots value).

Definition ext (value : target) : string :=
  match value with
  | TOctb1 => ".octb"
  | TOcps1 => ".ocps"
  end.

Definition out (kind : target) (value : root) : string :=
  append (root_name value) (ext kind).

Definition outputs (value : proj) : list string :=
  map (out (proj_target value)) (proj_roots value).

Inductive ordered : list string -> list src -> Prop :=
| OEnd : forall seen, ordered seen []
| ONext : forall seen value rest,
    src_b seen value = true ->
    ordered (src_path value :: seen) rest ->
    ordered seen (value :: rest).

Theorem str_has_in : forall item values,
  str_has item values = true -> In item values.
Proof.
  intros item values.
  induction values as [|value rest IH]; simpl; intros found.
  - discriminate.
  - apply orb_true_iff in found as [same | found].
    + apply String.eqb_eq in same. subst. left. reflexivity.
    + right. apply IH. exact found.
Qed.

Theorem src_b_dep : forall seen value dep,
  src_b seen value = true ->
  In dep (src_deps value) ->
  In dep seen.
Proof.
  intros seen value dep accepted present.
  unfold src_b in accepted.
  apply andb_true_iff in accepted as [_ deps].
  unfold deps_b in deps.
  apply andb_true_iff in deps as [_ seen_ok].
  rewrite forallb_forall in seen_ok.
  apply str_has_in.
  apply seen_ok.
  exact present.
Qed.

Theorem srcs_order : forall seen values,
  srcs_b seen values = true -> ordered seen values.
Proof.
  intros seen values.
  revert seen.
  induction values as [|value rest IH]; intros seen accepted; simpl in accepted.
  - constructor.
  - apply andb_true_iff in accepted as [head tail].
    constructor.
    + exact head.
    + apply IH. exact tail.
Qed.

Theorem proj_order : forall value,
  proj_b value = true -> ordered [] (proj_srcs value).
Proof.
  intros value accepted.
  unfold proj_b in accepted.
  apply andb_true_iff in accepted as [left roots].
  apply andb_true_iff in left as [left sources].
  apply srcs_order.
  exact sources.
Qed.

Theorem proj_roots_ok : forall value,
  proj_b value = true ->
  roots_b (src_names (proj_srcs value)) [] [] (proj_roots value) = true.
Proof.
  intros value accepted.
  unfold proj_b in accepted.
  apply andb_true_iff in accepted as [_ roots].
  exact roots.
Qed.

Theorem output_in : forall kind values value,
  In value values -> In (out kind value) (map (out kind) values).
Proof.
  intros kind values value present.
  apply in_map.
  exact present.
Qed.