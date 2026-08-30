(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import String.

Require Import Proj.

Import ListNotations.
Open Scope string_scope.

Record item : Type := Item {
  item_src : src;
  item_root : root
}.

Fixpoint src_at (path : string) (values : list src) : option src :=
  match values with
  | [] => None
  | value :: rest =>
      if String.eqb path (src_path value) then Some value
      else src_at path rest
  end.

Definition source_b (value : src) : bool :=
  match src_deps value with
  | [] => true
  | _ => false
  end.

Definition root_b (value : root) : bool :=
  String.eqb (root_feed value) "".

Definition item_at (sources : list src) (value : root) : option item :=
  match src_at (root_path value) sources with
  | Some source =>
      if source_b source && root_b value then Some (Item source value)
      else None
  | None => None
  end.

Fixpoint plan_at (sources : list src) (roots : list root)
    : option (list item) :=
  match roots with
  | [] => Some []
  | value :: rest =>
      match item_at sources value, plan_at sources rest with
      | Some first, Some tail => Some (first :: tail)
      | _, _ => None
      end
  end.

Definition plan (value : proj) : option (list item) :=
  if proj_b value then
    match proj_target value with
    | TOcps1 => plan_at (proj_srcs value) (proj_roots value)
    | TOctb1 => None
    end
  else None.

Theorem src_at_path : forall path values value,
  src_at path values = Some value -> src_path value = path.
Proof.
  intros path values.
  induction values as [|first rest IH]; intros value found; simpl in found.
  - discriminate.
  - destruct (String.eqb path (src_path first)) eqn:same.
    + inversion found. subst value.
      apply String.eqb_eq in same. symmetry. exact same.
    + apply IH. exact found.
Qed.

Theorem src_at_in : forall path values value,
  src_at path values = Some value -> In value values.
Proof.
  intros path values.
  induction values as [|first rest IH]; intros value found; simpl in found.
  - discriminate.
  - destruct (String.eqb path (src_path first)) eqn:same.
    + inversion found. left. reflexivity.
    + right. apply IH. exact found.
Qed.

Theorem item_at_root : forall sources value found,
  item_at sources value = Some found -> item_root found = value.
Proof.
  intros sources value found accepted.
  unfold item_at in accepted.
  destruct (src_at (root_path value) sources) as [source|] eqn:selected.
  - destruct (source_b source && root_b value) eqn:ready.
    + inversion accepted. reflexivity.
    + discriminate.
  - discriminate.
Qed.

Theorem item_at_exact : forall sources value found,
  item_at sources value = Some found ->
  src_path (item_src found) = root_path (item_root found)
  /\ In (item_src found) sources.
Proof.
  intros sources value found accepted.
  unfold item_at in accepted.
  destruct (src_at (root_path value) sources) as [source|] eqn:selected.
  - destruct (source_b source && root_b value) eqn:ready.
    + inversion accepted. split.
      * apply src_at_path in selected. exact selected.
      * apply src_at_in in selected. exact selected.
    + discriminate.
  - discriminate.
Qed.

Theorem plan_at_roots : forall sources roots items,
  plan_at sources roots = Some items -> map item_root items = roots.
Proof.
  intros sources roots.
  induction roots as [|value rest IH]; intros items accepted; simpl in accepted.
  - inversion accepted. reflexivity.
  - destruct (item_at sources value) as [first|] eqn:head.
    + destruct (plan_at sources rest) as [tail|] eqn:next.
      * inversion accepted. simpl. f_equal.
        -- apply item_at_root in head. exact head.
        -- apply IH. reflexivity.
      * discriminate.
    + discriminate.
Qed.

Theorem plan_at_exact : forall sources roots items,
  plan_at sources roots = Some items ->
  Forall
    (fun value =>
      src_path (item_src value) = root_path (item_root value)
      /\ In (item_src value) sources)
    items.
Proof.
  intros sources roots.
  induction roots as [|value rest IH]; intros items accepted; simpl in accepted.
  - inversion accepted. constructor.
  - destruct (item_at sources value) as [first|] eqn:head.
    + destruct (plan_at sources rest) as [tail|] eqn:next.
      * inversion accepted. constructor.
        -- apply item_at_exact in head. exact head.
        -- apply IH. reflexivity.
      * discriminate.
    + discriminate.
Qed.

Theorem plan_valid : forall value items,
  plan value = Some items -> proj_b value = true.
Proof.
  intros value items accepted.
  unfold plan in accepted.
  destruct (proj_b value) eqn:valid.
  - reflexivity.
  - discriminate.
Qed.

Theorem plan_target : forall value items,
  plan value = Some items -> proj_target value = TOcps1.
Proof.
  intros value items accepted.
  unfold plan in accepted.
  destruct (proj_b value); try discriminate.
  destruct (proj_target value) eqn:target; try discriminate.
  reflexivity.
Qed.

Theorem plan_roots : forall value items,
  plan value = Some items -> map item_root items = proj_roots value.
Proof.
  intros value items accepted.
  unfold plan in accepted.
  destruct (proj_b value); try discriminate.
  destruct (proj_target value); try discriminate.
  apply plan_at_roots with (sources := proj_srcs value). exact accepted.
Qed.

Theorem plan_exact : forall value items,
  plan value = Some items ->
  Forall
    (fun item =>
      src_path (item_src item) = root_path (item_root item)
      /\ In (item_src item) (proj_srcs value))
    items.
Proof.
  intros value items accepted.
  unfold plan in accepted.
  destruct (proj_b value); try discriminate.
  destruct (proj_target value); try discriminate.
  apply plan_at_exact with
    (sources := proj_srcs value) (roots := proj_roots value).
  exact accepted.
Qed.