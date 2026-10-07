(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import Arith Bool List Lia.
Import ListNotations.

Inductive code :=
  | Done
  | Bind (name : nat) (rest : code)
  | Write (name : nat) (rest : code)
  | Block (body rest : code)
  | Loop (name : nat) (body rest : code).

Definition erase name names := filter (fun value => negb (Nat.eqb name value)) names.

Fixpoint check names body :=
  match body with
  | Done => true
  | Bind name rest => check (erase name names) rest
  | Write name rest => negb (existsb (Nat.eqb name) names) && check names rest
  | Block body rest => check names body && check names rest
  | Loop name body rest => check (name :: names) body && check names rest
  end.

Fixpoint lookup name (env : list (nat * nat)) :=
  match env with
  | [] => None
  | (key, cell) :: rest => if Nat.eqb name key then Some cell else lookup name rest
  end.

Fixpoint writes env fresh body :=
  match body with
  | Done => []
  | Bind name rest => fresh :: writes ((name, fresh) :: env) (S fresh) rest
  | Write name rest =>
    match lookup name env with
    | None => writes env fresh rest
    | Some cell => cell :: writes env fresh rest
    end
  | Block body rest => writes env fresh body ++ writes env fresh rest
  | Loop name body rest =>
    fresh :: writes ((name, fresh) :: env) (S fresh) body ++ writes env fresh rest
  end.

Definition tracks env names cell :=
  forall name, lookup name env = Some cell -> In name names.

Lemma erase_tracks : forall env names cell name fresh,
  tracks env names cell -> cell < fresh ->
  tracks ((name, fresh) :: env) (erase name names) cell.
Proof.
  intros env names cell name fresh has smaller key found.
  simpl in found. destruct (key =? name) eqn:same.
  - inversion found. lia.
  - unfold erase. apply filter_In. split.
    + apply has. exact found.
    + apply negb_true_iff. apply Nat.eqb_neq.
      apply Nat.eqb_neq in same. congruence.
Qed.

Lemma loop_tracks : forall env names cell name fresh,
  tracks env names cell -> cell < fresh ->
  tracks ((name, fresh) :: env) (name :: names) cell.
Proof.
  intros env names cell name fresh has smaller key found.
  simpl in found. destruct (key =? name) eqn:same.
  - inversion found. lia.
  - right. apply has. exact found.
Qed.

Theorem checked_writes : forall body env fresh names cell,
  check names body = true -> tracks env names cell -> cell < fresh ->
  ~ In cell (writes env fresh body).
Proof.
  induction body; intros env fresh names cell valid has smaller; simpl in *.
  - tauto.
  - intros [same | member]. lia.
    apply (IHbody ((name, fresh) :: env) (S fresh) (erase name names) cell valid).
    + apply erase_tracks; auto.
    + lia.
    + exact member.
  - apply andb_true_iff in valid as [absent valid].
    destruct (lookup name env) as [value |] eqn:found.
    + intros [same | member].
      * subst value. apply has in found.
        apply negb_true_iff in absent.
        assert (existsb (Nat.eqb name) names = true) as present.
        { apply existsb_exists. exists name. split; auto. apply Nat.eqb_refl. }
        congruence.
      * eapply IHbody; eauto.
    + eapply IHbody; eauto.
  - apply andb_true_iff in valid as [left right].
    rewrite in_app_iff. intros [member | member].
    + eapply IHbody1; eauto.
    + eapply IHbody2; eauto.
  - apply andb_true_iff in valid as [left right].
    intros [same | member]. lia.
    apply in_app_iff in member as [member | member].
    + apply (IHbody1 ((name, fresh) :: env) (S fresh) (name :: names) cell left).
      * apply loop_tracks; auto.
      * lia.
      * exact member.
    + eapply IHbody2; eauto.
Qed.

Lemma lookup_old : forall env fresh name cell,
  Forall (fun item => snd item < fresh) env -> lookup name env = Some cell -> cell < fresh.
Proof.
  induction env as [| [key value] rest ih]; intros fresh name cell old found; simpl in found.
  - discriminate.
  - inversion old; subst. destruct (name =? key).
    + inversion found; subst. assumption.
    + eapply ih; eauto.
Qed.

Theorem loop_index : forall body env fresh name names,
  Forall (fun item => snd item < fresh) env ->
  check (name :: names) body = true ->
  ~ In fresh (writes ((name, fresh) :: env) (S fresh) body).
Proof.
  intros body env fresh name names old valid.
  eapply checked_writes; eauto; try lia.
  intros key found. simpl in found. destruct (key =? name) eqn:same.
  - apply Nat.eqb_eq in same. subst. left. reflexivity.
  - pose proof (lookup_old env fresh key fresh old found). lia.
Qed.

Fixpoint apply_writes (events : list (nat * nat)) (memory : nat -> nat) :=
  match events with
  | [] => memory
  | (cell, value) :: rest =>
    apply_writes rest (fun key => if Nat.eqb key cell then value else memory key)
  end.

Theorem memory_preserved : forall events memory cell,
  ~ In cell (map fst events) -> apply_writes events memory cell = memory cell.
Proof.
  induction events as [| [key value] rest ih]; intros memory cell untouched; simpl in *.
  - reflexivity.
  - rewrite ih by tauto. destruct (cell =? key) eqn:same; auto.
    apply Nat.eqb_eq in same. exfalso. apply untouched. left. congruence.
Qed.

Theorem checked_memory : forall body env fresh names cell events memory,
  check names body = true -> tracks env names cell -> cell < fresh ->
  (forall key, In key (map fst events) -> In key (writes env fresh body)) ->
  apply_writes events memory cell = memory cell.
Proof.
  intros body env fresh names cell events memory valid has smaller included.
  apply memory_preserved. intro member.
  eapply checked_writes; eauto.
Qed.