(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Require Import Uni.
Require Import Lim.

Import ListNotations.

Inductive ix : Type :=
| ILit : nat -> ix
| IVar : nat -> ix
| IAdd : ix -> ix -> ix
| IMul : ix -> ix -> ix
| IMax : ix -> ix -> ix
| ISub : ix -> ix -> ix.

Definition ienv := list (nat * nat).

Definition idepth_max : nat := 4096.
Definition inodes_max : nat := 100000.
Definition ivars_max : nat := 4096.

Definition ifit (value : nat) : bool := Nat.leb value lim.

Fixpoint ifind (name : nat) (env : ienv) : option nat :=
  match env with
  | [] => None
  | (key, value) :: rest =>
      if Nat.eqb name key then Some value else ifind name rest
  end.

Fixpoint ihas (name : nat) (env : ienv) : bool :=
  match env with
  | [] => false
  | (key, _) :: rest => Nat.eqb name key || ihas name rest
  end.

Fixpoint ienv_u (env : ienv) : bool :=
  match env with
  | [] => true
  | (name, _) :: rest => negb (ihas name rest) && ienv_u rest
  end.

Fixpoint ienv_v (env : ienv) : bool :=
  match env with
  | [] => true
  | (_, value) :: rest => ifit value && ienv_v rest
  end.

Definition ienv_b (env : ienv) : bool :=
  Nat.leb (length env) ivars_max && ienv_u env && ienv_v env.

Fixpoint idepth (term : ix) : nat :=
  match term with
  | ILit _ | IVar _ => 0
  | IAdd lhs rhs => S (Nat.max (idepth lhs) (idepth rhs))
  | IMul lhs rhs => S (Nat.max (idepth lhs) (idepth rhs))
  | IMax lhs rhs => S (Nat.max (idepth lhs) (idepth rhs))
  | ISub lhs rhs => S (Nat.max (idepth lhs) (idepth rhs))
  end.

Fixpoint inodes (term : ix) : nat :=
  match term with
  | ILit _ | IVar _ => 1
  | IAdd lhs rhs => S (inodes lhs + inodes rhs)
  | IMul lhs rhs => S (inodes lhs + inodes rhs)
  | IMax lhs rhs => S (inodes lhs + inodes rhs)
  | ISub lhs rhs => S (inodes lhs + inodes rhs)
  end.

Definition ix_b (term : ix) : bool :=
  Nat.leb (idepth term) idepth_max && Nat.leb (inodes term) inodes_max.

Fixpoint iev (env : ienv) (term : ix) : option nat :=
  match term with
  | ILit value => if ifit value then Some value else None
  | IVar name =>
      match ifind name env with
      | Some value => if ifit value then Some value else None
      | None => None
      end
  | IAdd lhs rhs =>
      match iev env lhs, iev env rhs with
      | Some lhs, Some rhs =>
          let value := lhs + rhs in
          if ifit value then Some value else None
      | _, _ => None
      end
  | IMul lhs rhs =>
      match iev env lhs, iev env rhs with
      | Some lhs, Some rhs =>
          let value := lhs * rhs in
          if ifit value then Some value else None
      | _, _ => None
      end
  | IMax lhs rhs =>
      match iev env lhs, iev env rhs with
      | Some lhs, Some rhs =>
          let value := Nat.max lhs rhs in
          if ifit value then Some value else None
      | _, _ => None
      end
  | ISub lhs rhs =>
      match iev env lhs, iev env rhs with
      | Some lhs, Some rhs =>
          let value := lhs - rhs in
          if ifit value then Some value else None
      | _, _ => None
      end
  end.

Definition ieval (env : ienv) (term : ix) : option nat :=
  if ienv_b env then
    if ix_b term then iev env term else None
  else None.

Definition iput (env : ienv) (name : nat) (term : ix) : option ienv :=
  if ienv_b env then
    if negb (ihas name env) then
      if Nat.ltb (length env) ivars_max then
        match ieval env term with
        | Some value => Some ((name, value) :: env)
        | None => None
        end
      else None
    else None
  else None.

Inductive ievR (env : ienv) : ix -> nat -> Prop :=
| ERLit : forall value,
    ifit value = true ->
    ievR env (ILit value) value
| ERVar : forall name value,
    ifind name env = Some value ->
    ifit value = true ->
    ievR env (IVar name) value
| ERAdd : forall left right lhs rhs,
    ievR env left lhs ->
    ievR env right rhs ->
    ifit (lhs + rhs) = true ->
    ievR env (IAdd left right) (lhs + rhs)
| ERMul : forall left right lhs rhs,
    ievR env left lhs ->
    ievR env right rhs ->
    ifit (lhs * rhs) = true ->
    ievR env (IMul left right) (lhs * rhs)
| ERMax : forall left right lhs rhs,
    ievR env left lhs ->
    ievR env right rhs ->
    ifit (Nat.max lhs rhs) = true ->
    ievR env (IMax left right) (Nat.max lhs rhs)
| ERSub : forall left right lhs rhs,
    ievR env left lhs ->
    ievR env right rhs ->
    ifit (lhs - rhs) = true ->
    ievR env (ISub left right) (lhs - rhs).

Theorem iev_sound : forall env term value,
  iev env term = Some value -> ievR env term value.
Proof.
  intros env term.
  induction term as [value | name | left IHl right IHr
    | left IHl right IHr | left IHl right IHr | left IHl right IHr];
    intros out H; simpl in H.
  - destruct (ifit value) eqn:Hfit; inversion H; subst.
    constructor. exact Hfit.
  - destruct (ifind name env) as [value |] eqn:Hfind; try discriminate.
    destruct (ifit value) eqn:Hfit; inversion H; subst.
    econstructor; eauto.
  - destruct (iev env left) as [lhs |] eqn:Hl; try discriminate.
    destruct (iev env right) as [rhs |] eqn:Hr; try discriminate.
    destruct (ifit (lhs + rhs)) eqn:Hfit; inversion H; subst.
    econstructor; eauto.
  - destruct (iev env left) as [lhs |] eqn:Hl; try discriminate.
    destruct (iev env right) as [rhs |] eqn:Hr; try discriminate.
    destruct (ifit (lhs * rhs)) eqn:Hfit; inversion H; subst.
    econstructor; eauto.
  - destruct (iev env left) as [lhs |] eqn:Hl; try discriminate.
    destruct (iev env right) as [rhs |] eqn:Hr; try discriminate.
    destruct (ifit (Nat.max lhs rhs)) eqn:Hfit; inversion H; subst.
    econstructor; eauto.
  - destruct (iev env left) as [lhs |] eqn:Hl; try discriminate.
    destruct (iev env right) as [rhs |] eqn:Hr; try discriminate.
    destruct (ifit (lhs - rhs)) eqn:Hfit; inversion H; subst.
    econstructor; eauto.
Qed.

Theorem iev_complete : forall env term value,
  ievR env term value -> iev env term = Some value.
Proof.
  intros env term value H.
  induction H; simpl.
  - rewrite H. reflexivity.
  - rewrite H, H0. reflexivity.
  - rewrite IHievR1, IHievR2, H1. reflexivity.
  - rewrite IHievR1, IHievR2, H1. reflexivity.
  - rewrite IHievR1, IHievR2, H1. reflexivity.
  - rewrite IHievR1, IHievR2, H1. reflexivity.
Qed.

Theorem iev_unique : forall env term left right,
  ievR env term left -> ievR env term right -> left = right.
Proof.
  intros env term left right Hl Hr.
  pose proof (iev_complete _ _ _ Hl) as El.
  pose proof (iev_complete _ _ _ Hr) as Er.
  rewrite El in Er. inversion Er. reflexivity.
Qed.

Theorem iev_fit : forall env term value,
  ievR env term value -> ifit value = true.
Proof.
  intros env term value run.
  inversion run; assumption.
Qed.

Theorem ieval_sound : forall env term value,
  ieval env term = Some value ->
  ienv_b env = true /\ ix_b term = true /\ ievR env term value.
Proof.
  intros env term value H.
  unfold ieval in H.
  destruct (ienv_b env) eqn:Henv; try discriminate.
  destruct (ix_b term) eqn:Hterm; try discriminate.
  repeat split; try assumption.
  eapply iev_sound. exact H.
Qed.

Theorem ieval_complete : forall env term value,
  ienv_b env = true ->
  ix_b term = true ->
  ievR env term value ->
  ieval env term = Some value.
Proof.
  intros env term value Henv Hterm Hrun.
  unfold ieval. rewrite Henv, Hterm.
  apply iev_complete. exact Hrun.
Qed.

Theorem iput_sound : forall env name term out,
  iput env name term = Some out ->
  exists value,
    ieval env term = Some value /\
    out = (name, value) :: env /\
    ienv_b out = true.
Proof.
  intros env name term out accepted.
  unfold iput in accepted.
  destruct (ienv_b env) eqn:env_ok; try discriminate.
  destruct (negb (ihas name env)) eqn:fresh; try discriminate.
  destruct (Nat.ltb (length env) ivars_max) eqn:room; try discriminate.
  destruct (ieval env term) as [value |] eqn:run; try discriminate.
  inversion accepted; subst out.
  exists value.
  repeat split; try assumption.
  apply ieval_sound in run as [_ [_ related]].
  pose proof (iev_fit env term value related) as value_ok.
  unfold ienv_b in env_ok.
  apply andb_true_iff in env_ok as [head values_ok].
  apply andb_true_iff in head as [_ unique_ok].
  unfold ienv_b.
  apply andb_true_iff.
  split.
  - apply andb_true_iff.
    split.
    + simpl.
      apply Nat.leb_le.
      apply Nat.ltb_lt in room.
      unfold ivars_max in room.
      lia.
    + simpl.
      rewrite fresh, unique_ok.
      reflexivity.
  - simpl.
    rewrite value_ok, values_ok.
    reflexivity.
Qed.

Theorem iput_complete : forall env name term value,
  ienv_b env = true ->
  ihas name env = false ->
  Nat.ltb (length env) ivars_max = true ->
  ieval env term = Some value ->
  iput env name term = Some ((name, value) :: env).
Proof.
  intros env name term value env_ok fresh room run.
  unfold iput.
  rewrite env_ok, fresh, room, run.
  reflexivity.
Qed.

Inductive ity : Type :=
| YUnit : ity
| YBool : ity
| YInt : ity
| YVar : nat -> ity
| YBytes : ix -> ity
| YVec : ix -> ity -> ity
| YCap : nat -> ity
| YPair : ity -> ity -> ity
| YSum : ity -> ity -> ity.

Fixpoint ydepth (typ : ity) : nat :=
  match typ with
  | YUnit | YBool | YInt | YVar _ | YBytes _ | YCap _ => 0
  | YVec _ elem => S (ydepth elem)
  | YPair lhs rhs | YSum lhs rhs => S (Nat.max (ydepth lhs) (ydepth rhs))
  end.

Fixpoint ynodes (typ : ity) : nat :=
  match typ with
  | YUnit | YBool | YInt | YVar _ | YBytes _ | YCap _ => 1
  | YVec _ elem => S (ynodes elem)
  | YPair lhs rhs | YSum lhs rhs => S (ynodes lhs + ynodes rhs)
  end.

Definition ydepth_max : nat := 256.
Definition ynodes_max : nat := 4096.

Definition ity_b (typ : ity) : bool :=
  Nat.leb (ydepth typ) ydepth_max && Nat.leb (ynodes typ) ynodes_max.

Fixpoint ytype (env : ienv) (typ : ity) : option ty :=
  match typ with
  | YUnit => Some TUnit
  | YBool => Some TBool
  | YInt => Some TInt
  | YVar _ => None
  | YBytes index =>
      match ieval env index with
      | Some len => Some (TBytes len)
      | None => None
      end
  | YVec index elem =>
      match ieval env index, ytype env elem with
      | Some len, Some out => Some (TVec len out)
      | _, _ => None
      end
  | YCap kind => if ifit kind then Some (TCap kind) else None
  | YPair lhs rhs =>
      match ytype env lhs, ytype env rhs with
      | Some lout, Some rout => Some (TPair lout rout)
      | _, _ => None
      end
  | YSum lhs rhs =>
      match ytype env lhs, ytype env rhs with
      | Some lout, Some rout => Some (TSum lout rout)
      | _, _ => None
      end
  end.

Definition yelab (env : ienv) (typ : ity) : option ty :=
  if ity_b typ then ytype env typ else None.

Inductive ityR (env : ienv) : ity -> ty -> Prop :=
| RYUnit : ityR env YUnit TUnit
| RYBool : ityR env YBool TBool
| RYInt : ityR env YInt TInt
| RYBytes : forall index len,
    ienv_b env = true ->
    ix_b index = true ->
    ievR env index len ->
    ityR env (YBytes index) (TBytes len)
| RYVec : forall index elem len out,
    ienv_b env = true ->
    ix_b index = true ->
    ievR env index len ->
    ityR env elem out ->
    ityR env (YVec index elem) (TVec len out)
| RYCap : forall kind,
    ifit kind = true ->
    ityR env (YCap kind) (TCap kind)
| RYPair : forall lhs rhs left right,
    ityR env lhs left ->
    ityR env rhs right ->
    ityR env (YPair lhs rhs) (TPair left right)
| RYSum : forall lhs rhs left right,
    ityR env lhs left ->
    ityR env rhs right ->
    ityR env (YSum lhs rhs) (TSum left right).

Theorem ytype_sound : forall env typ out,
  ytype env typ = Some out -> ityR env typ out.
Proof.
  intros env typ.
  induction typ as [| | | name | index | index elem IHelem | kind
    | lhs IHl rhs IHr | lhs IHl rhs IHr]; intros out H; simpl in H.
  - inversion H. constructor.
  - inversion H. constructor.
  - inversion H. constructor.
  - discriminate.
  - destruct (ieval env index) as [len |] eqn:Hindex; try discriminate.
    inversion H; subst. apply ieval_sound in Hindex as [Henv [Hshape Hrun]].
    econstructor; eauto.
  - destruct (ieval env index) as [len |] eqn:Hindex; try discriminate.
    destruct (ytype env elem) as [item |] eqn:Helem; try discriminate.
    inversion H; subst. apply ieval_sound in Hindex as [Henv [Hshape Hrun]].
    econstructor; eauto.
  - destruct (ifit kind) eqn:Hfit; inversion H; subst.
    constructor. exact Hfit.
  - destruct (ytype env lhs) as [lout |] eqn:Hl; try discriminate.
    destruct (ytype env rhs) as [rout |] eqn:Hr; try discriminate.
    inversion H; subst. constructor; eauto.
  - destruct (ytype env lhs) as [lout |] eqn:Hl; try discriminate.
    destruct (ytype env rhs) as [rout |] eqn:Hr; try discriminate.
    inversion H; subst. constructor; eauto.
Qed.

Theorem ytype_complete : forall env typ out,
  ityR env typ out -> ytype env typ = Some out.
Proof.
  intros env typ out H.
  induction H; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (ieval_complete _ _ _ H H0 H1). reflexivity.
  - rewrite (ieval_complete _ _ _ H H0 H1), IHityR. reflexivity.
  - rewrite H. reflexivity.
  - rewrite IHityR1, IHityR2. reflexivity.
  - rewrite IHityR1, IHityR2. reflexivity.
Qed.

Theorem yelab_sound : forall env typ out,
  yelab env typ = Some out ->
  ity_b typ = true /\ ityR env typ out.
Proof.
  intros env typ out H. unfold yelab in H.
  destruct (ity_b typ) eqn:Hshape; try discriminate.
  split. reflexivity.
  apply ytype_sound. exact H.
Qed.

Theorem yelab_complete : forall env typ out,
  ity_b typ = true ->
  ityR env typ out ->
  yelab env typ = Some out.
Proof.
  intros env typ out Hshape H.
  unfold yelab. rewrite Hshape.
  apply ytype_complete. exact H.
Qed.

Definition isame (env : ienv) (left right : ix) : option bool :=
  match ieval env left, ieval env right with
  | Some lhs, Some rhs => Some (Nat.eqb lhs rhs)
  | _, _ => None
  end.

Definition ile (env : ienv) (left right : ix) : option bool :=
  match ieval env left, ieval env right with
  | Some lhs, Some rhs => Some (Nat.leb lhs rhs)
  | _, _ => None
  end.

Inductive irel : Type :=
| IEq
| ILe.

Definition ihold (env : ienv) (rel : irel) (left right : ix) : option bool :=
  match rel with
  | IEq => isame env left right
  | ILe => ile env left right
  end.

Theorem isame_true : forall env left right,
  isame env left right = Some true <->
  exists value,
    ieval env left = Some value /\ ieval env right = Some value.
Proof.
  intros env left right. split.
  - intros H. unfold isame in H.
    destruct (ieval env left) as [lhs |] eqn:Hl; try discriminate.
    destruct (ieval env right) as [rhs |] eqn:Hr; try discriminate.
    inversion H. apply Nat.eqb_eq in H1. subst.
    exists rhs. auto.
  - intros [value [Hl Hr]]. unfold isame. rewrite Hl, Hr.
    rewrite Nat.eqb_refl. reflexivity.
Qed.

Theorem ile_true : forall env left right,
  ile env left right = Some true <->
  exists lhs rhs,
    ieval env left = Some lhs /\
    ieval env right = Some rhs /\
    lhs <= rhs.
Proof.
  intros env left right. split.
  - intros H. unfold ile in H.
    destruct (ieval env left) as [lhs |] eqn:Hl; try discriminate.
    destruct (ieval env right) as [rhs |] eqn:Hr; try discriminate.
    inversion H. apply Nat.leb_le in H1.
    exists lhs, rhs. auto.
  - intros [lhs [rhs [Hl [Hr Hle]]]]. unfold ile. rewrite Hl, Hr.
    apply Nat.leb_le in Hle. rewrite Hle. reflexivity.
Qed.

Theorem isame_dec : forall env left right lhs rhs,
  ieval env left = Some lhs ->
  ieval env right = Some rhs ->
  exists answer, isame env left right = Some answer.
Proof.
  intros env left right lhs rhs Hl Hr.
  unfold isame. rewrite Hl, Hr.
  destruct (Nat.eqb lhs rhs); eauto.
Qed.

Theorem ile_dec : forall env left right lhs rhs,
  ieval env left = Some lhs ->
  ieval env right = Some rhs ->
  exists answer, ile env left right = Some answer.
Proof.
  intros env left right lhs rhs Hl Hr.
  unfold ile. rewrite Hl, Hr.
  destruct (Nat.leb lhs rhs); eauto.
Qed.

Theorem ihold_true : forall env rel left right,
  ihold env rel left right = Some true <->
  match rel with
  | IEq => exists value,
      ieval env left = Some value /\ ieval env right = Some value
  | ILe => exists lhs rhs,
      ieval env left = Some lhs /\
      ieval env right = Some rhs /\
      lhs <= rhs
  end.
Proof.
  intros env rel left right.
  destruct rel; simpl.
  - apply isame_true.
  - apply ile_true.
Qed.

Theorem ihold_dec : forall env rel left right lhs rhs,
  ieval env left = Some lhs ->
  ieval env right = Some rhs ->
  exists answer, ihold env rel left right = Some answer.
Proof.
  intros env rel left right lhs rhs Hl Hr.
  destruct rel; simpl.
  - eapply isame_dec; eauto.
  - eapply ile_dec; eauto.
Qed.