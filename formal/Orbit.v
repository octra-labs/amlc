(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.

Require Import Uni.
Require Import Dec.
Require Import DecRel.
Require Import DecComp.
Require Import DecSound.
Require Import Surf.
Require Import Fin.
Require Import Low.
Require Import Cmp.

Import ListNotations.

Fixpoint oval (count : nat) (seed : stm) (item : sbind) (body : stm) : stm :=
  match count with
  | O => seed
  | S rest => SLet item (oval rest seed item body) body
  end.

Definition obody (item : sbind) (body : stm) : option chk :=
  match pcheck [item] body with
  | Some (typ, row, cost, next) =>
      if ty_eqb typ (sty item) then Some (typ, row, cost, next) else None
  | None => None
  end.

Definition oseed (seed : stm) (item : sbind) : stm :=
  SLet (SBind (sname item) M1 (sty item)) seed (SVar (sname item)).

Definition ofit (count : nat) (seed body : stm) : bool :=
  let node_count :=
    match count with
    | O => fin_nodes seed + 2
    | S _ => fin_nodes seed + count * (fin_nodes body + 1)
    end
  in
  let depth_count :=
    match count with
    | O => S (fin_depth seed)
    | S _ => count + Nat.max (fin_depth seed) (fin_depth body)
    end
  in
  fin_valid seed && fin_valid body && fin_fit node_count depth_count.

Definition oout (count : nat) (seed : stm) (item : sbind)
    (body : stm) : stm :=
  match count with
  | O => oseed seed item
  | S _ => oval count seed item body
  end.

Definition oterm (count : nat) (seed : stm) (item : sbind) (body : stm)
    : option stm :=
  match obody item body with
  | Some _ =>
      if ofit count seed body
      then Some (oout count seed item body)
      else None
  | None => None
  end.

Definition oguard (left right delta turn index : nat) : stm :=
  Cmp.term Cmp.Lt left right delta
    (SK (VInt (Z.of_nat index)) TInt) (SVar turn).

Fixpoint oval_to (count : nat) (left right delta turn : nat)
    (seed : stm) (item : sbind) (body : stm) : stm :=
  match count with
  | O => seed
  | S rest =>
      SLet item (oval_to rest left right delta turn seed item body)
        (SIf (oguard left right delta turn rest) body (SVar (sname item)))
  end.

Definition oout_to (count : nat) (left right delta turn : nat)
    (seed : stm) (item : sbind) (body : stm) : stm :=
  match count with
  | O => oseed seed item
  | S _ => oval_to count left right delta turn seed item body
  end.

Definition ofit_to (count : nat) (turns seed body guard : stm) : bool :=
  let step_nodes := fin_nodes guard + fin_nodes body + 3 in
  let node_count :=
    1 + fin_nodes turns +
      match count with
      | O => fin_nodes seed + 2
      | S _ => fin_nodes seed + count * step_nodes
      end
  in
  let branch_depth := 1 + Nat.max (fin_depth guard) (fin_depth body) in
  let loop_depth :=
    match count with
    | O => S (fin_depth seed)
    | S _ => count + Nat.max (fin_depth seed) branch_depth
    end
  in
  fin_valid turns && fin_valid seed && fin_valid body && fin_valid guard
    && fin_fit node_count (1 + Nat.max (fin_depth turns) loop_depth).

Definition oterm_to (left right delta turn count : nat) (turns seed : stm)
    (item : sbind) (body : stm) : option stm :=
  let guard := oguard left right delta turn 0 in
  match obody item body with
  | Some _ =>
      if ofit_to count turns seed body guard then
        Some (SLet (SBind turn MM TInt) turns
          (oout_to count left right delta turn seed item body))
      else None
  | None => None
  end.

Definition ocheck (inputs : list sbind) (count : nat) (seed : stm)
    (item : sbind) (body : stm) : option chk :=
  match oterm count seed item body with
  | Some term =>
      match pcheck inputs term with
      | Some (typ, row, cost, next) =>
          if ty_eqb typ (sty item)
          then Some (typ, row, cost, next)
          else None
      | None => None
      end
  | None => None
  end.

Theorem oval_zero : forall seed item body,
  oval 0 seed item body = seed.
Proof.
  reflexivity.
Qed.

Theorem oval_succ : forall count seed item body,
  oval (S count) seed item body = SLet item (oval count seed item body) body.
Proof.
  reflexivity.
Qed.

Theorem oval_add : forall left right seed item body,
  oval (left + right) seed item body =
    oval right (oval left seed item body) item body.
Proof.
  intros left right seed item body.
  induction right as [| right IH].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r. simpl. rewrite IH. reflexivity.
Qed.

Theorem oseed_nodes : forall seed item,
  fin_nodes (oseed seed item) = fin_nodes seed + 2.
Proof.
  intros seed item. simpl. lia.
Qed.

Theorem oseed_depth : forall seed item,
  fin_depth (oseed seed item) = S (fin_depth seed).
Proof.
  intros seed item. simpl. lia.
Qed.

Theorem oval_to_zero : forall left right delta turn seed item body,
  oval_to 0 left right delta turn seed item body = seed.
Proof.
  reflexivity.
Qed.

Theorem oval_to_succ : forall count left right delta turn seed item body,
  oval_to (S count) left right delta turn seed item body =
    SLet item (oval_to count left right delta turn seed item body)
      (SIf (oguard left right delta turn count) body (SVar (sname item))).
Proof.
  reflexivity.
Qed.

Theorem oguard_decide : forall left right,
  Cmp.decide Cmp.Lt (Z.of_nat left) right = true <->
  (Z.of_nat left < right)%Z.
Proof.
  intros left right.
  apply Cmp.decide_spec.
Qed.

Theorem onodes : forall count seed item body,
  fin_nodes (oval count seed item body) =
  fin_nodes seed + count * (fin_nodes body + 1).
Proof.
  induction count as [| count IH]; intros seed item body; simpl.
  - lia.
  - rewrite IH. nia.
Qed.

Theorem odepth : forall count seed item body,
  fin_depth (oval count seed item body) =
  match count with
  | O => fin_depth seed
  | S _ => count + Nat.max (fin_depth seed) (fin_depth body)
  end.
Proof.
  induction count as [| count IH]; intros seed item body; simpl.
  - reflexivity.
  - destruct count as [| count].
    + reflexivity.
    + rewrite IH.
      rewrite Nat.max_l by lia.
      lia.
Qed.

Theorem oout_nodes : forall count seed item body,
  fin_nodes (oout count seed item body) =
  match count with
  | O => fin_nodes seed + 2
  | S _ => fin_nodes seed + count * (fin_nodes body + 1)
  end.
Proof.
  intros count seed item body.
  destruct count as [| count].
  - apply oseed_nodes.
  - apply onodes.
Qed.

Theorem oout_depth : forall count seed item body,
  fin_depth (oout count seed item body) =
  match count with
  | O => S (fin_depth seed)
  | S _ => count + Nat.max (fin_depth seed) (fin_depth body)
  end.
Proof.
  intros count seed item body.
  destruct count as [| count].
  - apply oseed_depth.
  - apply odepth.
Qed.

Theorem oguard_nodes : forall left right delta turn index,
  fin_nodes (oguard left right delta turn index) =
  fin_nodes (oguard left right delta turn 0).
Proof.
  reflexivity.
Qed.

Theorem onodes_to : forall count left right delta turn seed item body,
  fin_nodes (oval_to count left right delta turn seed item body) =
  fin_nodes seed + count *
    (fin_nodes (oguard left right delta turn 0) + fin_nodes body + 3).
Proof.
  induction count as [| count IH]; intros left right delta turn seed item body.
  - cbn [oval_to]. lia.
  - cbn [oval_to].
    change
      (1 + fin_nodes (oval_to count left right delta turn seed item body)
        + (1 + fin_nodes (oguard left right delta turn count)
          + fin_nodes body + 1) =
       fin_nodes seed + S count *
        (fin_nodes (oguard left right delta turn 0) + fin_nodes body + 3)).
    rewrite IH, (oguard_nodes left right delta turn count).
    nia.
Qed.

Theorem oguard_depth : forall left right delta turn index,
  fin_depth (oguard left right delta turn index) =
  fin_depth (oguard left right delta turn 0).
Proof.
  reflexivity.
Qed.

Theorem odepth_to : forall count left right delta turn seed item body,
  fin_depth (oval_to count left right delta turn seed item body) =
  match count with
  | O => fin_depth seed
  | S _ => count + Nat.max (fin_depth seed)
      (1 + Nat.max (fin_depth (oguard left right delta turn 0))
        (fin_depth body))
  end.
Proof.
  induction count as [| count IH]; intros left right delta turn seed item body.
  - reflexivity.
  - destruct count as [| count].
    + change
        (1 + Nat.max
          (fin_depth (oval_to 0 left right delta turn seed item body))
          (1 + Nat.max (fin_depth (oguard left right delta turn 0))
            (Nat.max (fin_depth body) 0)) =
         1 + Nat.max (fin_depth seed)
          (1 + Nat.max (fin_depth (oguard left right delta turn 0))
            (fin_depth body))).
      rewrite IH, Nat.max_0_r. reflexivity.
    + change
        (1 + Nat.max
          (fin_depth (oval_to (S count) left right delta turn seed item body))
          (1 + Nat.max (fin_depth (oguard left right delta turn (S count)))
            (Nat.max (fin_depth body) 0)) =
         S (S count) + Nat.max (fin_depth seed)
          (1 + Nat.max (fin_depth (oguard left right delta turn 0))
            (fin_depth body))).
      rewrite IH, Nat.max_0_r,
        (oguard_depth left right delta turn (S count)).
      rewrite Nat.max_l by lia.
      lia.
Qed.

Theorem oout_to_nodes : forall count left right delta turn seed item body,
  fin_nodes (oout_to count left right delta turn seed item body) =
  match count with
  | O => fin_nodes seed + 2
  | S _ => fin_nodes seed + count *
      (fin_nodes (oguard left right delta turn 0) + fin_nodes body + 3)
  end.
Proof.
  intros count left right delta turn seed item body.
  destruct count as [| count].
  - apply oseed_nodes.
  - apply onodes_to.
Qed.

Theorem oout_to_depth : forall count left right delta turn seed item body,
  fin_depth (oout_to count left right delta turn seed item body) =
  match count with
  | O => S (fin_depth seed)
  | S _ => count + Nat.max (fin_depth seed)
      (1 + Nat.max (fin_depth (oguard left right delta turn 0))
        (fin_depth body))
  end.
Proof.
  intros count left right delta turn seed item body.
  destruct count as [| count].
  - apply oseed_depth.
  - apply odepth_to.
Qed.

Theorem ofit_to_valid : forall count left right delta turn turns seed item body,
  ofit_to count turns seed body (oguard left right delta turn 0) = true ->
  fin_valid (SLet (SBind turn MM TInt) turns
    (oout_to count left right delta turn seed item body)) = true.
Proof.
  intros count left right delta turn turns seed item body accepted.
  unfold ofit_to in accepted.
  repeat rewrite andb_true_iff in accepted.
  destruct accepted as [[[[_ _] _] _] fit_ok].
  unfold fin_valid.
  simpl.
  rewrite oout_to_nodes, oout_to_depth.
  apply fin_fit_spec in fit_ok.
  apply fin_fit_spec.
  destruct fit_ok.
  split; lia.
Qed.

Theorem oterm_to_valid : forall left right delta turn count turns seed item body
    term,
  oterm_to left right delta turn count turns seed item body = Some term ->
  fin_valid term = true.
Proof.
  intros left right delta turn count turns seed item body term built.
  unfold oterm_to in built.
  destruct (obody item body); try discriminate.
  destruct (ofit_to count turns seed body
    (oguard left right delta turn 0)) eqn:fit_ok; try discriminate.
  inversion built; subst.
  eapply ofit_to_valid.
  exact fit_ok.
Qed.

Theorem ofit_valid : forall count seed item body,
  ofit count seed body = true ->
  fin_valid (oout count seed item body) = true.
Proof.
  intros count seed item body accepted.
  unfold ofit in accepted.
  apply andb_true_iff in accepted as [_ fit_ok].
  unfold fin_valid.
  rewrite oout_nodes, oout_depth.
  exact fit_ok.
Qed.

Theorem oterm_valid : forall count seed item body term,
  oterm count seed item body = Some term ->
  fin_valid term = true.
Proof.
  intros count seed item body term built.
  unfold oterm in built.
  destruct (obody item body); try discriminate.
  destruct (ofit count seed body) eqn:fit_ok; try discriminate.
  inversion built; subst.
  apply ofit_valid.
  exact fit_ok.
Qed.

Theorem obody_type : forall item body typ row cost next,
  obody item body = Some (typ, row, cost, next) ->
  typ = sty item.
Proof.
  intros item body typ row cost next accepted.
  unfold obody in accepted.
  destruct (pcheck [item] body) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (sty item)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  reflexivity.
Qed.

Theorem obody_sound : forall item body row cost next,
  obody item body = Some (sty item, row, cost, next) ->
  pcheck [item] body = Some (sty item, row, cost, next).
Proof.
  intros item body row cost next accepted.
  unfold obody in accepted.
  destruct (pcheck [item] body) as [[[[typ brow] bcost] bnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb typ (sty item)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  subst.
  inversion accepted; subst.
  assumption.
Qed.

Theorem obody_complete : forall item body row cost next,
  pcheck [item] body = Some (sty item, row, cost, next) ->
  obody item body = Some (sty item, row, cost, next).
Proof.
  intros item body row cost next checked.
  unfold obody.
  rewrite checked, ty_eqb_refl.
  reflexivity.
Qed.

Theorem oterm_exact : forall count seed item body row cost next,
  obody item body = Some (sty item, row, cost, next) ->
  ofit count seed body = true ->
  oterm count seed item body = Some (oout count seed item body).
Proof.
  intros count seed item body row cost next body_ok fit_ok.
  unfold oterm.
  rewrite body_ok, fit_ok.
  reflexivity.
Qed.

Theorem oterm_zero : forall seed item body row cost next,
  obody item body = Some (sty item, row, cost, next) ->
  ofit 0 seed body = true ->
  oterm 0 seed item body = Some (oseed seed item).
Proof.
  intros seed item body row cost next body_ok fit_ok.
  rewrite (oterm_exact 0 seed item body row cost next body_ok fit_ok).
  reflexivity.
Qed.

Theorem oterm_succ : forall count seed item body row cost next,
  obody item body = Some (sty item, row, cost, next) ->
  ofit (S count) seed body = true ->
  oterm (S count) seed item body =
    Some (SLet item (oval count seed item body) body).
Proof.
  intros count seed item body row cost next body_ok fit_ok.
  rewrite (oterm_exact (S count) seed item body row cost next body_ok fit_ok).
  reflexivity.
Qed.

Theorem ocheck_type : forall inputs count seed item body typ row cost next,
  ocheck inputs count seed item body = Some (typ, row, cost, next) ->
  typ = sty item.
Proof.
  intros inputs count seed item body typ row cost next accepted.
  unfold ocheck in accepted.
  destruct (oterm count seed item body) as [term |]; try discriminate.
  destruct (pcheck inputs term) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (sty item)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  reflexivity.
Qed.

Theorem ocheck_sound : forall inputs count seed item body typ row cost next,
  ocheck inputs count seed item body = Some (typ, row, cost, next) ->
  exists brow bcost bnext term,
    obody item body = Some (sty item, brow, bcost, bnext) /\
    ofit count seed body = true /\
    oterm count seed item body = Some term /\
    pcheck inputs term = Some (sty item, row, cost, next) /\
    typ = sty item.
Proof.
  intros inputs count seed item body typ row cost next accepted.
  unfold ocheck in accepted.
  destruct (oterm count seed item body) as [term |] eqn:built;
    try discriminate.
  unfold oterm in built.
  destruct (obody item body) as [[[[btyp brow] bcost] bnext] |]
    eqn:body_ok; try discriminate.
  destruct (ofit count seed body) eqn:fit_ok; try discriminate.
  destruct (pcheck inputs term) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (sty item)) eqn:same; try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  inversion built; subst.
  pose proof (obody_type item body btyp brow bcost bnext body_ok)
    as body_type.
  subst btyp.
  exists brow, bcost, bnext, (oout count seed item body).
  repeat split; assumption.
Qed.

Theorem ocheck_complete : forall inputs count seed item body row cost next
    brow bcost bnext term,
  obody item body = Some (sty item, brow, bcost, bnext) ->
  oterm count seed item body = Some term ->
  pcheck inputs term = Some (sty item, row, cost, next) ->
  ocheck inputs count seed item body =
    Some (sty item, row, cost, next).
Proof.
  intros inputs count seed item body row cost next brow bcost bnext term
    body_ok built checked.
  unfold ocheck.
  rewrite built, checked, ty_eqb_refl.
  reflexivity.
Qed.