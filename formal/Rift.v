(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Require Import Uni.
Require Import Dec.
Require Import DecRel.
Require Import DecComp.
Require Import DecSound.
Require Import Lim.
Require Import Surf.
Require Import Fin.
Require Import Low.
Require Import Data.

Import ListNotations.

Record rstep : Type := RStep {
  rhead : nat;
  rtail : nat
}.

Record rpath : Type := RPath {
  rsource : nat;
  rsteps : list rstep
}.

Fixpoint rvec (elem : ty) (items : list nat) : stm :=
  match items with
  | [] => SVnil elem
  | item :: rest => SVcons (SVar item) (rvec elem rest)
  end.

Fixpoint rbody (steps : list rstep) (rest : nat) (elem : ty)
    (held : list nat) (source : nat) : stm :=
  match steps with
  | [] => SPair (rvec elem (rev held)) (SVar source)
  | step :: more =>
      let tail_ty := TVec (length more + rest) elem in
      SUnpair (SUncons (SVar source))
        (SBind (rhead step) (paym elem) elem)
        (SBind (rtail step) (paym tail_ty) tail_ty)
        (rbody more rest elem (rhead step :: held) (rtail step))
  end.

Fixpoint rids (steps : list rstep) : list nat :=
  match steps with
  | [] => []
  | step :: rest => rhead step :: rtail step :: rids rest
  end.

Fixpoint runiq (items : list nat) : bool :=
  match items with
  | [] => true
  | item :: rest => negb (existsb (Nat.eqb item) rest) && runiq rest
  end.

Definition rpath_b (cut : nat) (source : stm) (path : rpath) : bool :=
  let ids := rsource path :: rids (rsteps path) in
  Nat.eqb (length (rsteps path)) cut && runiq ids
    && forallb (fun name => negb (has name source)) ids.

Fixpoint rslots (fuel left index : nat) (source : stm) : option (list nat) :=
  match left, fuel with
  | O, _ => Some []
  | S _, O => None
  | S need, S more =>
      let name := did index in
      if has name source then rslots more (S need) (S index) source
      else
        match rslots more need (S index) source with
        | Some rest => Some (name :: rest)
        | None => None
        end
  end.

Fixpoint rpairs (items : list nat) : option (list rstep) :=
  match items with
  | [] => Some []
  | head :: tail :: rest =>
      match rpairs rest with
      | Some steps => Some (RStep head tail :: steps)
      | None => None
      end
  | _ => None
  end.

Definition rmake_path (cut : nat) (source : stm) : option rpath :=
  match rslots Low.pmax (S (cut + cut)) 0 source with
  | Some (first :: rest) =>
      match rpairs rest with
      | Some steps => Some (RPath first steps)
      | None => None
      end
  | _ => None
  end.

Definition rfit (cut : nat) (source : stm) : bool :=
  let body_depth :=
    match cut with
    | O => 1
    | S _ => cut + 2
    end
  in
  fin_valid source
    && fin_fit (fin_nodes source + 4 + 4 * cut)
      (S (Nat.max (fin_depth source) body_depth)).

Definition rout (path : rpath) (rest : nat) (elem : ty)
    (source : stm) : stm :=
  let source_ty := TVec (length (rsteps path) + rest) elem in
  SLet (SBind (rsource path) (paym source_ty) source_ty) source
    (rbody (rsteps path) rest elem [] (rsource path)).

Definition rterm (path : rpath) (cut rest : nat) (elem : ty)
    (source : stm) : option stm :=
  if fit (cut + rest) && ty_b elem && rfit cut source
      && rpath_b cut source path
  then Some (rout path rest elem source)
  else None.

Definition rift_make (cut rest : nat) (elem : ty) (source : stm) : option stm :=
  match rmake_path cut source with
  | Some path => rterm path cut rest elem source
  | None => None
  end.

Definition rift_check (inputs : list sbind) (path : rpath)
    (cut rest : nat) (elem : ty) (source : stm) : option chk :=
  match rterm path cut rest elem source with
  | Some term =>
      match pcheck inputs term with
      | Some (typ, row, cost, next) =>
          let expected := TPair (TVec cut elem) (TVec rest elem) in
          if ty_eqb typ expected then Some (typ, row, cost, next) else None
      | None => None
      end
  | None => None
  end.

Theorem rvec_nodes : forall elem items,
  fin_nodes (rvec elem items) = S (length items).
Proof.
  intros elem items.
  induction items as [|item rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Theorem rvec_depth : forall elem items,
  fin_depth (rvec elem items) =
    match items with
    | [] => 0
    | _ => 1
    end.
Proof.
  intros elem items.
  induction items as [|item rest IH]; simpl.
  - reflexivity.
  - destruct rest as [|next more]; simpl in *.
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.

Theorem rbody_nodes : forall steps rest elem held source,
  fin_nodes (rbody steps rest elem held source) =
    length held + 4 * length steps + 3.
Proof.
  induction steps as [|step more IH]; intros rest elem held source; simpl.
  - rewrite rvec_nodes, length_rev. lia.
  - rewrite IH. simpl. lia.
Qed.

Theorem rbody_depth_held : forall steps rest elem held source,
  held <> [] ->
  fin_depth (rbody steps rest elem held source) = length steps + 2.
Proof.
  induction steps as [|step more IH]; intros rest elem held source apart; simpl.
  - rewrite rvec_depth.
    destruct (rev held) eqn:reversed.
    + apply (f_equal (@rev nat)) in reversed.
      rewrite rev_involutive in reversed.
      contradiction.
    + reflexivity.
  - rewrite IH by discriminate.
    destruct more as [|next tail]; simpl; lia.
Qed.

Theorem rbody_depth : forall steps rest elem source,
  fin_depth (rbody steps rest elem [] source) =
    match steps with
    | [] => 1
    | _ => length steps + 2
    end.
Proof.
  intros steps rest elem source.
  destruct steps as [|step more]; simpl.
  - reflexivity.
  - rewrite rbody_depth_held by discriminate.
    destruct more as [|next tail]; simpl; lia.
Qed.

Theorem rout_nodes : forall path rest elem source,
  fin_nodes (rout path rest elem source) =
    fin_nodes source + 4 + 4 * length (rsteps path).
Proof.
  intros path rest elem source.
  unfold rout.
  simpl.
  rewrite rbody_nodes.
  simpl.
  lia.
Qed.

Theorem rout_depth : forall path rest elem source,
  fin_depth (rout path rest elem source) =
    let body_depth :=
      match rsteps path with
      | [] => 1
      | _ => length (rsteps path) + 2
      end
    in
    S (Nat.max (fin_depth source) body_depth).
Proof.
  intros path rest elem source.
  unfold rout.
  simpl.
  rewrite rbody_depth.
  reflexivity.
Qed.

Theorem rfit_valid : forall path cut rest elem source,
  length (rsteps path) = cut ->
  rfit cut source = true ->
  fin_valid (rout path rest elem source) = true.
Proof.
  intros path cut rest elem source count fit_ok.
  unfold rfit in fit_ok.
  apply andb_true_iff in fit_ok as [_ out_ok].
  unfold fin_valid.
  rewrite rout_nodes, rout_depth.
  destruct (rsteps path) as [|step steps];
    simpl in count, out_ok |- *;
    subst cut;
    exact out_ok.
Qed.

Theorem rterm_valid : forall path cut rest elem source term,
  rterm path cut rest elem source = Some term ->
  fin_valid term = true.
Proof.
  intros path cut rest elem source term built.
  unfold rterm in built.
  destruct (fit (cut + rest) && ty_b elem && rfit cut source
    && rpath_b cut source path) eqn:accepted; try discriminate.
  inversion built; subst.
  apply andb_true_iff in accepted as [left path_ok].
  apply andb_true_iff in left as [left fit_ok].
  apply andb_true_iff in left as [_ _].
  unfold rpath_b in path_ok.
  apply andb_true_iff in path_ok as [left _].
  apply andb_true_iff in left as [count _].
  apply Nat.eqb_eq in count.
  eapply rfit_valid; eauto.
Qed.

Theorem rcheck_type : forall inputs path cut rest elem source
    typ row cost next,
  rift_check inputs path cut rest elem source = Some (typ, row, cost, next) ->
  typ = TPair (TVec cut elem) (TVec rest elem).
Proof.
  intros inputs path cut rest elem source typ row cost next accepted.
  unfold rift_check in accepted.
  destruct (rterm path cut rest elem source) as [term |]; try discriminate.
  destruct (pcheck inputs term) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (TPair (TVec cut elem) (TVec rest elem))) eqn:same;
    try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  reflexivity.
Qed.

Theorem rcheck_sound : forall inputs path cut rest elem source
    typ row cost next,
  rift_check inputs path cut rest elem source = Some (typ, row, cost, next) ->
  exists term,
    rterm path cut rest elem source = Some term /\
    pcheck inputs term =
      Some (TPair (TVec cut elem) (TVec rest elem), row, cost, next) /\
    typ = TPair (TVec cut elem) (TVec rest elem).
Proof.
  intros inputs path cut rest elem source typ row cost next accepted.
  unfold rift_check in accepted.
  destruct (rterm path cut rest elem source) as [term |] eqn:built;
    try discriminate.
  destruct (pcheck inputs term) as [[[[got grow] gcost] gnext] |]
    eqn:checked; try discriminate.
  destruct (ty_eqb got (TPair (TVec cut elem) (TVec rest elem))) eqn:same;
    try discriminate.
  apply ty_eqb_eq in same.
  inversion accepted; subst.
  exists term.
  repeat split; assumption.
Qed.

Theorem rcheck_complete : forall inputs path cut rest elem source
    term row cost next,
  rterm path cut rest elem source = Some term ->
  pcheck inputs term =
    Some (TPair (TVec cut elem) (TVec rest elem), row, cost, next) ->
  rift_check inputs path cut rest elem source =
    Some (TPair (TVec cut elem) (TVec rest elem), row, cost, next).
Proof.
  intros inputs path cut rest elem source term row cost next built checked.
  unfold rift_check.
  rewrite built, checked, ty_eqb_refl.
  reflexivity.
Qed.