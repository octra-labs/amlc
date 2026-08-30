(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Uni.
Require Import Dec.
Require Import DecComp.
Require Import DecSound.
Require Import Lim.
Require Import Surf.
Require Import Low.

Import ListNotations.

Record ctor : Type := Ctor {
  cname : nat;
  carg : ty
}.

Record dtype : Type := DType {
  dtag : list bool;
  dname : nat;
  dctors : list ctor
}.

Record arm : Type := Arm {
  aname : nat;
  abind : sbind;
  abody : stm
}.

Fixpoint sumt (items : list ctor) : option ty :=
  match items with
  | [] => None
  | [item] => Some (carg item)
  | item :: rest =>
      match sumt rest with
      | Some rhs => Some (TSum (carg item) rhs)
      | None => None
      end
  end.

Definition tag_len : nat := 12.

Fixpoint tagt (bits : list bool) : ty :=
  match bits with
  | [] => TBytes 0
  | bit :: rest => TPair (if bit then TBool else TUnit) (tagt rest)
  end.

Fixpoint tagv (bits : list bool) : stm :=
  match bits with
  | [] => SBytes []
  | bit :: rest =>
      SPair (if bit then SK (VBool true) TBool else SK VUnit TUnit) (tagv rest)
  end.

Definition dtype_t (item : dtype) : option ty :=
  match sumt (dctors item) with
  | Some sum => Some (TPair (tagt (dtag item)) sum)
  | None => None
  end.

Fixpoint tdepth (typ : ty) : nat :=
  match typ with
  | TUnit | TBool | TInt | TBytes _ | TCap _ | TEnc _ _ => 0
  | TVec _ elem => S (tdepth elem)
  | TPair lhs rhs | TSum lhs rhs => S (Nat.max (tdepth lhs) (tdepth rhs))
  end.

Fixpoint tnodes (typ : ty) : nat :=
  match typ with
  | TUnit | TBool | TInt | TBytes _ | TCap _ | TEnc _ _ => 1
  | TVec _ elem => S (tnodes elem)
  | TPair lhs rhs | TSum lhs rhs => S (tnodes lhs + tnodes rhs)
  end.

Definition node_max : nat := 100000.

Definition dtype_b (item : dtype) : bool :=
  match dtype_t item with
  | Some typ =>
      ty_b typ
        && Nat.leb (tdepth typ) pmax
        && Nat.leb (tnodes typ) node_max
  | None => false
  end.

Fixpoint data_b (typ : ty) : bool :=
  match typ with
  | TUnit | TBool | TInt | TBytes _ | TEnc _ _ => true
  | TVec count elem =>
      match count with
      | 0 => true
      | S _ => data_b elem
      end
  | TCap _ => false
  | TPair lhs rhs | TSum lhs rhs => data_b lhs && data_b rhs
  end.

Definition paym (typ : ty) : mul := if data_b typ then MM else M1.

Definition meqb (lhs rhs : mul) : bool :=
  match lhs, rhs with
  | M0, M0 | M1, M1 | MM, MM => true
  | _, _ => false
  end.

Fixpoint has_name (name : nat) (items : list ctor) : bool :=
  match items with
  | [] => false
  | item :: rest => Nat.eqb name (cname item) || has_name name rest
  end.

Fixpoint names_b (items : list ctor) : bool :=
  match items with
  | [] => true
  | item :: rest => negb (has_name (cname item) rest) && names_b rest
  end.

Definition decl_b (item : dtype) : bool :=
  match dctors item with
  | [] => false
  | ctors =>
      Nat.eqb (length (dtag item)) tag_len
        && Nat.leb (length ctors) pmax
        && names_b ctors
        && dtype_b item
  end.

Definition arm_b (item : ctor) (choice : arm) : bool :=
  Nat.eqb (cname item) (aname choice)
    && ty_eqb (carg item) (sty (abind choice))
    && meqb (paym (carg item)) (smul (abind choice)).

Fixpoint arms_b (ctors : list ctor) (arms : list arm) : bool :=
  match ctors, arms with
  | [], [] => true
  | item :: rest, choice :: choices =>
      arm_b item choice && arms_b rest choices
  | _, _ => false
  end.

Fixpoint make_in (name : nat) (value : stm) (items : list ctor)
    : option stm :=
  match items with
  | [] => None
  | [item] => if Nat.eqb name (cname item) then Some value else None
  | item :: rest =>
      match sumt rest with
      | Some rhs =>
          if Nat.eqb name (cname item) then Some (SInl value rhs)
          else
            match make_in name value rest with
            | Some out => Some (SInr (carg item) out)
            | None => None
            end
      | None => None
      end
  end.

Definition make (item : dtype) (name : nat) (value : stm) : option stm :=
  if decl_b item then
    match make_in name value (dctors item) with
    | Some out => Some (SPair (tagv (dtag item)) out)
    | None => None
    end
  else None.

Definition did (id : nat) : nat := S (id + id).

Fixpoint dbranch (seed : nat) (ctors : list ctor) (arms : list arm)
    (value : stm) : option stm :=
  match ctors, arms with
  | [_], [choice] => Some (SLet (abind choice) value (abody choice))
  | _ :: rest, choice :: choices =>
      match sumt rest with
      | Some rhs =>
          match dbranch (S seed) rest choices (SVar (did seed)) with
          | Some no => Some (SCase value (abind choice) (abody choice)
              (SBind (did seed) M1 rhs) no)
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.

Definition dcase (item : dtype) (value : stm) (arms : list arm)
    : option stm :=
  if decl_b item then
    if arms_b (dctors item) arms then
      match sumt (dctors item),
          dbranch 2 (dctors item) arms (SVar (did 1)) with
      | Some sum, Some body => Some (SUnpair value
          (SBind (did 0) MM (tagt (dtag item)))
          (SBind (did 1) M1 sum) body)
      | _, _ => None
      end
    else None
  else None.

Fixpoint branch (env : senv) (next : nat) (ctors : list ctor)
    (arms : list arm) (value : tm) : option (tm * nat) :=
  match ctors, arms with
  | [_], [choice] =>
      match low ((sname (abind choice), next) :: env) (S next) (abody choice) with
      | Some (body, last) =>
          Some (Let (put next (abind choice)) value body, last)
      | None => None
      end
  | _ :: rest, choice :: choices =>
      match sumt rest with
      | Some rhs =>
          match low ((sname (abind choice), next) :: env) (S next)
              (abody choice) with
          | Some (yes, after_yes) =>
              let right_id := after_yes in
              match branch env (S right_id) rest choices (Var right_id) with
              | Some (no, last) =>
                  Some (Case value (put next (abind choice)) yes
                    (Bind right_id M1 rhs) no, last)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.

Definition dprog (items : list sbind) (item : dtype) (value : stm)
    (arms : list arm) : option (list bind * tm) :=
  if Nat.leb (length items) pmax then
    if decl_b item then
      if arms_b (dctors item) arms then
        match ins [] 0 items with
        | Some (env, next, binds) =>
            match low env next value with
            | Some (core, after) =>
                match sumt (dctors item) with
                | Some sum =>
                    let tag_id := after in
                    let sum_id := S tag_id in
                    match branch env (S sum_id) (dctors item) arms (Var sum_id) with
                    | Some (body, _) =>
                        let out := Unpair core
                          (Bind tag_id MM (tagt (dtag item)))
                          (Bind sum_id M1 sum) body in
                        if forallb bind_b binds && tm_b out
                        then Some (binds, out)
                        else None
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
      else None
    else None
  else None.

Definition dpcheck (items : list sbind) (item : dtype) (value : stm)
    (arms : list arm) : option chk :=
  match dprog items item value arms with
  | Some (binds, core) =>
      match opens [] binds with
      | Some gamma =>
          match checkb gamma core with
          | Some (typ, row, cost, next) =>
              if doneb next then Some (typ, row, cost, next) else None
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem tagt_inj : forall lhs rhs,
  tagt lhs = tagt rhs -> lhs = rhs.
Proof.
  induction lhs as [|lbit lrest IH]; intros rhs same;
    destruct rhs as [|rbit rrest]; simpl in same; try discriminate.
  - reflexivity.
  - destruct lbit, rbit; inversion same; subst; f_equal; apply IH; assumption.
Qed.

Lemma has_name_absent : forall name items,
  has_name name items = false -> ~ In name (map cname items).
Proof.
  intros name items.
  induction items as [|item rest IH]; intros absent found.
  - contradiction.
  - simpl in absent.
    apply orb_false_iff in absent as [head tail].
    simpl in found.
    destruct found as [same | found].
    + subst.
      rewrite Nat.eqb_refl in head.
      discriminate.
    + apply (IH tail found).
Qed.

Lemma names_ok : forall items,
  names_b items = true -> NoDup (map cname items).
Proof.
  induction items as [|item rest IH]; intros accepted.
  - constructor.
  - simpl in accepted.
    apply andb_true_iff in accepted as [head tail].
    constructor.
    + apply has_name_absent.
      apply negb_true_iff in head.
      exact head.
    + apply IH.
      exact tail.
Qed.

Lemma arm_name : forall item choice,
  arm_b item choice = true -> aname choice = cname item.
Proof.
  intros item choice accepted.
  unfold arm_b in accepted.
  apply andb_true_iff in accepted as [head _].
  apply andb_true_iff in head as [same _].
  apply Nat.eqb_eq in same.
  symmetry.
  exact same.
Qed.

Lemma arms_names : forall ctors arms,
  arms_b ctors arms = true -> map aname arms = map cname ctors.
Proof.
  induction ctors as [|item rest IH]; intros arms accepted;
    destruct arms as [|choice choices]; simpl in accepted; try discriminate.
  - reflexivity.
  - apply andb_true_iff in accepted as [head tail].
    simpl.
    rewrite (arm_name item choice head).
    rewrite (IH choices tail).
    reflexivity.
Qed.

Lemma decl_unique_b : forall item,
  decl_b item = true -> names_b (dctors item) = true.
Proof.
  intros item accepted.
  unfold decl_b in accepted.
  destruct (dctors item) as [|head rest] eqn:ctors; try discriminate.
  remember (names_b (head :: rest)) as unique eqn:unique_ok.
  destruct (Nat.eqb (length (dtag item)) tag_len); try discriminate.
  destruct (Nat.leb (length (head :: rest)) pmax); try discriminate.
  destruct unique; try discriminate.
  reflexivity.
Qed.

Lemma decl_names : forall item,
  decl_b item = true -> NoDup (map cname (dctors item)).
Proof.
  intros item accepted.
  apply names_ok.
  apply decl_unique_b.
  exact accepted.
Qed.

Theorem dprog_exhaustive : forall items item value arms binds core,
  dprog items item value arms = Some (binds, core) ->
  map aname arms = map cname (dctors item) /\
  NoDup (map aname arms).
Proof.
  intros items item value arms binds core accepted.
  unfold dprog in accepted.
  destruct (Nat.leb (length items) pmax); try discriminate.
  destruct (decl_b item) eqn:decl_ok; try discriminate.
  destruct (arms_b (dctors item) arms) eqn:arms_ok; try discriminate.
  split.
  - apply arms_names.
    exact arms_ok.
  - rewrite (arms_names (dctors item) arms arms_ok).
    apply decl_names.
    exact decl_ok.
Qed.

Theorem dcase_exhaustive : forall item value arms out,
  dcase item value arms = Some out ->
  map aname arms = map cname (dctors item) /\
  NoDup (map aname arms).
Proof.
  intros item value arms out accepted.
  unfold dcase in accepted.
  destruct (decl_b item) eqn:decl_ok; try discriminate.
  destruct (arms_b (dctors item) arms) eqn:arms_ok; try discriminate.
  split.
  - apply arms_names.
    exact arms_ok.
  - rewrite (arms_names (dctors item) arms arms_ok).
    apply decl_names.
    exact decl_ok.
Qed.

Theorem dpcheck_sound : forall items item value arms typ row cost next,
  dpcheck items item value arms = Some (typ, row, cost, next) ->
  exists binds core gamma,
    dprog items item value arms = Some (binds, core) /\
    opens [] binds = Some gamma /\
    check gamma core typ row cost next /\
    doneb next = true.
Proof.
  intros items item value arms typ row cost next accepted.
  unfold dpcheck in accepted.
  destruct (dprog items item value arms) as [[binds core] |] eqn:lowered;
    try discriminate.
  destruct (opens [] binds) as [gamma |] eqn:opened; try discriminate.
  destruct (checkb gamma core) as [[[[out_typ out_row] out_cost] out_next] |]
    eqn:checked; try discriminate.
  destruct (doneb out_next) eqn:done; try discriminate.
  inversion accepted; subst.
  exists binds, core, gamma.
  repeat split; try assumption.
  apply checkb_sound.
  exact checked.
Qed.

Theorem dpcheck_complete : forall items item value arms binds core gamma
    typ row cost next,
  dprog items item value arms = Some (binds, core) ->
  opens [] binds = Some gamma ->
  check gamma core typ row cost next ->
  doneb next = true ->
  dpcheck items item value arms = Some (typ, row, cost, next).
Proof.
  intros items item value arms binds core gamma typ row cost next
    lowered opened checked done.
  unfold dpcheck.
  rewrite lowered, opened.
  rewrite (checkb_complete gamma core typ row cost next checked).
  rewrite done.
  reflexivity.
Qed.