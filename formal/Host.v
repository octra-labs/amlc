(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Uni.
Require Import Dec.
Require Import Lim.
Require Import Low.
Require Import Rule.
Require Import Fp.

Import ListNotations.

Definition key := (nat * nat)%type.

Definition key_eqb (left right : key) : bool :=
  Nat.eqb (fst left) (fst right) && Nat.eqb (snd left) (snd right).

Definition key_ltb (left right : key) : bool :=
  Nat.ltb (fst left) (fst right) ||
  (Nat.eqb (fst left) (fst right) && Nat.ltb (snd left) (snd right)).

Fixpoint key_mem (item : key) (items : list key) : bool :=
  match items with
  | [] => false
  | first :: rest => key_eqb item first || key_mem item rest
  end.

Fixpoint key_ins (item : key) (items : list key) : list key :=
  match items with
  | [] => [item]
  | first :: rest =>
      if key_ltb item first then item :: items else first :: key_ins item rest
  end.

Fixpoint key_sort (items : list key) : list key :=
  match items with
  | [] => []
  | first :: rest => key_ins first (key_sort rest)
  end.

Fixpoint key_sub (left right : list key) : bool :=
  match left with
  | [] => true
  | first :: rest => key_mem first right && key_sub rest right
  end.

Fixpoint typed (typ : ty) (item : value) {struct typ} : bool :=
  match typ, item with
  | TUnit, VUnit => true
  | TBool, VBool _ => true
  | TInt, VInt _ => true
  | TBytes len, VBytes bytes =>
      Nat.eqb len (length bytes) && bytes_b bytes
  | TVec len elem, VVec values =>
      Nat.eqb len (length values) && forallb (typed elem) values
  | TCap kind, VCap actual id => Nat.eqb kind actual && fit id
  | TEnc key rem, VEnc actual_key actual_rem field =>
      Nat.eqb key actual_key && (Nat.eqb rem actual_rem && Fp.valid field)
  | TPair first_ty second_ty, VPair first second =>
      typed first_ty first && typed second_ty second
  | TSum first_ty _, VInl value => typed first_ty value
  | TSum _ second_ty, VInr value => typed second_ty value
  | _, _ => false
  end.

Definition vnode := (nat * value)%type.

Definition kids (depth : nat) (item : value) : list vnode :=
  let next := S depth in
  match item with
  | VVec values => map (fun value => (next, value)) values
  | VPair first second => [(next, first); (next, second)]
  | VInl value | VInr value => [(next, value)]
  | _ => []
  end.

Fixpoint shape_f (fuel : nat) (work : list vnode) : bool :=
  match work with
  | [] => true
  | (depth, item) :: rest =>
      match fuel with
      | 0 => false
      | S more =>
          Nat.leb depth (rtm_depth local) &&
          shape_f more (kids depth item ++ rest)
      end
  end.

Definition shape (item : value) : bool :=
  value_b item && shape_f (rtm_nodes local) [(0, item)].

Definition putv (binder : bind) (item : value) (sigma : env) : env :=
  match bmul binder with
  | M0 => sigma
  | M1 => Slot (bid binder) M1 (bty binder) item true :: sigma
  | MM => Slot (bid binder) MM (bty binder) item true :: sigma
  end.

Fixpoint load (sigma : env) (binds : list bind) (values : list value)
    : option env :=
  match binds, values with
  | [], [] => Some sigma
  | binder :: rest, item :: more =>
      if typed (bty binder) item && shape item then
        load (putv binder item sigma) rest more
      else None
  | _, _ => None
  end.

Fixpoint cap_f (fuel : nat) (work : list vnode) (seen : list key)
    : option (list key) :=
  match work with
  | [] => Some seen
  | (depth, item) :: rest =>
      match fuel with
      | 0 => None
      | S more =>
          if Nat.leb depth (rtm_depth local) then
            match item with
            | VCap kind id =>
                if fit kind && fit id then
                  let key := (kind, id) in
                  if key_mem key seen then None
                  else cap_f more rest (key :: seen)
                else None
            | _ => cap_f more (kids depth item ++ rest) seen
            end
          else None
      end
  end.

Definition caps (values : list value) : option (list key) :=
  if Nat.leb (length values) (rinputs local) then
    cap_f (rtm_nodes local) (map (fun value => (0, value)) values) []
  else None.

Definition cap (item : value) : option (list key) :=
  cap_f (rtm_nodes local) [(0, item)] [].

Lemma bytes_typed : forall bytes,
  bytes_b bytes = true -> Forall (fun byte => byte < 256) bytes.
Proof.
  induction bytes as [|byte rest repeat]; intros valid; simpl in valid.
  - constructor.
  - apply andb_true_iff in valid.
    destruct valid as [head tail].
    constructor.
    + apply Nat.ltb_lt. exact head.
    + apply repeat. exact tail.
Qed.

Theorem typed_sound : forall typ item,
  typed typ item = true -> hasv item typ.
Proof.
  induction typ as [| | |len|len elem repeat|kind|key rem
    |first first_ih second second_ih|first first_ih second second_ih];
    intros item valid; destruct item;
    simpl in valid; try discriminate.
  - constructor.
  - constructor.
  - constructor.
  - apply andb_true_iff in valid.
    destruct valid as [size bytes].
    apply Nat.eqb_eq in size.
    subst.
    constructor.
    apply bytes_typed.
    exact bytes.
  - apply andb_true_iff in valid.
    destruct valid as [size items].
    apply Nat.eqb_eq in size.
    subst.
    constructor.
    rewrite forallb_forall in items.
    rewrite Forall_forall.
    intros item present.
    apply repeat.
    apply items.
    exact present.
  - apply andb_true_iff in valid.
    destruct valid as [same_kind _].
    apply Nat.eqb_eq in same_kind.
    subst.
    constructor.
  - apply andb_true_iff in valid.
    destruct valid as [same_key tail].
    apply andb_true_iff in tail.
    destruct tail as [same_rem valid_field].
    apply Nat.eqb_eq in same_key.
    apply Nat.eqb_eq in same_rem.
    subst.
    constructor.
    unfold field, Fp.p.
    apply Fp.valid_range.
    exact valid_field.
  - apply andb_true_iff in valid.
    destruct valid as [left right].
    constructor.
    + apply first_ih. exact left.
    + apply second_ih. exact right.
  - constructor.
    apply first_ih.
    exact valid.
  - constructor.
    apply second_ih.
    exact valid.
Qed.

Lemma putv_ok : forall binder gamma next item sigma,
  openb binder gamma = Some next ->
  typed (bty binder) item = true ->
  env_ok gamma sigma ->
  env_ok next (putv binder item sigma).
Proof.
  intros [id mode typ] gamma next item sigma opened typed_ok env.
  cbn [bid bmul bty] in opened, typed_ok |- *.
  unfold openb in opened.
  cbn [bid bmul bty] in opened.
  destruct (fresh_b id gamma); try discriminate.
  destruct mode; cbn in opened; unfold putv; cbn.
  - destruct (data_b typ); inversion opened; subst. exact env.
  - inversion opened; subst.
    constructor.
    + apply typed_sound. exact typed_ok.
    + exact env.
  - destruct (data_b typ); try discriminate.
    inversion opened; subst.
    constructor.
    + apply typed_sound. exact typed_ok.
    + exact env.
Qed.

Theorem load_ok : forall binds values gamma next sigma final,
  opens gamma binds = Some next ->
  load sigma binds values = Some final ->
  env_ok gamma sigma ->
  env_ok next final.
Proof.
  induction binds as [|binder rest repeat]; intros values gamma next sigma final
    opened loaded env.
  - destruct values; simpl in loaded; try discriminate.
    simpl in opened.
    inversion opened; inversion loaded; subst.
    exact env.
  - destruct values as [|item more]; simpl in loaded; try discriminate.
    simpl in opened.
    destruct (openb binder gamma) as [mid |] eqn:one; try discriminate.
    destruct (typed (bty binder) item && shape item) eqn:item_ok;
      try discriminate.
    apply andb_true_iff in item_ok.
    destruct item_ok as [typed_ok _].
    apply repeat with (values := more) (gamma := mid)
      (sigma := putv binder item sigma).
    + exact opened.
    + exact loaded.
    + apply putv_ok with (gamma := gamma).
      * exact one.
      * exact typed_ok.
      * exact env.
Qed.