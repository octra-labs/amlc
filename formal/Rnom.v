(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.

Require Import Uni.
Require Import Lim.
Require Import Idx.
Require Import Raw.
Require Import Data.
Require Import Rec.

Import ListNotations.

Fixpoint ylift (typ : ty) : option ity :=
  match typ with
  | TUnit => Some YUnit
  | TBool => Some YBool
  | TInt => Some YInt
  | TBytes len => Some (YBytes (ILit len))
  | TVec len elem =>
      match ylift elem with
      | Some out => Some (YVec (ILit len) out)
      | None => None
      end
  | TCap kind => Some (YCap kind)
  | TPair lhs rhs =>
      match ylift lhs, ylift rhs with
      | Some lout, Some rout => Some (YPair lout rout)
      | _, _ => None
      end
  | TSum lhs rhs =>
      match ylift lhs, ylift rhs with
      | Some lout, Some rout => Some (YSum lout rout)
      | _, _ => None
      end
  | TEnc _ _ => None
  end.

Fixpoint ntag (bits : list bool) : rtm :=
  match bits with
  | [] => RBytes []
  | bit :: rest =>
      RPair (if bit then RBool true else RUnit) (ntag rest)
  end.

Fixpoint nmake_in (name : nat) (value : rtm) (items : list ctor)
    : option rtm :=
  match items with
  | [] => None
  | [item] => if Nat.eqb name (cname item) then Some value else None
  | item :: rest =>
      match sumt rest with
      | Some rhs =>
          if Nat.eqb name (cname item) then
            match ylift rhs with
            | Some raw => Some (RInl value raw)
            | None => None
            end
          else
            match ylift (carg item), nmake_in name value rest with
            | Some raw, Some out => Some (RInr raw out)
            | _, _ => None
            end
      | None => None
      end
  end.

Definition nmake (item : dtype) (name : nat) (value : rtm) : option rtm :=
  if decl_b item then
    match nmake_in name value (dctors item) with
    | Some out => Some (RPair (ntag (dtag item)) out)
    | None => None
    end
  else None.

Record narm : Type := NArm {
  naname : nat;
  nabind : rbind;
  nabody : rtm
}.

Fixpoint narms_b (ctors : list ctor) (arms : list narm) : bool :=
  match ctors, arms with
  | [], [] => true
  | item :: rest, choice :: choices =>
      Nat.eqb (cname item) (naname choice) && narms_b rest choices
  | _, _ => false
  end.

Fixpoint naexact (ctors : list ctor) (arms : list narm) (body : rtm)
    : option rtm :=
  match ctors, arms with
  | [], [] => Some body
  | ctor :: rest, arm :: tail =>
      match naexact rest tail body with
      | Some out => Some (RExact (nabind arm) (carg ctor) out)
      | None => None
      end
  | _, _ => None
  end.

Fixpoint nbranch (seed : nat) (ctors : list ctor) (arms : list narm)
    (value : rtm) : option rtm :=
  match ctors, arms with
  | [_], [choice] => Some (RLet (nabind choice) value (nabody choice))
  | _ :: rest, choice :: choices =>
      match sumt rest with
      | Some rhs =>
          match ylift rhs,
              nbranch (S seed) rest choices (RVar (did seed)) with
          | Some raw, Some no => Some (RCase value
              (nabind choice) (nabody choice)
              (RBind (did seed) M1 raw) no)
          | _, _ => None
          end
      | None => None
      end
  | _, _ => None
  end.

Definition ncase (item : dtype) (value : rtm) (arms : list narm)
    : option rtm :=
  if decl_b item then
    if narms_b (dctors item) arms then
      match tagt (dtag item), sumt (dctors item) with
      | tag, Some sum =>
          match ylift tag, ylift sum,
              nbranch 2 (dctors item) arms (RVar (did 1)) with
          | Some rtag, Some rsum, Some body =>
              naexact (dctors item) arms (RUnpair value
                (RBind (did 0) MM rtag) (RBind (did 1) M1 rsum) body)
          | _, _, _ => None
          end
      | _, None => None
      end
    else None
  else None.

Record nitem : Type := NItem {
  niname : nat;
  nivalue : rtm
}.

Fixpoint nitems_b (fields : list rfield) (items : list nitem) : bool :=
  match fields, items with
  | [], [] => true
  | field :: rest, item :: tail =>
      Nat.eqb (rfname field) (niname item) && nitems_b rest tail
  | _, _ => false
  end.

Fixpoint npack (items : list nitem) : option rtm :=
  match items with
  | [] => None
  | [item] => Some (nivalue item)
  | item :: rest =>
      match npack rest with
      | Some rhs => Some (RPair (nivalue item) rhs)
      | None => None
      end
  end.

Definition nrmake (item : rtype) (items : list nitem) : option rtm :=
  if rdecl_b item then
    if nitems_b (rfields item) items then
      match rdata item, npack items with
      | Some data, Some value => nmake data (rname item) value
      | _, _ => None
      end
    else None
  else None.

Record npick : Type := NPick {
  npname : nat;
  npbind : rbind
}.

Fixpoint npicks_b (fields : list rfield) (items : list npick) : bool :=
  match fields, items with
  | [], [] => true
  | field :: rest, item :: tail =>
      Nat.eqb (rfname field) (npname item) && npicks_b rest tail
  | _, _ => false
  end.

Fixpoint npexact (fields : list rfield) (items : list npick) (body : rtm)
    : option rtm :=
  match fields, items with
  | [], [] => Some body
  | field :: rest, item :: tail =>
      match npexact rest tail body with
      | Some out => Some (RExact (npbind item) (rftyp field) out)
      | None => None
      end
  | _, _ => None
  end.

Fixpoint nhas (name : nat) (items : list npick) : bool :=
  match items with
  | [] => false
  | item :: rest => Nat.eqb name (rbname (npbind item)) || nhas name rest
  end.

Fixpoint nnames_b (items : list npick) : bool :=
  match items with
  | [] => true
  | item :: rest =>
      negb (nhas (rbname (npbind item)) rest) && nnames_b rest
  end.

Fixpoint nrbody (seed : nat) (fields : list rfield) (items : list npick)
    (value body : rtm) : option rtm :=
  match fields, items with
  | [_], [item] => Some (RLet (npbind item) value body)
  | _ :: rest, item :: tail =>
      match prodt rest with
      | Some rhs =>
          match ylift rhs,
              nrbody (S seed) rest tail (RVar (did seed)) body with
          | Some raw, Some out => Some (RUnpair value (npbind item)
              (RBind (did seed) (paym rhs) raw) out)
          | _, _ => None
          end
      | None => None
      end
  | _, _ => None
  end.

Definition nrsplit (item : rtype) (value : rtm) (items : list npick)
    (body : rtm) : option rtm :=
  if rdecl_b item then
    if npicks_b (rfields item) items && nnames_b items then
      match prodt (rfields item), rdata item with
      | Some prod, Some data =>
          match ylift prod,
              nrbody 3 (rfields item) items (RVar (did 2)) body with
          | Some raw, Some out =>
              match ncase data value
                  [NArm (rname item) (RBind (did 2) (paym prod) raw) out] with
              | Some term => npexact (rfields item) items term
              | None => None
              end
          | _, _ => None
          end
      | _, _ => None
      end
    else None
  else None.

Theorem nmake_decl : forall item name value out,
  nmake item name value = Some out -> decl_b item = true.
Proof.
  intros item name value out accepted.
  unfold nmake in accepted.
  destruct (decl_b item) eqn:valid; try discriminate.
  reflexivity.
Qed.

Theorem ncase_decl : forall item value arms out,
  ncase item value arms = Some out ->
  decl_b item = true /\ narms_b (dctors item) arms = true.
Proof.
  intros item value arms out accepted.
  unfold ncase in accepted.
  destruct (decl_b item) eqn:valid; try discriminate.
  destruct (narms_b (dctors item) arms) eqn:ordered; try discriminate.
  split; reflexivity.
Qed.

Theorem nrmake_decl : forall item values out,
  nrmake item values = Some out ->
  rdecl_b item = true /\ nitems_b (rfields item) values = true.
Proof.
  intros item values out accepted.
  unfold nrmake in accepted.
  destruct (rdecl_b item) eqn:valid; try discriminate.
  destruct (nitems_b (rfields item) values) eqn:ordered; try discriminate.
  split; reflexivity.
Qed.

Theorem nrsplit_decl : forall item value fields body out,
  nrsplit item value fields body = Some out ->
  rdecl_b item = true /\
  npicks_b (rfields item) fields = true /\ nnames_b fields = true.
Proof.
  intros item value fields body out accepted.
  unfold nrsplit in accepted.
  destruct (rdecl_b item) eqn:valid; try discriminate.
  destruct (npicks_b (rfields item) fields && nnames_b fields)
    eqn:fields_ok; try discriminate.
  apply andb_true_iff in fields_ok as [ordered distinct].
  split.
  - reflexivity.
  - split; assumption.
Qed.