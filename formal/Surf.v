(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.

Require Import Uni.

Import ListNotations.

Record sbind : Type := SBind {
  sname : nat;
  smul : mul;
  sty : ty
}.

Inductive stm : Type :=
| SK : value -> ty -> stm
| SBytes : list nat -> stm
| SVnil : ty -> stm
| SVar : nat -> stm
| SLet : sbind -> stm -> stm -> stm
| SIf : stm -> stm -> stm -> stm
| SPair : stm -> stm -> stm
| SUnpair : stm -> sbind -> sbind -> stm -> stm
| SFst : stm -> stm
| SSnd : stm -> stm
| SInl : stm -> ty -> stm
| SInr : ty -> stm -> stm
| SCase : stm -> sbind -> stm -> sbind -> stm -> stm
| SAct : atom -> stm -> stm
| SAdd : stm -> stm -> stm
| SSub : stm -> stm -> stm
| SMul : stm -> stm -> stm
| SDiv : stm -> stm -> stm
| SMod : stm -> stm -> stm
| SNeg : stm -> stm
| SAbs : stm -> stm
| SEq : ty -> stm -> stm -> stm
| SCat : stm -> stm -> stm
| STake : nat -> stm -> stm
| SDrop : nat -> stm -> stm
| SVcons : stm -> stm -> stm
| SVcat : stm -> stm -> stm
| SAt : nat -> stm -> stm
| SUncons : stm -> stm
| SFold : nat -> stm -> stm -> sbind -> sbind -> stm -> stm
| SStep : stm -> stm -> stm
| SClose : stm -> stm.

Fixpoint names (term : stm) : list nat :=
  match term with
  | SK _ _ | SBytes _ | SVnil _ => []
  | SVar name => [name]
  | SLet item value body => sname item :: names value ++ names body
  | SIf guard yes no => names guard ++ names yes ++ names no
  | SPair first second | SAdd first second | SSub first second
  | SMul first second | SDiv first second | SMod first second
  | SCat first second
  | SVcons first second | SVcat first second | SStep first second =>
      names first ++ names second
  | SUnpair product first second body =>
      sname first :: sname second :: names product ++ names body
  | SFst value | SSnd value | SNeg value | SAbs value
  | SUncons value | SClose value => names value
  | SInl value _ | SInr _ value | SAct _ value
  | STake _ value | SDrop _ value | SAt _ value => names value
  | SCase value first yes second no =>
      sname first :: sname second :: names value ++ names yes ++ names no
  | SEq _ first second => names first ++ names second
  | SFold _ vector seed item state body =>
      sname item :: sname state :: names vector ++ names seed ++ names body
  end.

Definition has (name : nat) (term : stm) : bool :=
  existsb (Nat.eqb name) (names term).

Definition senv := list (nat * nat).

Fixpoint findn (name : nat) (env : senv) : option nat :=
  match env with
  | [] => None
  | (key, id) :: rest =>
      if Nat.eqb name key then Some id else findn name rest
  end.

Inductive alpha : senv -> senv -> stm -> stm -> Prop :=
| AK : forall left right value typ,
    alpha left right (SK value typ) (SK value typ)
| ABytes : forall left right bytes,
    alpha left right (SBytes bytes) (SBytes bytes)
| AVnil : forall left right typ,
    alpha left right (SVnil typ) (SVnil typ)
| AVar : forall left right lname rname id,
    findn lname left = Some id ->
    findn rname right = Some id ->
    alpha left right (SVar lname) (SVar rname)
| ALet : forall left right lname rname mode typ lvalue rvalue lbody rbody,
    alpha left right lvalue rvalue ->
    (forall id, alpha ((lname, id) :: left) ((rname, id) :: right)
      lbody rbody) ->
    alpha left right
      (SLet (SBind lname mode typ) lvalue lbody)
      (SLet (SBind rname mode typ) rvalue rbody)
| AIf : forall left right lg rg ly ry ln rn,
    alpha left right lg rg ->
    alpha left right ly ry ->
    alpha left right ln rn ->
    alpha left right (SIf lg ly ln) (SIf rg ry rn)
| APair : forall left right la ra lb rb,
    alpha left right la ra ->
    alpha left right lb rb ->
    alpha left right (SPair la lb) (SPair ra rb)
| AUnpair : forall left right lp rp ln1 rn1 mode1 typ1 ln2 rn2 mode2 typ2 lb rb,
    ln1 <> ln2 ->
    rn1 <> rn2 ->
    alpha left right lp rp ->
    (forall id1 id2,
      alpha ((ln2, id2) :: (ln1, id1) :: left)
        ((rn2, id2) :: (rn1, id1) :: right) lb rb) ->
    alpha left right
      (SUnpair lp (SBind ln1 mode1 typ1) (SBind ln2 mode2 typ2) lb)
      (SUnpair rp (SBind rn1 mode1 typ1) (SBind rn2 mode2 typ2) rb)
| AFst : forall left right lv rv,
    alpha left right lv rv ->
    alpha left right (SFst lv) (SFst rv)
| ASnd : forall left right lv rv,
    alpha left right lv rv ->
    alpha left right (SSnd lv) (SSnd rv)
| AInl : forall left right lv rv typ,
    alpha left right lv rv ->
    alpha left right (SInl lv typ) (SInl rv typ)
| AInr : forall left right typ lv rv,
    alpha left right lv rv ->
    alpha left right (SInr typ lv) (SInr typ rv)
| ACase : forall left right lv rv ln rn lmode ltyp ly ry
    ln2 rn2 rmode rtyp lno rno,
    alpha left right lv rv ->
    (forall id, alpha ((ln, id) :: left) ((rn, id) :: right) ly ry) ->
    (forall id, alpha ((ln2, id) :: left) ((rn2, id) :: right) lno rno) ->
    alpha left right
      (SCase lv (SBind ln lmode ltyp) ly (SBind ln2 rmode rtyp) lno)
      (SCase rv (SBind rn lmode ltyp) ry (SBind rn2 rmode rtyp) rno)
| AAct : forall left right action lb rb,
    alpha left right lb rb ->
    alpha left right (SAct action lb) (SAct action rb)
| AAdd : forall left right la ra lb rb,
    alpha left right la ra ->
    alpha left right lb rb ->
    alpha left right (SAdd la lb) (SAdd ra rb)
| ASub : forall left right la ra lb rb,
    alpha left right la ra ->
    alpha left right lb rb ->
    alpha left right (SSub la lb) (SSub ra rb)
| AMul : forall left right la ra lb rb,
    alpha left right la ra ->
    alpha left right lb rb ->
    alpha left right (SMul la lb) (SMul ra rb)
| ADiv : forall left right la ra lb rb,
    alpha left right la ra ->
    alpha left right lb rb ->
    alpha left right (SDiv la lb) (SDiv ra rb)
| AMod : forall left right la ra lb rb,
    alpha left right la ra ->
    alpha left right lb rb ->
    alpha left right (SMod la lb) (SMod ra rb)
| ANeg : forall left right lv rv,
    alpha left right lv rv ->
    alpha left right (SNeg lv) (SNeg rv)
| AAbs : forall left right lv rv,
    alpha left right lv rv ->
    alpha left right (SAbs lv) (SAbs rv)
| AEq : forall left right typ la ra lb rb,
    alpha left right la ra ->
    alpha left right lb rb ->
    alpha left right (SEq typ la lb) (SEq typ ra rb)
| ACat : forall left right la ra lb rb,
    alpha left right la ra ->
    alpha left right lb rb ->
    alpha left right (SCat la lb) (SCat ra rb)
| ATake : forall left right len lv rv,
    alpha left right lv rv ->
    alpha left right (STake len lv) (STake len rv)
| ADrop : forall left right len lv rv,
    alpha left right lv rv ->
    alpha left right (SDrop len lv) (SDrop len rv)
| AVcons : forall left right la ra lb rb,
    alpha left right la ra ->
    alpha left right lb rb ->
    alpha left right (SVcons la lb) (SVcons ra rb)
| AVcat : forall left right la ra lb rb,
    alpha left right la ra ->
    alpha left right lb rb ->
    alpha left right (SVcat la lb) (SVcat ra rb)
| AAt : forall left right index lv rv,
    alpha left right lv rv ->
    alpha left right (SAt index lv) (SAt index rv)
| AUncons : forall left right lv rv,
    alpha left right lv rv ->
    alpha left right (SUncons lv) (SUncons rv)
| AFold : forall left right count lv rv ls rs ln1 rn1 mode1 typ1
    ln2 rn2 mode2 typ2 lb rb,
    ln1 <> ln2 ->
    rn1 <> rn2 ->
    alpha left right lv rv ->
    alpha left right ls rs ->
    (forall id1 id2,
      alpha ((ln2, id2) :: (ln1, id1) :: left)
        ((rn2, id2) :: (rn1, id1) :: right) lb rb) ->
    alpha left right
      (SFold count lv ls (SBind ln1 mode1 typ1) (SBind ln2 mode2 typ2) lb)
      (SFold count rv rs (SBind rn1 mode1 typ1) (SBind rn2 mode2 typ2) rb)
| AStep : forall left right la ra lb rb,
    alpha left right la ra ->
    alpha left right lb rb ->
    alpha left right (SStep la lb) (SStep ra rb)
| AClose : forall left right lv rv,
    alpha left right lv rv ->
    alpha left right (SClose lv) (SClose rv).