(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Require Import Uni.
Require Import Surf.
Require Import Idx.
Require Import Law.
Require Import Dec.
Require Import Lim.
Require Import Rule.
Require Import Perm.
Require Import Data.
Require Import Rec.
Require Import Quant.
Require Import Weave.
Require Import Braid.
Require Import Loom.
Require Import Orbit.
Require Import Wake.
Require Import Rift.
Require Import Fun.
Require Import Raw.
Require Import Norm.
Require Import Rnom.
Require Import Spec.
Require Import Poly.
Require Import Fhe.
Require Import Param.
Require Import Hop.
Require Import Hfhe.
Require Import Hpar.
Require Import Text.

Import ListNotations.

Inductive lex : Type :=
| LKey : tok -> lex
| LName : nat -> lex
| LNat : nat -> lex
| LHex : list nat -> lex.

Record vocab : Type := Vocab {
  wveil : nat;
  wkey : nat;
  wadd : nat;
  wmul : nat;
  wrenew : nat;
  wstage : nat;
  wprod : nat;
  wparam : nat;
  wroom : nat;
  wstate : nat;
  wterms : nat;
  wslots : nat;
  wquery : nat;
  wenc : nat;
  wtrim : nat
}.

Definition vocab_b (words : vocab) : bool :=
  names_b [] [wveil words; wkey words; wadd words; wmul words;
    wrenew words; wstage words; wprod words; wparam words; wroom words;
    wstate words; wterms words; wslots words; wquery words; wenc words;
    wtrim words].

Definition pout (A : Type) := option (A * list lex).

Definition ltake (want : tok) (input : list lex) : option (list lex) :=
  match input with
  | LKey got :: rest => if tok_beq want got then Some rest else None
  | _ => None
  end.

Definition pname (input : list lex) : pout nat :=
  match input with
  | LName name :: rest => Some (name, rest)
  | _ => None
  end.

Definition pword (want : nat) (input : list lex) : option (list lex) :=
  match input with
  | LName got :: rest => if Nat.eqb want got then Some rest else None
  | _ => None
  end.

Definition pnat (input : list lex) : pout nat :=
  match input with
  | LNat value :: rest => Some (value, rest)
  | _ => None
  end.

Fixpoint pix_add (fuel : nat) (input : list lex) {struct fuel} : pout ix :=
  match fuel with
  | O => None
  | S fuel' =>
      match pix_mul fuel' input with
      | Some (lhs, rest) => pix_add_tail fuel' lhs rest
      | None => None
      end
  end
with pix_add_tail (fuel : nat) (lhs : ix) (input : list lex)
    {struct fuel} : pout ix :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TPlus :: rest =>
          match pix_mul fuel' rest with
          | Some (rhs, next) => pix_add_tail fuel' (IAdd lhs rhs) next
          | None => None
          end
      | LKey TMinus :: rest =>
          match pix_mul fuel' rest with
          | Some (rhs, next) => pix_add_tail fuel' (ISub lhs rhs) next
          | None => None
          end
      | _ => Some (lhs, input)
      end
  end
with pix_mul (fuel : nat) (input : list lex) {struct fuel} : pout ix :=
  match fuel with
  | O => None
  | S fuel' =>
      match pix_atom fuel' input with
      | Some (lhs, rest) => pix_mul_tail fuel' lhs rest
      | None => None
      end
  end
with pix_mul_tail (fuel : nat) (lhs : ix) (input : list lex)
    {struct fuel} : pout ix :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TStar :: rest =>
          match pix_atom fuel' rest with
          | Some (rhs, next) => pix_mul_tail fuel' (IMul lhs rhs) next
          | None => None
          end
      | _ => Some (lhs, input)
      end
  end
with pix_atom (fuel : nat) (input : list lex) {struct fuel} : pout ix :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LNat value :: rest =>
          if ifit value then Some (ILit value, rest) else None
      | LName name :: rest => Some (IVar name, rest)
      | LKey TMax :: LKey TLparen :: rest =>
          match pix_add fuel' rest with
          | Some (lhs, LKey TComma :: next) =>
              match pix_add fuel' next with
              | Some (rhs, LKey TRparen :: tail) =>
                  Some (IMax lhs rhs, tail)
              | _ => None
              end
          | _ => None
          end
      | LKey TLparen :: rest =>
          match pix_add fuel' rest with
          | Some (value, LKey TRparen :: tail) => Some (value, tail)
          | _ => None
          end
      | _ => None
      end
  end.

Definition tenv := list (nat * ty).

Fixpoint dfind (name : nat) (items : list dtype) : option dtype :=
  match items with
  | [] => None
  | item :: rest =>
      if Nat.eqb name (dname item) then Some item else dfind name rest
  end.

Fixpoint rfind (name : nat) (items : list rtype) : option rtype :=
  match items with
  | [] => None
  | item :: rest =>
      if Nat.eqb name (rname item) then Some item else rfind name rest
  end.

Fixpoint tfind (name : nat) (env : tenv) : option ty :=
  match env with
  | [] => None
  | (key, typ) :: rest =>
      if Nat.eqb name key then Some typ else tfind name rest
  end.

Fixpoint thas (name : nat) (env : tenv) : bool :=
  match env with
  | [] => false
  | (key, _) :: rest => Nat.eqb name key || thas name rest
  end.

Definition tput (env : tenv) (name : nat) (typ : ty) : option tenv :=
  if thas name env then None
  else if ty_b typ then Some ((name, typ) :: env)
  else None.

Fixpoint pty (fuel : nat) (env : ienv) (types : tenv)
    (input : list lex) {struct fuel} : pout ty :=
  match fuel with
  | O => None
  | S fuel' =>
      match pty_atom fuel' env types input with
      | Some (lhs, LKey TStar :: rest) =>
          match pty fuel' env types rest with
          | Some (rhs, next) => Some (Uni.TPair lhs rhs, next)
          | None => None
          end
      | other => other
      end
  end
with pty_atom (fuel : nat) (env : ienv) (types : tenv)
    (input : list lex) {struct fuel} : pout ty :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TUnit :: rest => Some (Uni.TUnit, rest)
      | LKey TBool :: rest => Some (Uni.TBool, rest)
      | LKey TInt :: rest => Some (Uni.TInt, rest)
      | LKey TBytes :: LKey TLbrack :: rest =>
          match pix_add fuel' rest with
          | Some (index, LKey TRbrack :: next) =>
              match ieval env index with
              | Some len => Some (Uni.TBytes len, next)
              | None => None
              end
          | _ => None
          end
      | LKey TVec :: LKey TLbrack :: rest =>
          match pix_add fuel' rest with
          | Some (index, LKey TComma :: next) =>
              match ieval env index, pty fuel' env types next with
              | Some len, Some (elem, LKey TRbrack :: tail) =>
                  Some (Uni.TVec len elem, tail)
              | _, _ => None
              end
          | _ => None
          end
      | LKey TCap :: LKey TLbrack :: LNat kind ::
          LKey TRbrack :: rest =>
          if ifit kind then Some (Uni.TCap kind, rest) else None
      | LKey TResult :: LKey TLbrack :: rest =>
          match pty fuel' env types rest with
          | Some (good, LKey TComma :: next) =>
              match pty fuel' env types next with
              | Some (bad, LKey TRbrack :: tail) =>
                  Some (Uni.TSum good bad, tail)
              | _ => None
              end
          | _ => None
          end
      | LName name :: rest =>
          match tfind name types with
          | Some typ => Some (typ, rest)
          | None => None
          end
      | LKey TLparen :: rest =>
          match pty fuel' env types rest with
          | Some (value, LKey TRparen :: tail) => Some (value, tail)
          | _ => None
          end
      | _ => None
      end
  end.

Definition pmode (input : list lex) : pout mul :=
  match input with
  | LKey TErase :: rest => Some (M0, rest)
  | LKey TOnce :: rest => Some (M1, rest)
  | LKey TMany :: rest => Some (MM, rest)
  | _ => None
  end.

Definition pbind (fuel : nat) (env : ienv) (types : tenv)
    (input : list lex) : pout sbind :=
  match pmode input with
  | Some (mode, LName name :: LKey TColon :: rest) =>
      match pty fuel env types rest with
      | Some (typ, next) => Some (SBind name mode typ, next)
      | None => None
      end
  | _ => None
  end.

Fixpoint yhas (name : nat) (vars : list nat) : bool :=
  match vars with
  | [] => false
  | item :: rest => Nat.eqb name item || yhas name rest
  end.

Fixpoint pity (fuel : nat) (vars : list nat) (types : tenv) (input : list lex)
    {struct fuel} : pout ity :=
  match fuel with
  | O => None
  | S fuel' =>
      match pity_atom fuel' vars types input with
      | Some (lhs, LKey TStar :: rest) =>
          match pity fuel' vars types rest with
          | Some (rhs, next) => Some (YPair lhs rhs, next)
          | None => None
          end
      | other => other
      end
  end
with pity_atom (fuel : nat) (vars : list nat) (types : tenv) (input : list lex)
    {struct fuel} : pout ity :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TUnit :: rest => Some (YUnit, rest)
      | LKey TBool :: rest => Some (YBool, rest)
      | LKey TInt :: rest => Some (YInt, rest)
      | LKey TBytes :: LKey TLbrack :: rest =>
          match pix_add fuel' rest with
          | Some (index, LKey TRbrack :: next) =>
              Some (YBytes index, next)
          | _ => None
          end
      | LKey TVec :: LKey TLbrack :: rest =>
          match pix_add fuel' rest with
          | Some (index, LKey TComma :: next) =>
              match pity fuel' vars types next with
              | Some (elem, LKey TRbrack :: tail) =>
                  Some (YVec index elem, tail)
              | _ => None
              end
          | _ => None
          end
      | LKey TCap :: LKey TLbrack :: LNat kind ::
          LKey TRbrack :: rest =>
          if ifit kind then Some (YCap kind, rest) else None
      | LKey TResult :: LKey TLbrack :: rest =>
          match pity fuel' vars types rest with
          | Some (good, LKey TComma :: next) =>
              match pity fuel' vars types next with
              | Some (bad, LKey TRbrack :: tail) =>
                  Some (YSum good bad, tail)
              | _ => None
              end
          | _ => None
          end
      | LName name :: rest =>
          if yhas name vars then Some (YVar name, rest)
          else
            match tfind name types with
            | Some typ =>
                match ylift typ with
                | Some out => Some (out, rest)
                | None => None
                end
            | None => None
            end
      | LKey TLparen :: rest =>
          match pity fuel' vars types rest with
          | Some (value, LKey TRparen :: tail) => Some (value, tail)
          | _ => None
          end
      | _ => None
      end
  end.

Definition prbind (fuel : nat) (vars : list nat) (types : tenv)
    (input : list lex) : pout rbind :=
  match pmode input with
  | Some (mode, LName name :: LKey TColon :: rest) =>
      match pity fuel vars types rest with
      | Some (typ, next) => Some (RBind name mode typ, next)
      | None => None
      end
  | _ => None
  end.

Definition pibind (fuel : nat) (vars : list nat) (types : tenv)
    (input : list lex) : pout ibind :=
  match pmode input with
  | Some (mode, LName name :: LKey TColon :: rest) =>
      match pity fuel vars types rest with
      | Some (typ, next) => Some (IBind name mode typ, next)
      | None => None
      end
  | _ => None
  end.

Definition psize (env : ienv) (input : list lex) : pout ienv :=
  match input with
  | LName key :: LKey TEq :: LNat value :: rest =>
      match iput env key (ILit value) with
      | Some next => Some (next, rest)
      | None => None
      end
  | _ => None
  end.

Definition pmeasure (fuel : nat) (env : ienv)
    (input : list lex) : pout ienv :=
  match input with
  | LName key :: LKey TEq :: rest =>
      match pix_add fuel rest with
      | Some (term, next) =>
          match iput env key term with
          | Some extended => Some (extended, next)
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Definition plaw (fuel : nat) (env : ienv)
    (input : list lex) : option (list lex) :=
  match pix_add fuel input with
  | Some (lhs, LKey TEq :: next) =>
      match pix_add fuel next with
      | Some (rhs, tail) =>
          match ihold env IEq lhs rhs with
          | Some true => Some tail
          | _ => None
          end
      | None => None
      end
  | Some (lhs, LKey TLe :: next) =>
      match pix_add fuel next with
      | Some (rhs, tail) =>
          match ihold env ILe lhs rhs with
          | Some true => Some tail
          | _ => None
          end
      | None => None
      end
  | _ => None
  end.

Definition pperm (input : list lex) : pout (nat * perm) :=
  match input with
  | LKey TCap :: LKey TLbrack :: LNat kind :: LKey TRbrack ::
      LKey TEq :: LKey TStep :: LKey TPlus :: LKey TClose :: rest =>
      Some ((kind, PBoth), rest)
  | LKey TCap :: LKey TLbrack :: LNat kind :: LKey TRbrack ::
      LKey TEq :: LKey TStep :: rest => Some ((kind, PStep), rest)
  | LKey TCap :: LKey TLbrack :: LNat kind :: LKey TRbrack ::
      LKey TEq :: LKey TClose :: rest => Some ((kind, PClose), rest)
  | _ => None
  end.

Definition cenv := list nat.

Fixpoint chas (code : nat) (env : cenv) : bool :=
  match env with
  | [] => false
  | head :: rest => Nat.eqb code head || chas code rest
  end.

Definition cput (env : cenv) (code : nat) : option cenv :=
  if chas code env then None else Some (code :: env).

Fixpoint pbits (fuel value : nat) : option (list bool) :=
  match fuel with
  | O => if Nat.eqb value 0 then Some [] else None
  | S fuel' =>
      match pbits fuel' (Nat.div2 value) with
      | Some rest => Some (Nat.odd value :: rest)
      | None => None
      end
  end.

Definition pctor (fuel : nat) (env : ienv) (types : tenv)
    (input : list lex) : pout ctor :=
  match input with
  | LName name :: LKey TLparen :: rest =>
      match pty fuel env types rest with
      | Some (typ, LKey TRparen :: next) =>
          Some (Ctor name typ, next)
      | _ => None
      end
  | _ => None
  end.

Fixpoint pctors (fuel : nat) (env : ienv) (types : tenv)
    (input : list lex) {struct fuel} : pout (list ctor) :=
  match fuel with
  | O => None
  | S fuel' =>
      match pctor fuel' env types input with
      | Some (item, LKey TBar :: rest) =>
          match pctors fuel' env types rest with
          | Some (items, next) => Some (item :: items, next)
          | None => None
          end
      | Some (item, rest) => Some ([item], rest)
      | None => None
      end
  end.

Record dout : Type := DOut {
  dcode : nat;
  dvalue : dtype;
  dtyp : ty
}.

Definition pdata (fuel : nat) (env : ienv) (types : tenv)
    (input : list lex) : pout dout :=
  match input with
  | LName name :: LKey TTag :: LNat code :: LKey TEq :: rest =>
      match pbits tag_len code, pctors fuel env types rest with
      | Some tag, Some (ctors, next) =>
          let item := DType tag name ctors in
          if decl_b item then
            match dtype_t item with
            | Some typ => Some (DOut code item typ, next)
            | None => None
            end
          else None
      | _, _ => None
      end
  | _ => None
  end.

Definition pfield (fuel : nat) (env : ienv) (types : tenv)
    (input : list lex) : pout rfield :=
  match input with
  | LName name :: LKey TColon :: rest =>
      match pty fuel env types rest with
      | Some (typ, next) => Some (RField name typ, next)
      | None => None
      end
  | _ => None
  end.

Fixpoint pfields (fuel : nat) (env : ienv) (types : tenv)
    (input : list lex) {struct fuel} : pout (list rfield) :=
  match fuel with
  | O => None
  | S fuel' =>
      match pfield fuel' env types input with
      | Some (item, LKey TComma :: rest) =>
          match pfields fuel' env types rest with
          | Some (items, next) => Some (item :: items, next)
          | None => None
          end
      | Some (item, LKey TRbrace :: rest) => Some ([item], rest)
      | _ => None
      end
  end.

Record sout : Type := SOut {
  scode : nat;
  svalue : rtype;
  styp : ty
}.

Definition pshape (fuel : nat) (env : ienv) (types : tenv)
    (input : list lex) : pout sout :=
  match input with
  | LName name :: LKey TTag :: LNat code :: LKey TEq ::
      LKey TLbrace :: rest =>
      match pbits tag_len code, pfields fuel env types rest with
      | Some tag, Some (fields, next) =>
          let item := RType tag name fields in
          if rdecl_b item then
            match rtype_t item with
            | Some typ => Some (SOut code item typ, next)
            | None => None
            end
          else None
      | _, _ => None
      end
  | _ => None
  end.

Definition eparse := list lex -> pout stm.

Fixpoint svec (typ : ty) (items : list stm) : stm :=
  match items with
  | [] => SVnil typ
  | item :: rest => SVcons item (svec typ rest)
  end.

Definition pone (next : eparse) (make : stm -> stm)
    (input : list lex) : pout stm :=
  match input with
  | LKey TLparen :: rest =>
      match next rest with
      | Some (value, LKey TRparen :: tail) => Some (make value, tail)
      | _ => None
      end
  | _ => None
  end.

Definition ptwo (next : eparse) (make : stm -> stm -> stm)
    (input : list lex) : pout stm :=
  match input with
  | LKey TLparen :: rest =>
      match next rest with
      | Some (lhs, LKey TComma :: more) =>
          match next more with
          | Some (rhs, LKey TRparen :: tail) =>
              Some (make lhs rhs, tail)
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition ptyped_one (fuel : nat) (env : ienv) (types : tenv)
    (next : eparse) (make : ty -> stm -> stm)
    (input : list lex) : pout stm :=
  match input with
  | LKey TLbrack :: rest =>
      match pty fuel env types rest with
      | Some (typ, LKey TRbrack :: LKey TLparen :: more) =>
          match next more with
          | Some (value, LKey TRparen :: tail) => Some (make typ value, tail)
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition ptyped_two (fuel : nat) (env : ienv) (types : tenv)
    (next : eparse) (make : ty -> stm -> stm -> stm)
    (input : list lex) : pout stm :=
  match input with
  | LKey TLbrack :: rest =>
      match pty fuel env types rest with
      | Some (typ, LKey TRbrack :: LKey TLparen :: more) =>
          match next more with
          | Some (lhs, LKey TComma :: after) =>
              match next after with
              | Some (rhs, LKey TRparen :: tail) =>
                  Some (make typ lhs rhs, tail)
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition pindexed (next : eparse) (make : nat -> stm -> stm)
    (input : list lex) : pout stm :=
  match input with
  | LKey TLbrack :: LNat index :: LKey TRbrack ::
      LKey TLparen :: rest =>
      if ifit index then
        match next rest with
        | Some (value, LKey TRparen :: tail) => Some (make index value, tail)
        | _ => None
        end
      else None
  | _ => None
  end.

Fixpoint pdarms (fuel : nat) (env : ienv) (types : tenv)
    (next : eparse) (input : list lex) {struct fuel}
    : pout (list Data.arm) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LName name :: rest =>
          match pbind fuel' env types rest with
          | Some (item, LKey TArrow :: body) =>
              match next body with
              | Some (term, LKey TBar :: more) =>
                  match pdarms fuel' env types next more with
                  | Some (items, tail) =>
                      Some (Data.Arm name item term :: items, tail)
                  | None => None
                  end
              | Some (term, LKey TRbrace :: tail) =>
                  Some ([Data.Arm name item term], tail)
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  end.

Fixpoint pritems (fuel : nat) (next : eparse) (input : list lex)
    {struct fuel} : pout (list Rec.ritem) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LName name :: LKey TEq :: rest =>
          match next rest with
          | Some (term, LKey TComma :: more) =>
              match pritems fuel' next more with
              | Some (items, tail) =>
                  Some (Rec.RItem name term :: items, tail)
              | None => None
              end
          | Some (term, LKey TRbrace :: tail) =>
              Some ([Rec.RItem name term], tail)
          | _ => None
          end
      | _ => None
      end
  end.

Fixpoint prpicks (fuel : nat) (env : ienv) (types : tenv)
    (input : list lex) {struct fuel} : pout (list Rec.rpick) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LName name :: LKey TArrow :: rest =>
          match pbind fuel' env types rest with
          | Some (item, LKey TComma :: more) =>
              match prpicks fuel' env types more with
              | Some (items, tail) =>
                  Some (Rec.RPick name item :: items, tail)
              | None => None
              end
          | Some (item, LKey TRbrace :: tail) =>
              Some ([Rec.RPick name item], tail)
          | _ => None
          end
      | _ => None
      end
  end.

Fixpoint pexpr (fuel : nat) (env : ienv) (types : tenv)
    (data : list dtype) (shapes : list rtype)
    (input : list lex) {struct fuel} : pout stm :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TLet :: rest =>
          match pbind fuel' env types rest with
          | Some (item, LKey TEq :: more) =>
              match pexpr fuel' env types data shapes more with
              | Some (value, LKey TIn :: after) =>
                  match pexpr fuel' env types data shapes after with
                  | Some (body, tail) => Some (SLet item value body, tail)
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TSplit :: rest =>
          match pexpr fuel' env types data shapes rest with
          | Some (value, LKey TAs :: after) =>
              match after with
              | LName name :: LKey TLbrace :: fields =>
                  match rfind name shapes with
                  | Some item =>
                      match prpicks fuel' env types fields with
                      | Some (items, LKey TIn :: body) =>
                          match pexpr fuel' env types data shapes body with
                          | Some (out, tail) =>
                              match Rec.rsplit item value items out with
                              | Some term => Some (term, tail)
                              | None => None
                              end
                          | None => None
                          end
                      | _ => None
                      end
                  | None => None
                  end
              | _ =>
                  match pbind fuel' env types after with
                  | Some (lhs, LKey TComma :: more) =>
                      match pbind fuel' env types more with
                      | Some (rhs, LKey TIn :: body) =>
                          match pexpr fuel' env types data shapes body with
                          | Some (out, tail) =>
                              Some (SUnpair value lhs rhs out, tail)
                          | None => None
                          end
                      | _ => None
                      end
                  | _ => None
                  end
              end
          | _ => None
          end
      | LKey TIf :: rest =>
          match pexpr fuel' env types data shapes rest with
          | Some (guard, LKey TThen :: more) =>
              match pexpr fuel' env types data shapes more with
              | Some (yes, LKey TElse :: after) =>
                  match pexpr fuel' env types data shapes after with
                  | Some (no, tail) => Some (SIf guard yes no, tail)
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TCase :: rest =>
          match pexpr fuel' env types data shapes rest with
          | Some (value, after) =>
              match after with
              | LKey TOf :: LKey TGood :: more =>
                  match pbind fuel' env types more with
                  | Some (good, LKey TArrow :: yes) =>
                      match pexpr fuel' env types data shapes yes with
                      | Some (lhs, LKey TBar :: LKey TBad :: more) =>
                          match pbind fuel' env types more with
                          | Some (bad, LKey TArrow :: no) =>
                              match pexpr fuel' env types data shapes no with
                              | Some (rhs, tail) =>
                                  Some (SCase value good lhs bad rhs, tail)
                              | None => None
                              end
                          | _ => None
                          end
                      | _ => None
                      end
                  | _ => None
                  end
              | LKey TAs :: LName name :: LKey TOf ::
                  LKey TLbrace :: arms =>
                  match dfind name data with
                  | Some item =>
                      match pdarms fuel' env types
                          (pexpr fuel' env types data shapes) arms with
                      | Some (items, tail) =>
                          match Data.dcase item value items with
                          | Some term => Some (term, tail)
                          | None => None
                          end
                      | None => None
                      end
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TWeave :: LKey TLbrack :: rest =>
          match pix_add fuel' rest with
          | Some (raw_count, LKey TComma :: more) =>
              match ieval env raw_count, pty fuel' env types more with
              | Some count, Some (out, LKey TRbrack :: source) =>
                  match pexpr fuel' env types data shapes source with
                  | Some (value, LKey TWith :: bind) =>
                      match pbind fuel' env types bind with
                      | Some (item, LKey TArrow :: body) =>
                          match pexpr fuel' env types data shapes body with
                          | Some (term, tail) =>
                              match Weave.wterm (did 0) count out value item term with
                              | Some result => Some (result, tail)
                              | None => None
                              end
                          | None => None
                          end
                      | _ => None
                      end
                  | _ => None
                  end
              | _, _ => None
              end
          | _ => None
          end
      | LKey TBraid :: LKey TLbrack :: rest =>
          match pix_add fuel' rest with
          | Some (raw_count, LKey TComma :: more) =>
              match ieval env raw_count, pty fuel' env types more with
              | Some count, Some (out, LKey TRbrack :: lsrc) =>
                  match pexpr fuel' env types data shapes lsrc with
                  | Some (lhs, LKey TComma :: rsrc) =>
                      match pexpr fuel' env types data shapes rsrc with
                      | Some (rhs, LKey TWith :: first) =>
                          match pbind fuel' env types first with
                          | Some (one, LKey TComma :: second) =>
                              match pbind fuel' env types second with
                              | Some (two, LKey TArrow :: body) =>
                                  match pexpr fuel' env types data shapes body with
                                  | Some (term, tail) =>
                                      match Braid.bterm (did 0) (did 1) count
                                          out lhs rhs one two term with
                                      | Some result => Some (result, tail)
                                      | None => None
                                      end
                                  | None => None
                                  end
                              | _ => None
                              end
                          | _ => None
                          end
                      | _ => None
                      end
                  | _ => None
                  end
              | _, _ => None
              end
          | _ => None
          end
      | LKey TLoom :: LKey TLbrack :: rest =>
          match pix_add fuel' rest with
          | Some (raw_count, LKey TComma :: more) =>
              match ieval env raw_count, pty fuel' env types more with
              | Some count, Some (out, LKey TRbrack :: LKey TWith :: bind) =>
                  match pbind fuel' env types bind with
                  | Some (item, LKey TArrow :: body) =>
                      match pexpr fuel' env types data shapes body with
                      | Some (term, tail) =>
                          match Loom.lterm count out item term with
                          | Some result => Some (result, tail)
                          | None => None
                          end
                      | None => None
                      end
                  | _ => None
                  end
              | _, _ => None
              end
          | _ => None
          end
      | LKey TOrbit :: LKey TLbrack :: rest =>
          match pix_add fuel' rest with
          | Some (raw_count, LKey TRbrack :: LKey TFrom :: seed) =>
              match ieval env raw_count with
              | Some count =>
                  match pexpr fuel' env types data shapes seed with
                  | Some (value, LKey TWith :: bind) =>
                      match pbind fuel' env types bind with
                      | Some (item, LKey TArrow :: body) =>
                          match pexpr fuel' env types data shapes body with
                          | Some (term, tail) =>
                              match Orbit.oterm count value item term with
                              | Some result => Some (result, tail)
                              | None => None
                              end
                          | None => None
                          end
                      | _ => None
                      end
                  | _ => None
                  end
              | None => None
              end
          | _ => None
          end
      | LKey TWake :: LKey TLbrack :: rest =>
          match pix_add fuel' rest with
          | Some (raw_count, LKey TRbrack :: LKey TFrom :: seed) =>
              match ieval env raw_count with
              | Some count =>
                  match pexpr fuel' env types data shapes seed with
                  | Some (value, LKey TWith :: bind) =>
                      match pbind fuel' env types bind with
                      | Some (item, LKey TArrow :: body) =>
                          match pexpr fuel' env types data shapes body with
                          | Some (term, tail) =>
                              match Wake.kterm (did 0) count value item term with
                              | Some result => Some (result, tail)
                              | None => None
                              end
                          | None => None
                          end
                      | _ => None
                      end
                  | _ => None
                  end
              | None => None
              end
          | _ => None
          end
      | LKey TRift :: LKey TLbrack :: input =>
          match pix_add fuel' input with
          | Some (raw_cut, LKey TComma :: input) =>
              match pix_add fuel' input with
              | Some (raw_rest, LKey TComma :: input) =>
                  match ieval env raw_cut, ieval env raw_rest,
                      pty fuel' env types input with
                  | Some cut, Some rest,
                      Some (elem, LKey TRbrack :: LKey TLparen :: source) =>
                      match pexpr fuel' env types data shapes source with
                      | Some (value, LKey TRparen :: tail) =>
                          match Rift.rift_make cut rest elem value with
                          | Some result => Some (result, tail)
                          | None => None
                          end
                      | _ => None
                      end
                  | _, _, _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | _ => padd fuel' env types data shapes input
      end
  end
with padd (fuel : nat) (env : ienv) (types : tenv)
    (data : list dtype) (shapes : list rtype)
    (input : list lex) {struct fuel} : pout stm :=
  match fuel with
  | O => None
  | S fuel' =>
      match pmul fuel' env types data shapes input with
      | Some (lhs, rest) => padd_tail fuel' env types data shapes lhs rest
      | None => None
      end
  end
with padd_tail (fuel : nat) (env : ienv) (types : tenv)
    (data : list dtype) (shapes : list rtype)
    (lhs : stm) (input : list lex) {struct fuel} : pout stm :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TPlus :: rest =>
          match pmul fuel' env types data shapes rest with
          | Some (rhs, next) =>
              padd_tail fuel' env types data shapes (SAdd lhs rhs) next
          | None => None
          end
      | LKey TMinus :: rest =>
          match pmul fuel' env types data shapes rest with
          | Some (rhs, next) =>
              padd_tail fuel' env types data shapes (SSub lhs rhs) next
          | None => None
          end
      | _ => Some (lhs, input)
      end
  end
with pmul (fuel : nat) (env : ienv) (types : tenv)
    (data : list dtype) (shapes : list rtype)
    (input : list lex) {struct fuel} : pout stm :=
  match fuel with
  | O => None
  | S fuel' =>
      match patom fuel' env types data shapes input with
      | Some (lhs, rest) => pmul_tail fuel' env types data shapes lhs rest
      | None => None
      end
  end
with pmul_tail (fuel : nat) (env : ienv) (types : tenv)
    (data : list dtype) (shapes : list rtype)
    (lhs : stm) (input : list lex) {struct fuel} : pout stm :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TStar :: rest =>
          match patom fuel' env types data shapes rest with
          | Some (rhs, next) =>
              pmul_tail fuel' env types data shapes (SMul lhs rhs) next
          | None => None
          end
      | LKey TSlash :: rest =>
          match patom fuel' env types data shapes rest with
          | Some (rhs, next) =>
              pmul_tail fuel' env types data shapes (SDiv lhs rhs) next
          | None => None
          end
      | LKey TPercent :: rest =>
          match patom fuel' env types data shapes rest with
          | Some (rhs, next) =>
              pmul_tail fuel' env types data shapes (SMod lhs rhs) next
          | None => None
          end
      | _ => Some (lhs, input)
      end
  end
with patom (fuel : nat) (env : ienv) (types : tenv)
    (data : list dtype) (shapes : list rtype)
    (input : list lex) {struct fuel} : pout stm :=
  match fuel with
  | O => None
  | S fuel' =>
      let next := pexpr fuel' env types data shapes in
      match input with
      | LNat value :: rest =>
          Some (SK (VInt (Z.of_nat value)) Uni.TInt, rest)
      | LKey TMinus :: LNat value :: rest =>
          Some (SK (VInt (Z.opp (Z.of_nat value))) Uni.TInt, rest)
      | LKey TMinus :: rest =>
          match patom fuel' env types data shapes rest with
          | Some (value, tail) => Some (SNeg value, tail)
          | None => None
          end
      | LHex value :: rest => Some (SBytes value, rest)
      | LKey TTrue :: rest => Some (SK (VBool true) Uni.TBool, rest)
      | LKey TFalse :: rest => Some (SK (VBool false) Uni.TBool, rest)
      | LKey TUnit :: rest => Some (SK VUnit Uni.TUnit, rest)
      | LName name :: rest => Some (SVar name, rest)
      | LKey TLparen :: LKey TRparen :: rest =>
          Some (SK VUnit Uni.TUnit, rest)
      | LKey TLparen :: rest =>
          match next rest with
          | Some (lhs, LKey TComma :: more) =>
              match next more with
              | Some (rhs, LKey TRparen :: tail) =>
                  Some (SPair lhs rhs, tail)
              | _ => None
              end
          | Some (value, LKey TRparen :: tail) => Some (value, tail)
          | _ => None
          end
      | LKey TVec :: LKey TLbrack :: rest =>
          match pty fuel' env types rest with
          | Some (typ, LKey TRbrack :: LKey TLparen :: more) =>
              match pvals fuel' env types data shapes more with
              | Some (items, tail) => Some (svec typ items, tail)
              | None => None
              end
          | _ => None
          end
      | LKey TMake :: LName name :: rest =>
          match dfind name data, rfind name shapes with
          | Some item, _ =>
              match rest with
              | LName ctor :: LKey TLparen :: more =>
                  match next more with
                  | Some (value, LKey TRparen :: tail) =>
                      match Data.make item ctor value with
                      | Some term => Some (term, tail)
                      | None => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | None, Some item =>
              match rest with
              | LKey TLbrace :: fields =>
                  match pritems fuel' next fields with
                  | Some (items, tail) =>
                      match Rec.rmake item items with
                      | Some term => Some (term, tail)
                      | None => None
                      end
                  | None => None
                  end
              | _ => None
              end
          | None, None => None
          end
      | LKey TFst :: rest => pone next SFst rest
      | LKey TSnd :: rest => pone next SSnd rest
      | LKey TUncons :: rest => pone next SUncons rest
      | LKey TAbs :: rest => pone next SAbs rest
      | LKey TCat :: rest => ptwo next SCat rest
      | LKey TVcat :: rest => ptwo next SVcat rest
      | LKey TStep :: rest => ptwo next SStep rest
      | LKey TEqual :: rest => ptyped_two fuel' env types next SEq rest
      | LKey TGood :: rest =>
          ptyped_one fuel' env types next (fun bad value => SInl value bad) rest
      | LKey TBad :: rest =>
          ptyped_one fuel' env types next SInr rest
      | LKey TTake :: rest => pindexed next STake rest
      | LKey TDrop :: rest => pindexed next SDrop rest
      | LKey TAt :: rest => pindexed next SAt rest
      | LKey TRead :: rest =>
          pindexed next (fun kind value => SAct (Uni.ARead kind) value) rest
      | LKey TWrite :: rest =>
          pindexed next (fun kind value => SAct (Uni.AWrite kind) value) rest
      | LKey TEmit :: rest =>
          pindexed next (fun kind value => SAct (Uni.AEmit kind) value) rest
      | LKey TFail :: rest =>
          pindexed next (fun kind value => SAct (Uni.AFail kind) value) rest
      | LKey TClose :: LKey TLbrack :: rest =>
          pindexed next (fun kind value => SAct (Uni.AClose kind) value)
            (LKey TLbrack :: rest)
      | LKey TClose :: rest => pone next SClose rest
      | _ => None
      end
  end
with pvals (fuel : nat) (env : ienv) (types : tenv)
    (data : list dtype) (shapes : list rtype)
    (input : list lex) {struct fuel} : pout (list stm) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TRparen :: rest => Some ([], rest)
      | _ =>
          match pexpr fuel' env types data shapes input with
          | Some (item, LKey TComma :: more) =>
              match pvals fuel' env types data shapes more with
              | Some (items, tail) => Some (item :: items, tail)
              | None => None
              end
          | Some (item, LKey TRparen :: rest) => Some ([item], rest)
          | _ => None
          end
      end
  end.

Fixpoint rvec (typ : ity) (items : list rtm) : rtm :=
  match items with
  | [] => RVnil typ
  | item :: rest => RVcons item (rvec typ rest)
  end.

Definition rpone (next : list lex -> pout rtm) (make : rtm -> rtm)
    (input : list lex) : pout rtm :=
  match input with
  | LKey TLparen :: rest =>
      match next rest with
      | Some (value, LKey TRparen :: tail) => Some (make value, tail)
      | _ => None
      end
  | _ => None
  end.

Definition rptwo (next : list lex -> pout rtm)
    (make : rtm -> rtm -> rtm) (input : list lex) : pout rtm :=
  match input with
  | LKey TLparen :: rest =>
      match next rest with
      | Some (lhs, LKey TComma :: more) =>
          match next more with
          | Some (rhs, LKey TRparen :: tail) =>
              Some (make lhs rhs, tail)
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition rptyped_one (fuel : nat) (vars : list nat) (types : tenv)
    (next : list lex -> pout rtm) (make : ity -> rtm -> rtm)
    (input : list lex) : pout rtm :=
  match input with
  | LKey TLbrack :: rest =>
      match pity fuel vars types rest with
      | Some (typ, LKey TRbrack :: LKey TLparen :: more) =>
          match next more with
          | Some (value, LKey TRparen :: tail) => Some (make typ value, tail)
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition rptyped_two (fuel : nat) (vars : list nat) (types : tenv)
    (next : list lex -> pout rtm) (make : ity -> rtm -> rtm -> rtm)
    (input : list lex) : pout rtm :=
  match input with
  | LKey TLbrack :: rest =>
      match pity fuel vars types rest with
      | Some (typ, LKey TRbrack :: LKey TLparen :: more) =>
          match next more with
          | Some (lhs, LKey TComma :: after) =>
              match next after with
              | Some (rhs, LKey TRparen :: tail) =>
                  Some (make typ lhs rhs, tail)
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition rpindexed (next : list lex -> pout rtm)
    (make : nat -> rtm -> rtm) (input : list lex) : pout rtm :=
  match input with
  | LKey TLbrack :: LNat index :: LKey TRbrack ::
      LKey TLparen :: rest =>
      if ifit index then
        match next rest with
        | Some (value, LKey TRparen :: tail) => Some (make index value, tail)
        | _ => None
        end
      else None
  | _ => None
  end.

Fixpoint prnpicks (fuel : nat) (vars : list nat) (types : tenv)
    (input : list lex)
    {struct fuel} : pout (list npick) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LName name :: LKey TArrow :: rest =>
          match prbind fuel' vars types rest with
          | Some (item, LKey TComma :: more) =>
              match prnpicks fuel' vars types more with
              | Some (items, tail) =>
                  Some (NPick name item :: items, tail)
              | None => None
              end
          | Some (item, LKey TRbrace :: tail) =>
              Some ([NPick name item], tail)
          | _ => None
          end
      | _ => None
      end
  end.

Definition nraw (value : option rtm) : rtm :=
  match value with
  | Some term => term
  | None => RReject
  end.

Fixpoint prexpr (fuel : nat) (vars : list nat) (types : tenv)
    (data : list dtype) (shapes : list rtype) (input : list lex)
    {struct fuel} : pout rtm :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TLet :: rest =>
          match prbind fuel' vars types rest with
          | Some (item, LKey TEq :: more) =>
              match prexpr fuel' vars types data shapes more with
              | Some (value, LKey TIn :: after) =>
                  match prexpr fuel' vars types data shapes after with
                  | Some (body, tail) => Some (RLet item value body, tail)
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TSplit :: rest =>
          match prexpr fuel' vars types data shapes rest with
          | Some (value, LKey TAs :: after) =>
              match after with
              | LName name :: LKey TLbrace :: fields =>
                  match rfind name shapes with
                  | Some item =>
                      match prnpicks fuel' vars types fields with
                      | Some (items, LKey TIn :: body) =>
                          match prexpr fuel' vars types data shapes body with
                          | Some (out, tail) =>
                              Some (nraw (nrsplit item value items out), tail)
                          | None => None
                          end
                      | _ => None
                      end
                  | None => None
                  end
              | _ =>
                  match prbind fuel' vars types after with
                  | Some (lhs, LKey TComma :: more) =>
                      match prbind fuel' vars types more with
                      | Some (rhs, LKey TIn :: body) =>
                          match prexpr fuel' vars types data shapes body with
                          | Some (out, tail) =>
                              Some (RUnpair value lhs rhs out, tail)
                          | None => None
                          end
                      | _ => None
                      end
                  | _ => None
                  end
              end
          | _ => None
          end
      | LKey TIf :: rest =>
          match prexpr fuel' vars types data shapes rest with
          | Some (guard, LKey TThen :: more) =>
              match prexpr fuel' vars types data shapes more with
              | Some (yes, LKey TElse :: after) =>
                  match prexpr fuel' vars types data shapes after with
                  | Some (no, tail) => Some (RIf guard yes no, tail)
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TCase :: rest =>
          match prexpr fuel' vars types data shapes rest with
          | Some (value, after) =>
              match after with
              | LKey TOf :: LKey TGood :: more =>
                  match prbind fuel' vars types more with
                  | Some (good, LKey TArrow :: yes) =>
                      match prexpr fuel' vars types data shapes yes with
                      | Some (lhs, LKey TBar :: LKey TBad :: more) =>
                          match prbind fuel' vars types more with
                          | Some (bad, LKey TArrow :: no) =>
                              match prexpr fuel' vars types data shapes no with
                              | Some (rhs, tail) =>
                                  Some (RCase value good lhs bad rhs, tail)
                              | None => None
                              end
                          | _ => None
                          end
                      | _ => None
                      end
                  | _ => None
                  end
              | LKey TAs :: LName name :: LKey TOf ::
                  LKey TLbrace :: arms =>
                  match dfind name data with
                  | Some item =>
                      match prnarms fuel' vars types data shapes arms with
                      | Some (items, tail) =>
                          Some (nraw (ncase item value items), tail)
                      | None => None
                      end
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TFold :: rest =>
          match prexpr fuel' vars types data shapes rest with
          | Some (source, LKey TFrom :: seed) =>
              match prexpr fuel' vars types data shapes seed with
              | Some (init, LKey TWith :: first) =>
                  match prbind fuel' vars types first with
                  | Some (item, LKey TComma :: second) =>
                      match prbind fuel' vars types second with
                      | Some (state, LKey TArrow :: body) =>
                          match prexpr fuel' vars types data shapes body with
                          | Some (term, tail) =>
                              Some (RFoldI source init item state term, tail)
                          | None => None
                          end
                      | _ => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TEvery :: rest =>
          match prexpr fuel' vars types data shapes rest with
          | Some (source, LKey TWith :: bind) =>
              match prbind fuel' vars types bind with
              | Some (item, LKey TArrow :: body) =>
                  match prexpr fuel' vars types data shapes body with
                  | Some (term, tail) =>
                      Some (RQuant QEvery source item term, tail)
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TSome :: rest =>
          match prexpr fuel' vars types data shapes rest with
          | Some (source, LKey TWith :: bind) =>
              match prbind fuel' vars types bind with
              | Some (item, LKey TArrow :: body) =>
                  match prexpr fuel' vars types data shapes body with
                  | Some (term, tail) =>
                      Some (RQuant QSome source item term, tail)
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TCount :: rest =>
          match prexpr fuel' vars types data shapes rest with
          | Some (source, LKey TWith :: bind) =>
              match prbind fuel' vars types bind with
              | Some (item, LKey TArrow :: body) =>
                  match prexpr fuel' vars types data shapes body with
                  | Some (term, tail) =>
                      Some (RQuant QCount source item term, tail)
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TTotal :: rest =>
          match prexpr fuel' vars types data shapes rest with
          | Some (source, LKey TWith :: bind) =>
              match prbind fuel' vars types bind with
              | Some (item, LKey TArrow :: body) =>
                  match prexpr fuel' vars types data shapes body with
                  | Some (term, tail) =>
                      Some (RQuant QSum source item term, tail)
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TWeave :: LKey TLbrack :: rest =>
          match pix_add fuel' rest with
          | Some (raw_count, LKey TComma :: more) =>
              match pity fuel' vars types more with
              | Some (raw_out, LKey TRbrack :: source) =>
                  match prexpr fuel' vars types data shapes source with
                  | Some (value, LKey TWith :: bind) =>
                      match prbind fuel' vars types bind with
                      | Some (item, LKey TArrow :: body) =>
                          match prexpr fuel' vars types data shapes body with
                          | Some (term, tail) =>
                              Some (RWeave raw_count raw_out value item term,
                                tail)
                          | None => None
                          end
                      | _ => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TBraid :: LKey TLbrack :: rest =>
          match pix_add fuel' rest with
          | Some (raw_count, LKey TComma :: more) =>
              match pity fuel' vars types more with
              | Some (raw_out, LKey TRbrack :: left_input) =>
                  match prexpr fuel' vars types data shapes left_input with
                  | Some (lhs, LKey TComma :: right_input) =>
                      match prexpr fuel' vars types data shapes right_input with
                      | Some (rhs, LKey TWith :: first) =>
                          match prbind fuel' vars types first with
                          | Some (one, LKey TComma :: second) =>
                              match prbind fuel' vars types second with
                              | Some (two, LKey TArrow :: body) =>
                                  match prexpr fuel' vars types data shapes body with
                                  | Some (term, tail) =>
                                      Some (RBraid raw_count raw_out lhs rhs
                                        one two term, tail)
                                  | None => None
                                  end
                              | _ => None
                              end
                          | _ => None
                          end
                      | _ => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TLoom :: LKey TLbrack :: rest =>
          match pix_add fuel' rest with
          | Some (raw_count, LKey TComma :: more) =>
              match pity fuel' vars types more with
              | Some (raw_out, LKey TRbrack :: LKey TWith :: bind) =>
                  match prbind fuel' vars types bind with
                  | Some (item, LKey TArrow :: body) =>
                      match prexpr fuel' vars types data shapes body with
                      | Some (term, tail) =>
                          Some (RLoom raw_count raw_out item term, tail)
                      | None => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TOrbit :: LKey TLbrack :: rest =>
          match pix_add fuel' rest with
          | Some (raw_count, LKey TRbrack :: LKey TFrom :: seed) =>
              match prexpr fuel' vars types data shapes seed with
              | Some (value, LKey TWith :: bind) =>
                  match prbind fuel' vars types bind with
                  | Some (item, LKey TArrow :: body) =>
                      match prexpr fuel' vars types data shapes body with
                      | Some (term, tail) =>
                          Some (ROrbit raw_count value item term, tail)
                      | None => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TWake :: LKey TLbrack :: rest =>
          match pix_add fuel' rest with
          | Some (raw_count, LKey TRbrack :: LKey TFrom :: seed) =>
              match prexpr fuel' vars types data shapes seed with
              | Some (value, LKey TWith :: bind) =>
                  match prbind fuel' vars types bind with
                  | Some (item, LKey TArrow :: body) =>
                      match prexpr fuel' vars types data shapes body with
                      | Some (term, tail) =>
                          Some (RWake raw_count value item term, tail)
                      | None => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TRift :: LKey TLbrack :: input =>
          match pix_add fuel' input with
          | Some (raw_cut, LKey TComma :: input) =>
              match pix_add fuel' input with
              | Some (raw_rest, LKey TComma :: input) =>
                  match pity fuel' vars types input with
                  | Some (elem, LKey TRbrack :: LKey TLparen :: source) =>
                      match prexpr fuel' vars types data shapes source with
                      | Some (value, LKey TRparen :: tail) =>
                          Some (RRift raw_cut raw_rest elem value, tail)
                      | _ => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | _ => pradd fuel' vars types data shapes input
      end
  end
with pradd (fuel : nat) (vars : list nat) (types : tenv)
    (data : list dtype) (shapes : list rtype) (input : list lex)
    {struct fuel} : pout rtm :=
  match fuel with
  | O => None
  | S fuel' =>
      match prmul fuel' vars types data shapes input with
      | Some (lhs, rest) => pradd_tail fuel' vars types data shapes lhs rest
      | None => None
      end
  end
with pradd_tail (fuel : nat) (vars : list nat) (types : tenv)
    (data : list dtype) (shapes : list rtype) (lhs : rtm)
    (input : list lex) {struct fuel} : pout rtm :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TPlus :: rest =>
          match prmul fuel' vars types data shapes rest with
          | Some (rhs, next) =>
              pradd_tail fuel' vars types data shapes (RAdd lhs rhs) next
          | None => None
          end
      | LKey TMinus :: rest =>
          match prmul fuel' vars types data shapes rest with
          | Some (rhs, next) =>
              pradd_tail fuel' vars types data shapes (RSub lhs rhs) next
          | None => None
          end
      | _ => Some (lhs, input)
      end
  end
with prmul (fuel : nat) (vars : list nat) (types : tenv)
    (data : list dtype) (shapes : list rtype) (input : list lex)
    {struct fuel} : pout rtm :=
  match fuel with
  | O => None
  | S fuel' =>
      match pratom fuel' vars types data shapes input with
      | Some (lhs, rest) => prmul_tail fuel' vars types data shapes lhs rest
      | None => None
      end
  end
with prmul_tail (fuel : nat) (vars : list nat) (types : tenv)
    (data : list dtype) (shapes : list rtype) (lhs : rtm)
    (input : list lex) {struct fuel} : pout rtm :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TStar :: rest =>
          match pratom fuel' vars types data shapes rest with
          | Some (rhs, next) =>
              prmul_tail fuel' vars types data shapes (RMul lhs rhs) next
          | None => None
          end
      | LKey TSlash :: rest =>
          match pratom fuel' vars types data shapes rest with
          | Some (rhs, next) =>
              prmul_tail fuel' vars types data shapes (RDiv lhs rhs) next
          | None => None
          end
      | LKey TPercent :: rest =>
          match pratom fuel' vars types data shapes rest with
          | Some (rhs, next) =>
              prmul_tail fuel' vars types data shapes (RMod lhs rhs) next
          | None => None
          end
      | _ => Some (lhs, input)
      end
  end
with pratom (fuel : nat) (vars : list nat) (types : tenv)
    (data : list dtype) (shapes : list rtype) (input : list lex)
    {struct fuel} : pout rtm :=
  match fuel with
  | O => None
  | S fuel' =>
      let next := prexpr fuel' vars types data shapes in
      match input with
      | LNat value :: rest => Some (RInt (Z.of_nat value), rest)
      | LKey TMinus :: LNat value :: rest =>
          Some (RInt (Z.opp (Z.of_nat value)), rest)
      | LKey TMinus :: rest =>
          match pratom fuel' vars types data shapes rest with
          | Some (value, tail) => Some (RNeg value, tail)
          | None => None
          end
      | LHex value :: rest => Some (RBytes value, rest)
      | LKey TTrue :: rest => Some (RBool true, rest)
      | LKey TFalse :: rest => Some (RBool false, rest)
      | LKey TUnit :: rest => Some (RUnit, rest)
      | LName name :: rest => Some (RVar name, rest)
      | LKey TLparen :: LKey TRparen :: rest => Some (RUnit, rest)
      | LKey TLparen :: rest =>
          match next rest with
          | Some (lhs, LKey TComma :: more) =>
              match next more with
              | Some (rhs, LKey TRparen :: tail) =>
                  Some (RPair lhs rhs, tail)
              | _ => None
              end
          | Some (value, LKey TRparen :: tail) => Some (value, tail)
          | _ => None
          end
      | LKey TVec :: LKey TLbrack :: rest =>
          match pity fuel' vars types rest with
          | Some (typ, LKey TRbrack :: LKey TLparen :: more) =>
              match prvals fuel' vars types data shapes more with
              | Some (items, tail) => Some (rvec typ items, tail)
              | None => None
              end
          | _ => None
          end
      | LKey TMake :: LName name :: rest =>
          match dfind name data, rfind name shapes with
          | Some item, _ =>
              match rest with
              | LName ctor :: LKey TLparen :: more =>
                  match next more with
                  | Some (value, LKey TRparen :: tail) =>
                      Some (nraw (nmake item ctor value), tail)
                  | _ => None
                  end
              | _ => None
              end
          | None, Some item =>
              match rest with
              | LKey TLbrace :: fields =>
                  match prnitems fuel' vars types data shapes fields with
                  | Some (items, tail) =>
                      Some (nraw (nrmake item items), tail)
                  | None => None
                  end
              | _ => None
              end
          | None, None => None
          end
      | LKey TFst :: rest => rpone next RFst rest
      | LKey TSnd :: rest => rpone next RSnd rest
      | LKey TUncons :: rest => rpone next RUncons rest
      | LKey TAbs :: rest => rpone next RAbs rest
      | LKey TCat :: rest => rptwo next RCat rest
      | LKey TVcat :: rest => rptwo next RVcat rest
      | LKey TStep :: rest => rptwo next RStep rest
      | LKey TEqual :: rest =>
          rptyped_two fuel' vars types next REq rest
      | LKey TGood :: rest =>
          rptyped_one fuel' vars types next (fun bad value => RInl value bad) rest
      | LKey TBad :: rest =>
          rptyped_one fuel' vars types next RInr rest
      | LKey TTake :: rest => rpindexed next RTake rest
      | LKey TDrop :: rest => rpindexed next RDrop rest
      | LKey TAt :: rest => rpindexed next RAt rest
      | LKey TRead :: rest =>
          rpindexed next (fun kind value => RAct (Uni.ARead kind) value) rest
      | LKey TWrite :: rest =>
          rpindexed next (fun kind value => RAct (Uni.AWrite kind) value) rest
      | LKey TEmit :: rest =>
          rpindexed next (fun kind value => RAct (Uni.AEmit kind) value) rest
      | LKey TFail :: rest =>
          rpindexed next (fun kind value => RAct (Uni.AFail kind) value) rest
      | LKey TClose :: LKey TLbrack :: rest =>
          rpindexed next (fun kind value => RAct (Uni.AClose kind) value)
            (LKey TLbrack :: rest)
      | LKey TClose :: rest => rpone next RClose rest
      | _ => None
      end
  end
with prvals (fuel : nat) (vars : list nat) (types : tenv)
    (data : list dtype) (shapes : list rtype) (input : list lex)
    {struct fuel} : pout (list rtm) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TRparen :: rest => Some ([], rest)
      | _ =>
          match prexpr fuel' vars types data shapes input with
          | Some (item, LKey TComma :: more) =>
              match prvals fuel' vars types data shapes more with
              | Some (items, tail) => Some (item :: items, tail)
              | None => None
              end
          | Some (item, LKey TRparen :: rest) => Some ([item], rest)
          | _ => None
          end
      end
  end
with prnarms (fuel : nat) (vars : list nat) (types : tenv)
    (data : list dtype) (shapes : list rtype) (input : list lex)
    {struct fuel} : pout (list narm) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LName name :: rest =>
          match prbind fuel' vars types rest with
          | Some (item, LKey TArrow :: body) =>
              match prexpr fuel' vars types data shapes body with
              | Some (term, LKey TBar :: more) =>
                  match prnarms fuel' vars types data shapes more with
                  | Some (items, tail) =>
                      Some (NArm name item term :: items, tail)
                  | None => None
                  end
              | Some (term, LKey TRbrace :: tail) =>
                  Some ([NArm name item term], tail)
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  end
with prnitems (fuel : nat) (vars : list nat) (types : tenv)
    (data : list dtype) (shapes : list rtype) (input : list lex)
    {struct fuel} : pout (list nitem) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LName name :: LKey TEq :: rest =>
          match prexpr fuel' vars types data shapes rest with
          | Some (term, LKey TComma :: more) =>
              match prnitems fuel' vars types data shapes more with
              | Some (items, tail) =>
                  Some (NItem name term :: items, tail)
              | None => None
              end
          | Some (term, LKey TRbrace :: tail) =>
              Some ([NItem name term], tail)
          | _ => None
          end
      | _ => None
      end
  end.

Definition pelab (fuel : nat) (env : ienv) (types : tenv)
    (data : list dtype) (shapes : list rtype) (scope : list sbind)
    (input : list lex) : pout stm :=
  match prexpr fuel [] types data shapes input with
  | Some (raw, rest) =>
      match nelab env scope raw with
      | Some term => Some (term, rest)
      | None => None
      end
  | None => None
  end.

Definition atag (action : atom) : nat :=
  match action with
  | Uni.ARead _ => 0 | Uni.AWrite _ => 1 | Uni.AEmit _ => 2
  | Uni.AFail _ => 3 | Uni.AClose _ => 4
  end.

Definition aid (action : atom) : nat :=
  match action with
  | Uni.ARead kind | Uni.AWrite kind | Uni.AEmit kind
  | Uni.AFail kind | Uni.AClose kind => kind
  end.

Definition aleb (left right : atom) : bool :=
  Nat.ltb (atag left) (atag right)
    || (Nat.eqb (atag left) (atag right) && Nat.leb (aid left) (aid right)).

Fixpoint ains (action : atom) (row : list atom) : list atom :=
  match row with
  | [] => [action]
  | item :: rest =>
      if aleb action item then action :: row else item :: ains action rest
  end.

Definition pmark (input : list lex) : pout atom :=
  match input with
  | LKey TRead :: LKey TLbrack :: LNat kind :: LKey TRbrack :: rest =>
      if ifit kind then Some (Uni.ARead kind, rest) else None
  | LKey TWrite :: LKey TLbrack :: LNat kind :: LKey TRbrack :: rest =>
      if ifit kind then Some (Uni.AWrite kind, rest) else None
  | LKey TEmit :: LKey TLbrack :: LNat kind :: LKey TRbrack :: rest =>
      if ifit kind then Some (Uni.AEmit kind, rest) else None
  | LKey TFail :: LKey TLbrack :: LNat kind :: LKey TRbrack :: rest =>
      if ifit kind then Some (Uni.AFail kind, rest) else None
  | LKey TClose :: LKey TLbrack :: LNat kind :: LKey TRbrack :: rest =>
      if ifit kind then Some (Uni.AClose kind, rest) else None
  | _ => None
  end.

Fixpoint pmarks (fuel : nat) (row : list atom) (input : list lex)
    {struct fuel} : pout (list atom) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TRbrace :: rest => Some (row, rest)
      | _ =>
          match pmark input with
          | Some (action, LKey TComma :: more) =>
              if has_atom action row then None
              else pmarks fuel' (ains action row) more
          | Some (action, LKey TRbrace :: rest) =>
              if has_atom action row then None
              else Some (ains action row, rest)
          | _ => None
          end
      end
  end.

Definition punder (input : list lex) : pout res :=
  match input with
  | LKey TUnder :: LKey TLbrace ::
      LKey TSteps :: LKey TLbrack :: LNat steps :: LKey TRbrack ::
      LKey TComma :: LKey TDepth :: LKey TLbrack :: LNat depth ::
      LKey TRbrack :: LKey TComma :: LKey TWork :: LKey TLbrack ::
      LNat work :: LKey TRbrack :: LKey TRbrace :: rest =>
      if ifit steps && ifit depth && ifit work
      then Some (Res steps depth work, rest)
      else None
  | _ => None
  end.

Fixpoint pcaps (fuel : nat) (env : ienv) (types : tenv)
    (input : list lex) {struct fuel} : pout (list sbind) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TRbrack :: rest => Some ([], rest)
      | _ =>
          match pbind fuel' env types input with
          | Some (item, LKey TComma :: more) =>
              match pcaps fuel' env types more with
              | Some (items, tail) => Some (item :: items, tail)
              | None => None
              end
          | Some (item, LKey TRbrack :: rest) => Some ([item], rest)
          | _ => None
          end
      end
  end.

Definition pform (fuel : nat) (env : ienv) (types : tenv)
    (data : list dtype) (shapes : list rtype)
    (input : list lex) : pout fn :=
  match input with
  | LName name :: LKey TLbrack :: rest =>
      match pcaps fuel env types rest with
      | Some (caps, LKey TLparen :: more) =>
          match pbind fuel env types more with
          | Some (arg, LKey TRparen :: LKey TThin :: LKey TLbrack :: after) =>
              match pmode after with
              | Some (mode, LKey TRbrack :: output) =>
                  match pty fuel env types output with
                  | Some (out, LKey TMarks :: LKey TLbrace :: marks) =>
                      match pmarks fuel [] marks with
                      | Some (row, next) =>
                          match next with
                          | LKey TUnder :: _ =>
                              match punder next with
                              | Some (lim, LKey TEq :: body) =>
                                  match pexpr fuel env types data shapes body with
                                  | Some (term, tail) =>
                                      Some (Fn name
                                        (Arr mode caps arg out row (Some lim))
                                        term, tail)
                                  | None => None
                                  end
                              | _ => None
                              end
                          | LKey TEq :: body =>
                              match pexpr fuel env types data shapes body with
                              | Some (term, tail) =>
                                  Some (Fn name (Arr mode caps arg out row None)
                                    term, tail)
                              | None => None
                              end
                          | _ => None
                          end
                      | None => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Fixpoint ppars (fuel : nat) (input : list lex)
    {struct fuel} : pout (list nat) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LName name :: LKey TComma :: rest =>
          match ppars fuel' rest with
          | Some (names, tail) => Some (name :: names, tail)
          | None => None
          end
      | LName name :: LKey TRbrack :: rest => Some ([name], rest)
      | _ => None
      end
  end.

Fixpoint prcaps (fuel : nat) (vars : list nat) (types : tenv)
    (input : list lex)
    {struct fuel} : pout (list ibind) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TRbrack :: rest => Some ([], rest)
      | _ =>
          match pibind fuel' vars types input with
          | Some (item, LKey TComma :: more) =>
              match prcaps fuel' vars types more with
              | Some (items, tail) => Some (item :: items, tail)
              | None => None
              end
          | Some (item, LKey TRbrack :: rest) => Some ([item], rest)
          | _ => None
          end
      end
  end.

Fixpoint pkinds (fuel : nat) (input : list lex) {struct fuel}
    : pout (list ppar) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LName name :: LKey TColon :: LKey TData :: LKey TComma :: rest =>
          match pkinds fuel' rest with
          | Some (items, tail) => Some (PPar name PData :: items, tail)
          | None => None
          end
      | LName name :: LKey TColon :: LKey TRes :: LKey TComma :: rest =>
          match pkinds fuel' rest with
          | Some (items, tail) => Some (PPar name PRes :: items, tail)
          | None => None
          end
      | LName name :: LKey TColon :: LKey TData :: LKey TRbrack :: rest =>
          Some ([PPar name PData], rest)
      | LName name :: LKey TColon :: LKey TRes :: LKey TRbrack :: rest =>
          Some ([PPar name PRes], rest)
      | _ => None
      end
  end.

Fixpoint plaws (fuel : nat) (input : list lex) {struct fuel}
    : pout (list law) :=
  match fuel with
  | O => None
  | S fuel' =>
      match pix_add fuel' input with
      | Some (lhs, LKey TEq :: rest) =>
          match pix_add fuel' rest with
          | Some (rhs, LKey TComma :: tail) =>
              match plaws fuel' tail with
              | Some (items, out) => Some (Law IEq lhs rhs :: items, out)
              | None => None
              end
          | Some (rhs, LKey TRbrack :: tail) =>
              Some ([Law IEq lhs rhs], tail)
          | _ => None
          end
      | Some (lhs, LKey TLe :: rest) =>
          match pix_add fuel' rest with
          | Some (rhs, LKey TComma :: tail) =>
              match plaws fuel' tail with
              | Some (items, out) => Some (Law ILe lhs rhs :: items, out)
              | None => None
              end
          | Some (rhs, LKey TRbrack :: tail) =>
              Some ([Law ILe lhs rhs], tail)
          | _ => None
          end
      | _ => None
      end
  end.

Definition pigen (fuel : nat) (vars : list nat) (types : tenv)
    (data : list dtype) (shapes : list rtype) (name : nat)
    (pars : list nat) (laws : list law) (input : list lex) : pout ifn :=
  match input with
  | LKey TLbrack :: caps_input =>
      match prcaps fuel vars types caps_input with
      | Some (caps, LKey TLparen :: more) =>
          match pibind fuel vars types more with
          | Some (arg, LKey TRparen :: LKey TThin :: LKey TLbrack :: after) =>
              match pmode after with
              | Some (mode, LKey TRbrack :: output) =>
                  match pity fuel vars types output with
                  | Some (out, LKey TMarks :: LKey TLbrace :: marks) =>
                      match pmarks fuel [] marks with
                      | Some (row, next) =>
                          match next with
                          | LKey TUnder :: _ =>
                              match punder next with
                              | Some (lim, LKey TEq :: body) =>
                                  match prexpr fuel vars types data shapes body with
                                  | Some (term, tail) =>
                                      let item := IFn name pars laws
                                        (IArr mode caps arg out row (Some lim))
                                        term in
                                      if ifn_b item then Some (item, tail)
                                      else None
                                  | None => None
                                  end
                              | _ => None
                              end
                          | LKey TEq :: body =>
                              match prexpr fuel vars types data shapes body with
                              | Some (term, tail) =>
                                  let item := IFn name pars laws
                                    (IArr mode caps arg out row None) term in
                                  if ifn_b item then Some (item, tail)
                                  else None
                              | None => None
                              end
                          | _ => None
                          end
                      | None => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition piform (fuel : nat) (types : tenv)
    (data : list dtype) (shapes : list rtype)
    (input : list lex) : pout ifn :=
  match input with
  | LName name :: LKey TSize :: LKey TLbrack :: rest =>
      match ppars fuel rest with
      | Some (pars, LKey TLaw :: LKey TLbrack :: tail) =>
          match plaws fuel tail with
          | Some (laws, out) =>
              pigen fuel [] types data shapes name pars laws out
          | None => None
          end
      | Some (pars, tail) =>
          pigen fuel [] types data shapes name pars [] tail
      | None => None
      end
  | _ => None
  end.

Definition ppform (fuel : nat) (types : tenv)
    (data : list dtype) (shapes : list rtype)
    (input : list lex) : pout pfn :=
  match input with
  | LName name :: LKey TKind :: LKey TLbrack :: rest =>
      match pkinds fuel rest with
      | Some (kinds, LKey TSize :: LKey TLbrack :: sized) =>
          match ppars fuel sized with
          | Some (pars, LKey TLaw :: LKey TLbrack :: tail) =>
              match plaws fuel tail with
              | Some (laws, out) =>
                  match pigen fuel (map ppname kinds) types data shapes name
                      pars laws out with
                  | Some (base, tail) =>
                      let item := PFn kinds base in
                      if pfn_b item then Some (item, tail) else None
                  | None => None
                  end
              | None => None
              end
          | Some (pars, tail) =>
              match pigen fuel (map ppname kinds) types data shapes name pars
                  [] tail with
              | Some (base, out) =>
                  let item := PFn kinds base in
                  if pfn_b item then Some (item, out) else None
              | None => None
              end
          | None => None
          end
      | Some (kinds, tail) =>
          match pigen fuel (map ppname kinds) types data shapes name [] [] tail with
          | Some (base, out) =>
              let item := PFn kinds base in
              if pfn_b item then Some (item, out) else None
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Inductive fdecl : Type :=
| FMono : fn -> fdecl
| FSize : ifn -> fdecl
| FPoly : pfn -> fdecl.

Definition pfdecl (fuel : nat) (env : ienv) (types : tenv)
    (data : list dtype) (shapes : list rtype)
    (input : list lex) : pout fdecl :=
  match input with
  | LName _ :: LKey TKind :: _ =>
      match ppform fuel types data shapes input with
      | Some (item, rest) => Some (FPoly item, rest)
      | None => None
      end
  | LName _ :: LKey TSize :: _ =>
      match piform fuel types data shapes input with
      | Some (item, rest) => Some (FSize item, rest)
      | None => None
      end
  | _ =>
      match pform fuel env types data shapes input with
      | Some (item, rest) => Some (FMono item, rest)
      | None => None
      end
  end.

Definition fdname (item : fdecl) : nat :=
  match item with
  | FMono value => fname value
  | FSize value => iname value
  | FPoly value => iname (pbase value)
  end.

Definition fdecl_b (item : fdecl) : bool :=
  match item with
  | FMono value => fcheckb value
  | FSize value => ifn_b value
  | FPoly value => pfn_b value
  end.

Fixpoint fdecls_b (seen : list nat) (items : list fdecl) : bool :=
  match items with
  | [] => true
  | item :: rest =>
      negb (existsb (Nat.eqb (fdname item)) seen)
        && fdecl_b item && fdecls_b (fdname item :: seen) rest
  end.

Fixpoint fmono (items : list fdecl) : list fn :=
  match items with
  | [] => []
  | FMono item :: rest => item :: fmono rest
  | _ :: rest => fmono rest
  end.

Fixpoint pactuals (fuel : nat) (env : ienv) (types : tenv)
    (data : list dtype) (shapes : list rtype) (scope : list sbind)
    (input : list lex) {struct fuel} : pout (list stm) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TRbrack :: rest => Some ([], rest)
      | _ =>
          match pelab fuel' env types data shapes scope input with
          | Some (item, LKey TComma :: more) =>
              match pactuals fuel' env types data shapes scope more with
              | Some (items, tail) => Some (item :: items, tail)
              | None => None
              end
          | Some (item, LKey TRbrack :: rest) => Some ([item], rest)
          | _ => None
          end
      end
  end.

Fixpoint piacts (fuel : nat) (input : list lex)
    {struct fuel} : pout (list ix) :=
  match fuel with
  | O => None
  | S fuel' =>
      match pix_add fuel' input with
      | Some (item, LKey TComma :: more) =>
          match piacts fuel' more with
          | Some (items, tail) => Some (item :: items, tail)
          | None => None
          end
      | Some (item, LKey TRbrack :: rest) => Some ([item], rest)
      | _ => None
      end
  end.

Fixpoint pitacts (fuel : nat) (types : tenv) (input : list lex)
    {struct fuel} : pout (list ity) :=
  match fuel with
  | O => None
  | S fuel' =>
      match pity fuel' [] types input with
      | Some (item, LKey TComma :: more) =>
          match pitacts fuel' types more with
          | Some (items, tail) => Some (item :: items, tail)
          | None => None
          end
      | Some (item, LKey TRbrack :: rest) => Some ([item], rest)
      | _ => None
      end
  end.

Fixpoint flookup (name : nat) (items : list fdecl) : option fdecl :=
  match items with
  | [] => None
  | item :: rest =>
      if Nat.eqb name (fdname item) then Some item else flookup name rest
  end.

Fixpoint nvals_eqb (lhs rhs : list nat) : bool :=
  match lhs, rhs with
  | [], [] => true
  | one :: lrest, two :: rrest =>
      Nat.eqb one two && nvals_eqb lrest rrest
  | _, _ => false
  end.

Fixpoint tvals_eqb (lhs rhs : list ty) : bool :=
  match lhs, rhs with
  | [], [] => true
  | one :: lrest, two :: rrest =>
      ty_eqb one two && tvals_eqb lrest rrest
  | _, _ => false
  end.

Record fuse : Type := FUse {
  fkey : nat;
  ftypes : list ty;
  fvals : list nat;
  ffresh : nat
}.

Fixpoint fuse_find (name : nat) (types : list ty) (values : list nat)
    (items : list fuse) : option nat :=
  match items with
  | [] => None
  | item :: rest =>
      if Nat.eqb name (fkey item)
          && tvals_eqb types (ftypes item)
          && nvals_eqb values (fvals item)
      then Some (ffresh item)
      else fuse_find name types values rest
  end.

Record fctx : Type := FCtx {
  fcdefs : list fdecl;
  fcuses : list fuse;
  fcmade : list fn;
  fcnext : nat
}.

Definition gname (id : nat) : nat := S (id + id).

Definition fresolve (env : ienv) (name : nat) (actuals : list ix)
    (ctx : fctx) : option (nat * fctx) :=
  match flookup name (fcdefs ctx) with
  | Some (FSize item) =>
      match ivals env actuals with
      | Some values =>
          match fuse_find name [] values (fcuses ctx) with
          | Some fresh => Some (fresh, ctx)
          | None =>
              if Nat.ltb (fcnext ctx) pmax then
                let fresh := gname (fcnext ctx) in
                match fspec_check env fresh item actuals with
                | Some made => Some (fresh,
                    FCtx (fcdefs ctx)
                      (FUse name [] values fresh :: fcuses ctx)
                      (made :: fcmade ctx) (S (fcnext ctx)))
                | None => None
                end
              else None
          end
      | None => None
      end
  | _ => None
  end.

Definition presolve (env : ienv) (name : nat) (types : list ity)
    (sizes : list ix) (ctx : fctx) : option (nat * fctx) :=
  match flookup name (fcdefs ctx) with
  | Some (FPoly item) =>
      match Poly.pvals env (Poly.ppars item) types, ivals env sizes with
      | Some norm, Some values =>
          match Poly.ptys norm with
          | Some keys =>
              match fuse_find name keys values (fcuses ctx) with
              | Some fresh => Some (fresh, ctx)
              | None =>
                  if Nat.ltb (fcnext ctx) pmax then
                    let fresh := gname (fcnext ctx) in
                    match pspec env fresh item types sizes with
                    | Some made => Some (fresh,
                        FCtx (fcdefs ctx)
                          (FUse name keys values fresh :: fcuses ctx)
                          (made :: fcmade ctx)
                          (S (fcnext ctx)))
                    | None => None
                    end
                  else None
              end
          | None => None
          end
      | _, _ => None
      end
  | _ => None
  end.

Theorem gname_inj : forall lhs rhs,
  gname lhs = gname rhs -> lhs = rhs.
Proof.
  intros lhs rhs same.
  unfold gname in same.
  lia.
Qed.

Theorem gname_step : forall id,
  gname (S id) = S (S (gname id)).
Proof.
  intros id.
  unfold gname.
  lia.
Qed.

Theorem fresolve_reuse : forall env name actuals defs uses made next item values fresh,
  flookup name defs = Some (FSize item) ->
  ivals env actuals = Some values ->
  fuse_find name [] values uses = Some fresh ->
  fresolve env name actuals (FCtx defs uses made next) =
    Some (fresh, FCtx defs uses made next).
Proof.
  intros env name actuals defs uses made next item values fresh found ran reused.
  unfold fresolve.
  simpl.
  rewrite found, ran, reused.
  reflexivity.
Qed.

Theorem fresolve_new : forall env name actuals defs uses ready next item values made,
  flookup name defs = Some (FSize item) ->
  ivals env actuals = Some values ->
  fuse_find name [] values uses = None ->
  Nat.ltb next pmax = true ->
  fspec_check env (gname next) item actuals = Some made ->
  fresolve env name actuals (FCtx defs uses ready next) =
    Some (gname next,
      FCtx defs (FUse name [] values (gname next) :: uses)
        (made :: ready) (S next)).
Proof.
  intros env name actuals defs uses ready next item values made
    found ran absent room checked.
  unfold fresolve.
  simpl.
  rewrite found, ran, absent, room, checked.
  reflexivity.
Qed.

Theorem presolve_reuse : forall env name types sizes defs uses made next item
    norm keys values fresh,
  flookup name defs = Some (FPoly item) ->
  Poly.pvals env (Poly.ppars item) types = Some norm ->
  ivals env sizes = Some values ->
  Poly.ptys norm = Some keys ->
  fuse_find name keys values uses = Some fresh ->
  presolve env name types sizes (FCtx defs uses made next) =
    Some (fresh, FCtx defs uses made next).
Proof.
  intros env name types sizes defs uses made next item norm keys values fresh
    found typed sized keyed reused.
  unfold presolve. simpl.
  rewrite found, typed, sized, keyed, reused.
  reflexivity.
Qed.

Theorem presolve_new : forall env name types sizes defs uses ready next item
    norm keys values made,
  flookup name defs = Some (FPoly item) ->
  Poly.pvals env (Poly.ppars item) types = Some norm ->
  ivals env sizes = Some values ->
  Poly.ptys norm = Some keys ->
  fuse_find name keys values uses = None ->
  Nat.ltb next pmax = true ->
  pspec env (gname next) item types sizes = Some made ->
  presolve env name types sizes (FCtx defs uses ready next) =
    Some (gname next,
      FCtx defs (FUse name keys values (gname next) :: uses)
        (made :: ready) (S next)).
Proof.
  intros env name types sizes defs uses ready next item norm keys values made
    found typed sized keyed absent room checked.
  unfold presolve. simpl.
  rewrite found, typed, sized, keyed, absent, room, checked.
  reflexivity.
Qed.

Fixpoint pflow (fuel : nat) (env : ienv) (types : tenv)
    (data : list dtype) (shapes : list rtype) (scope : list sbind)
    (ctx : fctx)
    (input : list lex) {struct fuel} : pout (Fun.ftm * fctx) :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TIf :: rest =>
          match pelab fuel' env types data shapes scope rest with
          | Some (guard, LKey TThen :: more) =>
              match pflow fuel' env types data shapes scope ctx more with
              | Some ((yes, yes_ctx), LKey TElse :: after) =>
                  match pflow fuel' env types data shapes scope yes_ctx after with
                  | Some ((no, no_ctx), tail) =>
                      Some ((FIf guard yes no, no_ctx), tail)
                  | None => None
                  end
              | _ => None
              end
          | _ => None
          end
      | LKey TUse :: LName name :: rest =>
          let picked :=
            match flookup name (fcdefs ctx) with
            | Some (FSize _) =>
                match rest with
                | LKey TSize :: LKey TLbrack :: sized =>
                    match piacts fuel' sized with
                    | Some (actuals, tail) =>
                        match fresolve env name actuals ctx with
                        | Some (fresh, next_ctx) =>
                            Some ((fresh, next_ctx), tail)
                        | None => None
                        end
                    | None => None
                    end
                | _ => None
                end
            | Some (FPoly _) =>
                match rest with
                | LKey TKind :: LKey TLbrack :: typed =>
                    match pitacts fuel' types typed with
                    | Some (type_args, LKey TSize :: LKey TLbrack :: sized) =>
                        match piacts fuel' sized with
                        | Some (size_args, tail) =>
                            match presolve env name type_args size_args ctx with
                            | Some (fresh, next_ctx) =>
                                Some ((fresh, next_ctx), tail)
                            | None => None
                            end
                        | None => None
                        end
                    | Some (type_args, tail) =>
                        match presolve env name type_args [] ctx with
                        | Some (fresh, next_ctx) =>
                            Some ((fresh, next_ctx), tail)
                        | None => None
                        end
                    | None => None
                    end
                | _ => None
                end
            | _ => Some ((name, ctx), rest)
            end in
          match picked with
          | Some ((call, next_ctx), LKey TLbrack :: cap_input) =>
              match pactuals fuel' env types data shapes scope cap_input with
              | Some (caps, LKey TLparen :: more) =>
                  match pelab fuel' env types data shapes scope more with
                  | Some (arg, LKey TRparen :: LKey TAs :: after) =>
                      match pbind fuel' env types after with
                      | Some (result, LKey TIn :: body) =>
                          match pflow fuel' env types data shapes
                              (spush scope result) next_ctx body with
                          | Some ((next, last_ctx), tail) =>
                              Some ((FCall result call caps arg next, last_ctx),
                                tail)
                          | None => None
                          end
                      | _ => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | _ =>
          match pelab fuel' env types data shapes scope input with
          | Some (term, tail) =>
              @Some ((Fun.ftm * fctx) * list lex)
                (@pair (Fun.ftm * fctx) (list lex)
                  (@pair Fun.ftm fctx (FRet term) ctx) tail)
          | None => None
          end
      end
  end.

Record vdecl : Type := VDecl {
  vdname : nat;
  vdinfo : Fhe.finfo;
  vdparam : Param.fparam;
  vdhost : Hop.htm;
  vdstage : option Hfhe.hinfo
}.

Fixpoint vhas (name : nat) (items : list vdecl) : bool :=
  match items with
  | [] => false
  | item :: rest => Nat.eqb name (vdname item) || vhas name rest
  end.

Definition pvval (fuel : nat) (env : ienv) (input : list lex) : pout nat :=
  match pix_add fuel input with
  | Some (term, rest) =>
      match ieval env term with
      | Some value => Some (value, rest)
      | None => None
      end
  | None => None
  end.

Definition pvfield (fuel : nat) (env : ienv) (word : nat)
    (input : list lex) : pout nat :=
  match pword word input with
  | Some (LKey TLbrack :: rest) =>
      match pvval fuel env rest with
      | Some (value, LKey TRbrack :: tail) => Some (value, tail)
      | _ => None
      end
  | _ => None
  end.

Definition pvdepth (fuel : nat) (env : ienv) (input : list lex) : pout nat :=
  match input with
  | LKey TDepth :: LKey TLbrack :: rest =>
      match pvval fuel env rest with
      | Some (value, LKey TRbrack :: tail) => Some (value, tail)
      | _ => None
      end
  | _ => None
  end.

Fixpoint pvadd (fuel : nat) (words : vocab) (env : ienv)
    (input : list lex) {struct fuel} : pout Fhe.ftm :=
  match fuel with
  | O => None
  | S fuel' =>
      match pvmul fuel' words env input with
      | Some (lhs, rest) => pvadd_tail fuel' words env lhs rest
      | None => None
      end
  end
with pvadd_tail (fuel : nat) (words : vocab) (env : ienv)
    (lhs : Fhe.ftm) (input : list lex) {struct fuel} : pout Fhe.ftm :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TPlus :: rest =>
          match pvmul fuel' words env rest with
          | Some (rhs, next) =>
              pvadd_tail fuel' words env (Fhe.FAdd lhs rhs) next
          | None => None
          end
      | _ => Some (lhs, input)
      end
  end
with pvmul (fuel : nat) (words : vocab) (env : ienv)
    (input : list lex) {struct fuel} : pout Fhe.ftm :=
  match fuel with
  | O => None
  | S fuel' =>
      match pvatom fuel' words env input with
      | Some (lhs, rest) => pvmul_tail fuel' words env lhs rest
      | None => None
      end
  end
with pvmul_tail (fuel : nat) (words : vocab) (env : ienv)
    (lhs : Fhe.ftm) (input : list lex) {struct fuel} : pout Fhe.ftm :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TStar :: rest =>
          match pvatom fuel' words env rest with
          | Some (rhs, next) =>
              pvmul_tail fuel' words env (Fhe.FMul lhs rhs) next
          | None => None
          end
      | _ => Some (lhs, input)
      end
  end
with pvatom (fuel : nat) (words : vocab) (env : ienv)
    (input : list lex) {struct fuel} : pout Fhe.ftm :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LName name :: rest =>
          if Nat.eqb name (wrenew words) then
            match rest with
            | LKey TLparen :: more =>
                match pvadd fuel' words env more with
                | Some (term, LKey TRparen :: tail) =>
                    Some (Fhe.FRe term, tail)
                | _ => None
                end
            | _ => None
            end
          else if Nat.eqb name (wtrim words) then
            match rest with
            | LKey TLbrack :: more =>
                match pvval fuel' env more with
                | Some (cut, LKey TRbrack :: LKey TLparen :: body) =>
                    match pvadd fuel' words env body with
                    | Some (term, LKey TRparen :: tail) =>
                        Some (Fhe.FTrim cut term, tail)
                    | _ => None
                    end
                | _ => None
                end
            | _ => None
            end
          else Some (Fhe.FVar name, rest)
      | LKey TLparen :: rest =>
          match pvadd fuel' words env rest with
          | Some (term, LKey TRparen :: tail) => Some (term, tail)
          | _ => None
          end
      | _ => None
      end
  end.

Definition pvparam (fuel : nat) (words : vocab) (env : ienv) (key : nat)
    (input : list lex) : pout Param.fparam :=
  match pword (wparam words) input with
  | Some (LKey TLbrack :: rest) =>
      match pvval fuel env rest with
      | Some (id, LKey TRbrack :: more) =>
          match pvfield fuel env (wroom words) more with
          | Some (room, tail) => Some (Param.Fparam id key room, tail)
          | None => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition pvstate (fuel : nat) (words : vocab) (env : ienv)
    (input : list lex) : pout Hfhe.hshape :=
  match pword (wstate words) input with
  | Some (LKey TLbrace :: rest) =>
      match pvfield fuel env (wterms words) rest with
      | Some (terms, LKey TComma :: more) =>
          match pvfield fuel env (wslots words) more with
          | Some (slots, LKey TComma :: after) =>
              match pvfield fuel env (wquery words) after with
              | Some (query, LKey TRbrace :: tail) =>
                  Some (Hfhe.hmake terms slots query, tail)
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition pvinput (fuel : nat) (words : vocab) (env : ienv) (staged : bool)
    (input : list lex)
    : pout ((nat * Fhe.enc) * option (nat * Hfhe.hshape)) :=
  match input with
  | LKey TInput :: rest =>
      match pname rest with
      | Some (name, LKey TColon :: more) =>
          match pword (wenc words) more with
          | Some (LKey TLbrack :: sized) =>
              match pvval fuel env sized with
              | Some (key, LKey TComma :: after) =>
                  match pvval fuel env after with
                  | Some (rem, LKey TRbrack :: tail) =>
                      if staged then
                        match pvstate fuel words env tail with
                        | Some (shape, next) =>
                            Some (((name, Fhe.Enc key rem),
                              Some (name, shape)), next)
                        | None => None
                        end
                      else Some (((name, Fhe.Enc key rem), None), tail)
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Record vraw : Type := VRaw {
  vrpars : Param.fcatalog;
  vrenv : Fhe.fenv;
  vrhenv : Hfhe.henv;
  vrterm : Fhe.ftm
}.

Fixpoint pvitems (fuel : nat) (words : vocab) (env : ienv) (key : nat)
    (staged : bool) (pars : Param.fcatalog) (fenv : Fhe.fenv)
    (henv : Hfhe.henv) (input : list lex) {struct fuel} : pout vraw :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LName name :: _ =>
          if Nat.eqb name (wparam words) then
            match pvparam fuel' words env key input with
            | Some (item, rest) =>
                pvitems fuel' words env key staged (item :: pars) fenv henv rest
            | None => None
            end
          else None
      | LKey TInput :: _ =>
          match pvinput fuel' words env staged input with
          | Some ((item, hitem), rest) =>
              let next_h :=
                match hitem with Some value => value :: henv | None => henv end in
              pvitems fuel' words env key staged pars (item :: fenv) next_h rest
          | None => None
          end
      | LKey TTerm :: rest =>
          match pvadd fuel' words env rest with
          | Some (term, LKey TRbrace :: tail) =>
              Some (VRaw (rev pars) (rev fenv) (rev henv) term, tail)
          | _ => None
          end
      | _ => None
      end
  end.

Definition pvdecl (fuel : nat) (words : vocab) (env : ienv)
    (input : list lex) : pout vdecl :=
  match pword (wveil words) input with
  | Some rest =>
      match pname rest with
      | Some (name, more) =>
          match pvfield fuel env (wkey words) more with
          | Some (key, sized) =>
              match pvdepth fuel env sized with
              | Some (full, LKey TUnder :: LKey TLbrace :: under) =>
                  match pvfield fuel env (wadd words) under with
                  | Some (add, LKey TComma :: muls) =>
                      match pvfield fuel env (wmul words) muls with
                      | Some (mul, LKey TComma :: renews) =>
                          match pvfield fuel env (wrenew words) renews with
                          | Some (renew, LKey TRbrace :: after) =>
                              let picked :=
                                match after with
                                | LName got :: _ =>
                                    if Nat.eqb got (wstage words) then
                                      match pword (wstage words) after with
                                      | Some (LKey TLbrack :: stage) =>
                                          match pword (wprod words) stage with
                                          | Some (LKey TRbrack :: tail) =>
                                              Some (true, tail)
                                          | _ => None
                                          end
                                      | _ => None
                                      end
                                    else Some (false, after)
                                | _ => Some (false, after)
                                end in
                              match picked with
                              | Some (staged, LKey TLbrace :: body) =>
                                  match pvitems fuel words env key staged
                                      [] [] [] body with
                                  | Some (raw, tail) =>
                                      let cfg := Fhe.Fcfg full add mul renew in
                                      let profile := [(key, cfg)] in
                                      let catalog := vrpars raw in
                                      if Param.catalog_b catalog then
                                        match Hop.lower profile (vrenv raw)
                                            (vrterm raw) with
                                        | Some host =>
                                            if staged then
                                              match Hpar.check_cat Hpar.prod_cat
                                                  catalog profile (vrenv raw)
                                                  (vrhenv raw) (vrterm raw) with
                                              | Some link =>
                                                  Some (VDecl name
                                                    (Hpar.lfhe link)
                                                    (Hpar.lparam link) host
                                                    (Some (Hpar.lhfhe link)), tail)
                                              | None => None
                                              end
                                            else
                                              match Fhe.fcheck profile (vrenv raw)
                                                  (vrterm raw) with
                                              | Some info =>
                                                  match Param.params catalog info with
                                                  | Some param =>
                                                      Some (VDecl name info param host
                                                        None, tail)
                                                  | None => None
                                                  end
                                              | None => None
                                              end
                                        | None => None
                                        end
                                      else None
                                  | None => None
                                  end
                              | _ => None
                              end
                          | _ => None
                          end
                      | _ => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Inductive hphase : Type := HOpen | HDecl | HForm.

Definition early (phase : hphase) : bool :=
  match phase with HOpen => true | _ => false end.

Definition preform (phase : hphase) : bool :=
  match phase with HForm => false | _ => true end.

Record hstate : Type := HState {
  hphasev : hphase;
  hsizes : ienv;
  htypes : tenv;
  hcodes : cenv;
  hbinds : list sbind;
  hperms : pset;
  hdata : list dtype;
  hshapes : list rtype;
  hforms : list fdecl;
  hveils : list vdecl
}.

Definition hzero : hstate := HState HOpen [] [] [] [] [] [] [] [] [].

Record raw_head : Type := RawHead {
  rhname : nat;
  rhbinds : list sbind;
  rhperms : pset;
  rhdata : list dtype;
  rhshapes : list rtype;
  rhforms : list fdecl;
  rhready : list fn;
  rhveils : list vdecl;
  rhbody : Fun.ftm
}.

Fixpoint pheads (fuel : nat) (words : vocab) (name : nat) (state : hstate)
    (input : list lex)
    {struct fuel} : pout raw_head :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | LKey TSize :: rest =>
          if early (hphasev state) then
            match psize (hsizes state) rest with
            | Some (next, tail) =>
                pheads fuel' words name
                  (HState HOpen next (htypes state) (hcodes state)
                    (hbinds state) (hperms state) (hdata state)
                    (hshapes state) (hforms state) (hveils state)) tail
            | None => None
            end
          else
            None
      | LKey TMeasure :: rest =>
          if early (hphasev state) then
            match pmeasure fuel' (hsizes state) rest with
            | Some (next, tail) =>
                pheads fuel' words name
                  (HState HOpen next (htypes state) (hcodes state)
                    (hbinds state) (hperms state) (hdata state)
                    (hshapes state) (hforms state) (hveils state)) tail
            | None => None
            end
          else
            None
      | LKey TLaw :: rest =>
          if early (hphasev state) then
            match plaw fuel' (hsizes state) rest with
            | Some tail => pheads fuel' words name state tail
            | None => None
            end
          else
            None
      | LKey TData :: rest =>
          if preform (hphasev state) then
            match pdata fuel' (hsizes state) (htypes state) rest with
            | Some (item, next) =>
                match tput (htypes state) (dname (dvalue item)) (dtyp item),
                    cput (hcodes state) (dcode item) with
                | Some types, Some codes =>
                    pheads fuel' words name
                      (HState HDecl (hsizes state) types codes (hbinds state)
                        (hperms state) (dvalue item :: hdata state)
                        (hshapes state) (hforms state) (hveils state)) next
                | _, _ => None
                end
            | None => None
            end
          else None
      | LKey TShape :: rest =>
          if preform (hphasev state) then
            match pshape fuel' (hsizes state) (htypes state) rest with
            | Some (item, next) =>
                match tput (htypes state) (rname (svalue item)) (styp item),
                    cput (hcodes state) (scode item) with
                | Some types, Some codes =>
                    pheads fuel' words name
                      (HState HDecl (hsizes state) types codes (hbinds state)
                        (hperms state) (hdata state)
                        (svalue item :: hshapes state) (hforms state)
                        (hveils state)) next
                | _, _ => None
                end
            | None => None
            end
          else None
      | LKey TPermit :: rest =>
          if preform (hphasev state) then
            match pperm rest with
            | Some (one, next) =>
                pheads fuel' words name
                  (HState HDecl (hsizes state) (htypes state) (hcodes state)
                    (hbinds state) (one :: hperms state) (hdata state)
                    (hshapes state) (hforms state) (hveils state)) next
            | None => None
            end
          else None
      | LKey TInput :: rest =>
          if preform (hphasev state) then
            match pbind fuel' (hsizes state) (htypes state) rest with
            | Some (item, next) =>
                pheads fuel' words name
                  (HState (hphasev state) (hsizes state) (htypes state)
                    (hcodes state) (item :: hbinds state) (hperms state)
                    (hdata state) (hshapes state) (hforms state)
                    (hveils state)) next
            | None => None
            end
          else None
      | LKey TForm :: rest =>
          match pfdecl fuel' (hsizes state) (htypes state)
              (hdata state) (hshapes state) rest with
          | Some (item, next) =>
              pheads fuel' words name
                (HState HForm (hsizes state) (htypes state) (hcodes state)
                  (hbinds state) (hperms state) (hdata state)
                  (hshapes state) (item :: hforms state)
                  (hveils state)) next
          | None => None
          end
      | LName got :: _ =>
          if preform (hphasev state) && Nat.eqb got (wveil words) then
            match pvdecl fuel' words (hsizes state) input with
            | Some (item, next) =>
                if vhas (vdname item) (hveils state) then None
                else
                  pheads fuel' words name
                    (HState HDecl (hsizes state) (htypes state)
                      (hcodes state) (hbinds state) (hperms state)
                      (hdata state) (hshapes state) (hforms state)
                      (item :: hveils state)) next
            | None => None
            end
          else None
      | LKey TTerm :: rest =>
          let ctx := FCtx (hforms state) [] [] 0 in
          match pflow fuel' (hsizes state) (htypes state)
              (hdata state) (hshapes state) (rev (hbinds state)) ctx rest with
          | Some ((body, last), LKey TRbrace :: LKey TEof :: tail) =>
              let forms := rev (hforms state) in
              let ready := fmono forms ++ rev (fcmade last) in
              Some (RawHead name (rev (hbinds state)) (rev (hperms state))
                (rev (hdata state)) (rev (hshapes state)) forms ready
                (rev (hveils state)) body, tail)
          | _ => None
          end
      | _ => None
      end
  end.

Definition pread (words : vocab) (fuel : nat) (input : list lex)
    : pout raw_head :=
  match input with
  | LKey TProgram :: LName name :: LKey TLbrace :: rest =>
      pheads fuel words name hzero rest
  | _ => None
  end.

Fixpoint shas (name : nat) (items : list sbind) : bool :=
  match items with
  | [] => false
  | item :: rest => Nat.eqb name (sname item) || shas name rest
  end.

Fixpoint suniq (items : list sbind) : bool :=
  match items with
  | [] => true
  | item :: rest => negb (shas (sname item) rest) && suniq rest
  end.

Definition smode (item : sbind) : bool :=
  if data_b (sty item) then true
  else match smul item with M1 => true | _ => false end.

Definition sgood (items : list sbind) : bool :=
  Nat.leb (length items) (rinputs local)
    && suniq items
    && forallb smode items
    && forallb (fun item => ty_b (sty item)) items.

Definition dgood (items : list dtype) : bool := forallb decl_b items.
Definition rgood (items : list rtype) : bool := forallb rdecl_b items.

Definition bopen (items : list sbind) : option (list sbind) :=
  if sgood items then Some items else None.

Record front : Type := Front {
  frname : nat;
  frbinds : list sbind;
  frperms : pset;
  frdata : list dtype;
  frshapes : list rtype;
  frforms : list fdecl;
  frready : list fn;
  frveils : list vdecl;
  frbody : Fun.ftm;
  frrest : list lex
}.

Definition read (words : vocab) (fuel : nat) (input : list lex) : option front :=
  if vocab_b words then match pread words fuel input with
  | Some (head, rest) =>
      if pset_b (rhperms head) then
        if dgood (rhdata head) then
          if rgood (rhshapes head) then
            if fdecls_b [] (rhforms head) then
              if defs_b [] (rhready head) then
                match bopen (rhbinds head) with
                | Some items => Some (Front (rhname head) items (rhperms head)
                    (rhdata head) (rhshapes head) (rhforms head)
                    (rhready head) (rhveils head) (rhbody head) rest)
                | None => None
                end
              else None
            else None
          else None
        else None
      else None
  | None => None
  end else None.

Theorem bopen_sound : forall raw items,
  bopen raw = Some items -> raw = items /\ sgood items = true.
Proof.
  intros raw items accepted.
  unfold bopen in accepted.
  destruct (sgood raw) eqn:good; try discriminate.
  inversion accepted; subst.
  split; reflexivity || assumption.
Qed.

Theorem bopen_complete : forall items,
  sgood items = true -> bopen items = Some items.
Proof.
  intros items good.
  unfold bopen.
  rewrite good.
  reflexivity.
Qed.

Theorem read_sound : forall words fuel input value,
  read words fuel input = Some value ->
  exists head,
    vocab_b words = true
      /\ pread words fuel input = Some (head, frrest value)
      /\ rhname head = frname value
      /\ rhbinds head = frbinds value
      /\ rhperms head = frperms value
      /\ rhdata head = frdata value
      /\ rhshapes head = frshapes value
      /\ rhforms head = frforms value
      /\ rhready head = frready value
      /\ rhveils head = frveils value
      /\ rhbody head = frbody value
      /\ pset_b (frperms value) = true
      /\ dgood (frdata value) = true
      /\ rgood (frshapes value) = true
      /\ fdecls_b [] (frforms value) = true
      /\ defs_b [] (frready value) = true
      /\ sgood (frbinds value) = true.
Proof.
  intros words fuel input value accepted.
  unfold read in accepted.
  destruct (vocab_b words) eqn:vocab_ok; try discriminate.
  destruct (pread words fuel input) as [[head rest] |] eqn:parsed;
    try discriminate.
  destruct (pset_b (rhperms head)) eqn:rights; try discriminate.
  destruct (dgood (rhdata head)) eqn:data_ok; try discriminate.
  destruct (rgood (rhshapes head)) eqn:shape_ok; try discriminate.
  destruct (fdecls_b [] (rhforms head)) eqn:forms_ok; try discriminate.
  destruct (defs_b [] (rhready head)) eqn:ready_ok; try discriminate.
  destruct (bopen (rhbinds head)) as [items |] eqn:opened;
    try discriminate.
  inversion accepted; subst.
  apply bopen_sound in opened as [same good].
  subst items.
  exists head.
  repeat split; assumption || reflexivity.
Qed.

Theorem read_complete : forall words fuel input head rest,
  vocab_b words = true ->
  pread words fuel input = Some (head, rest) ->
  pset_b (rhperms head) = true ->
  dgood (rhdata head) = true ->
  rgood (rhshapes head) = true ->
  fdecls_b [] (rhforms head) = true ->
  defs_b [] (rhready head) = true ->
  sgood (rhbinds head) = true ->
  read words fuel input = Some (Front (rhname head) (rhbinds head)
    (rhperms head) (rhdata head) (rhshapes head) (rhforms head)
    (rhready head) (rhveils head) (rhbody head) rest).
Proof.
  intros words fuel input head rest vocab_ok parsed rights data_ok shape_ok
    forms_ok ready_ok good.
  unfold read.
  rewrite vocab_ok, parsed, rights, data_ok, shape_ok, forms_ok, ready_ok,
    (bopen_complete _ good).
  reflexivity.
Qed.

Theorem read_unique : forall words fuel input left right,
  read words fuel input = Some left ->
  read words fuel input = Some right ->
  left = right.
Proof.
  intros words fuel input left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.