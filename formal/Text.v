(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.

Require Import Prof.

Import ListNotations.

Inductive tok : Type :=
| TProgram
| TSize
| TMeasure
| TLaw
| TInput
| TTerm
| TForm
| TKind
| TMarks
| TUnder
| TSteps
| TDepth
| TWork
| TUse
| TData
| TShape
| TPermit
| TTag
| TMake
| TErase
| TOnce
| TMany
| TUnit
| TBool
| TInt
| TBytes
| TVec
| TCap
| TResult
| TRes
| TLet
| TIn
| TSplit
| TAs
| TIf
| TThen
| TElse
| TTrue
| TFalse
| TGood
| TBad
| TCase
| TOf
| TFst
| TSnd
| TEqual
| TRead
| TWrite
| TEmit
| TFail
| TCat
| TTake
| TDrop
| TVcat
| TAt
| TUncons
| TFold
| TEvery
| TSome
| TCount
| TTotal
| TWeave
| TBraid
| TLoom
| TOrbit
| TWake
| TRift
| TFrom
| TWith
| TStep
| TClose
| TMax
| TAbs
| TLbrace
| TRbrace
| TLparen
| TRparen
| TLbrack
| TRbrack
| TColon
| TComma
| TEq
| TLt
| TLe
| TGt
| TGe
| TArrow
| TThin
| TBar
| TPlus
| TMinus
| TStar
| TSlash
| TPercent
| TName
| TNat
| THex
| THold : mode -> tok
| TEof.

Scheme Equality for tok.

Definition out := option (list tok).

Definition take (want : tok) (input : list tok) : out :=
  match input with
  | got :: rest => if tok_beq want got then Some rest else None
  | [] => None
  end.

Theorem take_sound : forall want input rest,
  take want input = Some rest -> input = want :: rest.
Proof.
  intros want input rest H.
  destruct input as [| got tail]; try discriminate.
  destruct want, got; simpl in H; try discriminate;
    try (inversion H; reflexivity).
  destruct m, m0; simpl in H; try discriminate;
    inversion H; reflexivity.
Qed.

Theorem take_complete : forall want rest,
  take want (want :: rest) = Some rest.
Proof.
  intros want rest.
  destruct want; try reflexivity.
  destruct m; reflexivity.
Qed.

Fixpoint pidx_add (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match pidx_mul fuel' input with
      | Some rest => pidx_add_tail fuel' rest
      | None => None
      end
  end
with pidx_add_tail (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TPlus :: rest | TMinus :: rest =>
          match pidx_mul fuel' rest with
          | Some next => pidx_add_tail fuel' next
          | None => None
          end
      | _ => Some input
      end
  end
with pidx_mul (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match pidx_atom fuel' input with
      | Some rest => pidx_mul_tail fuel' rest
      | None => None
      end
  end
with pidx_mul_tail (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TStar :: rest =>
          match pidx_atom fuel' rest with
          | Some next => pidx_mul_tail fuel' next
          | None => None
          end
      | _ => Some input
      end
  end
with pidx_atom (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TNat :: rest | TName :: rest => Some rest
      | TMax :: rest =>
          match take TLparen rest with
          | Some rest =>
              match pidx_add fuel' rest with
              | Some rest =>
                  match take TComma rest with
                  | Some rest =>
                      match pidx_add fuel' rest with
                      | Some rest => take TRparen rest
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | TLparen :: rest =>
          match pidx_add fuel' rest with
          | Some rest => take TRparen rest
          | None => None
          end
      | _ => None
      end
  end.

Fixpoint pty (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match pty_atom fuel' input with
      | Some (TStar :: rest) => pty fuel' rest
      | other => other
      end
  end
with pty_atom (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TUnit :: rest | TBool :: rest | TInt :: rest | TName :: rest => Some rest
      | TBytes :: rest =>
          match take TLbrack rest with
          | Some rest =>
              match pidx_add fuel' rest with
              | Some rest => take TRbrack rest
              | None => None
              end
          | None => None
          end
      | TVec :: rest =>
          match take TLbrack rest with
          | Some rest =>
              match pidx_add fuel' rest with
              | Some rest =>
                  match take TComma rest with
                  | Some rest =>
                      match pty fuel' rest with
                      | Some rest => take TRbrack rest
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | TCap :: rest =>
          match take TLbrack rest with
          | Some rest =>
              match take TNat rest with
              | Some rest => take TRbrack rest
              | None => None
              end
          | None => None
          end
      | TResult :: rest =>
          match take TLbrack rest with
          | Some rest =>
              match pty fuel' rest with
              | Some rest =>
                  match take TComma rest with
                  | Some rest =>
                      match pty fuel' rest with
                      | Some rest => take TRbrack rest
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | TLparen :: rest =>
          match pty fuel' rest with
          | Some rest => take TRparen rest
          | None => None
          end
      | _ => None
      end
  end.

Definition pmul (input : list tok) : out :=
  match input with
  | TErase :: rest | TOnce :: rest | TMany :: rest => Some rest
  | _ => None
  end.

Definition pbind (fuel : nat) (input : list tok) : out :=
  match pmul input with
  | Some rest =>
      match take TName rest with
      | Some rest =>
          match take TColon rest with
          | Some rest => pty fuel rest
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Fixpoint pspicks (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TName :: TArrow :: rest =>
          match pbind fuel' rest with
          | Some (TComma :: rest) => pspicks fuel' rest
          | Some (TRbrace :: rest) => Some rest
          | _ => None
          end
      | _ => None
      end
  end.

Fixpoint pexpr (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TLet :: rest =>
          match pbind fuel' rest with
          | Some rest =>
              match take TEq rest with
              | Some rest =>
                  match pexpr fuel' rest with
                  | Some rest =>
                      match take TIn rest with
                      | Some rest => pexpr fuel' rest
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | TSplit :: rest =>
          match pexpr fuel' rest with
          | Some rest =>
              match take TAs rest with
              | Some (TName :: TLbrace :: rest) =>
                  match pspicks fuel' rest with
                  | Some (TIn :: rest) => pexpr fuel' rest
                  | _ => None
                  end
              | Some rest =>
                  match pbind fuel' rest with
                  | Some rest =>
                      match take TComma rest with
                      | Some rest =>
                          match pbind fuel' rest with
                          | Some rest =>
                              match take TIn rest with
                              | Some rest => pexpr fuel' rest
                              | None => None
                              end
                          | None => None
                          end
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | TIf :: rest =>
          match pexpr fuel' rest with
          | Some rest =>
              match take TThen rest with
              | Some rest =>
                  match pexpr fuel' rest with
                  | Some rest =>
                      match take TElse rest with
                      | Some rest => pexpr fuel' rest
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | TCase :: rest =>
          match pexpr fuel' rest with
          | Some (TAs :: TName :: TOf :: TLbrace :: rest) => pdarms fuel' rest
          | Some (TOf :: TGood :: rest) =>
              match pbind fuel' rest with
              | Some rest =>
                  match take TArrow rest with
                  | Some rest =>
                      match pexpr fuel' rest with
                      | Some (TBar :: TBad :: rest) =>
                          match pbind fuel' rest with
                          | Some rest =>
                              match take TArrow rest with
                              | Some rest => pexpr fuel' rest
                              | None => None
                              end
                          | None => None
                          end
                      | _ => None
                      end
                  | None => None
                  end
              | None => None
              end
          | _ => None
          end
      | TFold :: rest =>
          match pexpr fuel' rest with
          | Some rest =>
              match take TFrom rest with
              | Some rest =>
                  match pexpr fuel' rest with
                  | Some rest =>
                      match take TWith rest with
                      | Some rest =>
                          match pbind fuel' rest with
                          | Some rest =>
                              match take TComma rest with
                              | Some rest =>
                                  match pbind fuel' rest with
                                  | Some rest =>
                                      match take TArrow rest with
                                      | Some rest => pexpr fuel' rest
                                      | None => None
                                      end
                                  | None => None
                                  end
                              | None => None
                              end
                          | None => None
                          end
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | TEvery :: rest | TSome :: rest | TCount :: rest | TTotal :: rest =>
          match pexpr fuel' rest with
          | Some rest =>
              match take TWith rest with
              | Some rest =>
                  match pbind fuel' rest with
                  | Some rest =>
                      match take TArrow rest with
                      | Some rest => pexpr fuel' rest
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | TWeave :: TLbrack :: rest =>
          match pidx_add fuel' rest with
          | Some (TComma :: rest) =>
              match pty fuel' rest with
              | Some (TRbrack :: rest) =>
                  match pexpr fuel' rest with
                  | Some (TWith :: rest) =>
                      match pbind fuel' rest with
                      | Some (TArrow :: rest) => pexpr fuel' rest
                      | _ => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | TBraid :: TLbrack :: rest =>
          match pidx_add fuel' rest with
          | Some (TComma :: rest) =>
              match pty fuel' rest with
              | Some (TRbrack :: rest) =>
                  match pexpr fuel' rest with
                  | Some (TComma :: rest) =>
                      match pexpr fuel' rest with
                      | Some (TWith :: rest) =>
                          match pbind fuel' rest with
                          | Some (TComma :: rest) =>
                              match pbind fuel' rest with
                              | Some (TArrow :: rest) => pexpr fuel' rest
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
      | TLoom :: TLbrack :: rest =>
          match pidx_add fuel' rest with
          | Some (TComma :: rest) =>
              match pty fuel' rest with
              | Some (TRbrack :: TWith :: rest) =>
                  match pbind fuel' rest with
                  | Some (TArrow :: rest) => pexpr fuel' rest
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | TOrbit :: TLbrack :: rest =>
          match pidx_add fuel' rest with
          | Some (TRbrack :: TFrom :: rest) =>
              match pexpr fuel' rest with
              | Some (TWith :: rest) =>
                  match pbind fuel' rest with
                  | Some (TArrow :: rest) => pexpr fuel' rest
                  | _ => None
                  end
              | _ => None
              end
          | Some (TComma :: rest) =>
              match pexpr fuel' rest with
              | Some (TRbrack :: TFrom :: rest) =>
                  match pexpr fuel' rest with
                  | Some (TWith :: rest) =>
                      match pbind fuel' rest with
                      | Some (TArrow :: rest) => pexpr fuel' rest
                      | _ => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | TWake :: TLbrack :: rest =>
          match pidx_add fuel' rest with
          | Some (TRbrack :: TFrom :: rest) =>
              match pexpr fuel' rest with
              | Some (TWith :: rest) =>
                  match pbind fuel' rest with
                  | Some (TArrow :: rest) => pexpr fuel' rest
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | TRift :: TLbrack :: rest =>
          match pidx_add fuel' rest with
          | Some (TComma :: rest) =>
              match pidx_add fuel' rest with
              | Some (TComma :: rest) =>
                  match pty fuel' rest with
                  | Some (TRbrack :: TLparen :: rest) =>
                      match pexpr fuel' rest with
                      | Some (TRparen :: rest) => Some rest
                      | _ => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | _ => None
          end
      | _ => porder fuel' input
      end
  end
with porder (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match padd fuel' input with
      | Some (TLt :: rest) | Some (TLe :: rest)
      | Some (TGt :: rest) | Some (TGe :: rest) => padd fuel' rest
      | Some rest => Some rest
      | None => None
      end
  end
with padd (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match pprod fuel' input with
      | Some rest => padd_tail fuel' rest
      | None => None
      end
  end
with padd_tail (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TPlus :: rest | TMinus :: rest =>
          match pprod fuel' rest with
          | Some next => padd_tail fuel' next
          | None => None
          end
      | _ => Some input
      end
  end
with pprod (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match patom fuel' input with
      | Some rest => pprod_tail fuel' rest
      | None => None
      end
  end
with pprod_tail (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TStar :: rest | TSlash :: rest | TPercent :: rest =>
          match patom fuel' rest with
              | Some next => pprod_tail fuel' next
          | None => None
          end
      | _ => Some input
      end
  end
with patom (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TNat :: rest | THex :: rest | TTrue :: rest | TFalse :: rest
      | TUnit :: rest | TName :: rest => Some rest
      | TMinus :: rest => patom fuel' rest
      | TLparen :: TRparen :: rest => Some rest
      | TLparen :: rest =>
          match pexpr fuel' rest with
          | Some (TComma :: rest) =>
              match pexpr fuel' rest with
              | Some rest => take TRparen rest
              | None => None
              end
          | Some rest => take TRparen rest
          | None => None
          end
      | TVec :: rest => pvec fuel' rest
      | TMake :: TName :: TName :: rest => pone fuel' rest
      | TMake :: TName :: TLbrace :: rest => pmake_fields fuel' rest
      | TFst :: rest | TSnd :: rest | TUncons :: rest | TAbs :: rest =>
          pone fuel' rest
      | TCat :: rest | TVcat :: rest | TStep :: rest => ptwo fuel' rest
      | TEqual :: rest => ptyped_two fuel' rest
      | TGood :: rest | TBad :: rest => ptyped_one fuel' rest
      | TTake :: rest | TDrop :: rest | TAt :: rest
      | TRead :: rest | TWrite :: rest | TEmit :: rest | TFail :: rest =>
          pindexed_one fuel' rest
      | TClose :: TLbrack :: rest => pindexed_after fuel' rest
      | TClose :: rest => pone fuel' rest
      | _ => None
      end
  end
with pone (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match take TLparen input with
      | Some rest =>
          match pexpr fuel' rest with
          | Some rest => take TRparen rest
          | None => None
          end
      | None => None
      end
  end
with ptwo (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match take TLparen input with
      | Some rest =>
          match pexpr fuel' rest with
          | Some rest =>
              match take TComma rest with
              | Some rest =>
                  match pexpr fuel' rest with
                  | Some rest => take TRparen rest
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  end
with ptyped_one (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match take TLbrack input with
      | Some rest =>
          match pty fuel' rest with
          | Some rest =>
              match take TRbrack rest with
              | Some rest => pone fuel' rest
              | None => None
              end
          | None => None
          end
      | None => None
      end
  end
with ptyped_two (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match take TLbrack input with
      | Some rest =>
          match pty fuel' rest with
          | Some rest =>
              match take TRbrack rest with
              | Some rest => ptwo fuel' rest
              | None => None
              end
          | None => None
          end
      | None => None
      end
  end
with pindexed_one (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match take TLbrack input with
      | Some rest => pindexed_after fuel' rest
      | None => None
      end
  end
with pindexed_after (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match take TNat input with
      | Some rest =>
          match take TRbrack rest with
          | Some rest => pone fuel' rest
          | None => None
          end
      | None => None
      end
  end
with pvec (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match take TLbrack input with
      | Some rest =>
          match pty fuel' rest with
          | Some rest =>
              match take TRbrack rest with
              | Some rest =>
                  match take TLparen rest with
                  | Some rest => pitems fuel' rest
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  end
with pitems (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TRparen :: rest => Some rest
      | _ =>
          match pexpr fuel' input with
          | Some (TComma :: rest) => pitems fuel' rest
          | Some rest => take TRparen rest
          | None => None
          end
      end
  end
with pdarms (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TName :: rest =>
          match pbind fuel' rest with
          | Some (TArrow :: rest) =>
              match pexpr fuel' rest with
              | Some (TBar :: rest) => pdarms fuel' rest
              | Some (TRbrace :: rest) => Some rest
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  end
with pmake_fields (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TName :: TEq :: rest =>
          match pexpr fuel' rest with
          | Some (TComma :: rest) => pmake_fields fuel' rest
          | Some (TRbrace :: rest) => Some rest
          | _ => None
          end
      | _ => None
      end
  end.

Fixpoint pcaps (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TRbrack :: rest => Some rest
      | _ =>
          match pbind fuel' input with
          | Some (TComma :: rest) => pcaps fuel' rest
          | Some rest => take TRbrack rest
          | None => None
          end
      end
  end.

Fixpoint pactuals (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TRbrack :: rest => Some rest
      | _ =>
          match pexpr fuel' input with
          | Some (TComma :: rest) => pactuals fuel' rest
          | Some rest => take TRbrack rest
          | None => None
          end
      end
  end.

Definition pmark (input : list tok) : out :=
  match input with
  | TRead :: TLbrack :: TNat :: TRbrack :: rest => Some rest
  | TWrite :: TLbrack :: TNat :: TRbrack :: rest => Some rest
  | TEmit :: TLbrack :: TNat :: TRbrack :: rest => Some rest
  | TFail :: TLbrack :: TNat :: TRbrack :: rest => Some rest
  | TClose :: TLbrack :: TNat :: TRbrack :: rest => Some rest
  | _ => None
  end.

Fixpoint prows (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TRbrace :: rest => Some rest
      | _ =>
          match pmark input with
          | Some (TComma :: rest) => prows fuel' rest
          | Some rest => take TRbrace rest
          | None => None
          end
      end
  end.

Definition punder (input : list tok) : out :=
  match input with
  | TUnder :: TLbrace :: TSteps :: TLbrack :: TNat :: TRbrack ::
      TComma :: TDepth :: TLbrack :: TNat :: TRbrack ::
      TComma :: TWork :: TLbrack :: TNat :: TRbrack :: TRbrace :: rest =>
      Some rest
  | _ => None
  end.

Fixpoint pnames (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TName :: TComma :: rest => pnames fuel' rest
      | TName :: TRbrack :: rest => Some rest
      | _ => None
      end
  end.

Fixpoint plaws (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match pidx_add fuel' input with
      | Some (TEq :: rest) | Some (TLe :: rest) =>
          match pidx_add fuel' rest with
          | Some (TComma :: tail) => plaws fuel' tail
          | Some (TRbrack :: tail) => Some tail
          | _ => None
          end
      | _ => None
      end
  end.

Fixpoint pkpars (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TName :: TColon :: TData :: TComma :: rest
      | TName :: TColon :: TRes :: TComma :: rest => pkpars fuel' rest
      | TName :: TColon :: TData :: TRbrack :: rest
      | TName :: TColon :: TRes :: TRbrack :: rest => Some rest
      | _ => None
      end
  end.

Definition pform_body (fuel : nat) (input : list tok) : out :=
  match input with
  | TLbrack :: rest =>
      match pcaps fuel rest with
      | Some (TLparen :: rest) =>
          match pbind fuel rest with
          | Some (TRparen :: TThin :: TLbrack :: rest) =>
              match pmul rest with
              | Some (TRbrack :: rest) =>
                  match pty fuel rest with
                  | Some (TMarks :: TLbrace :: rest) =>
                      match prows fuel rest with
                      | Some (TUnder :: rest) =>
                          match punder (TUnder :: rest) with
                          | Some (TEq :: rest) => pexpr fuel rest
                          | _ => None
                          end
                      | Some (TEq :: rest) => pexpr fuel rest
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
  end.

Definition pform_size (fuel : nat) (input : list tok) : out :=
  match input with
  | TLaw :: TLbrack :: rest =>
      match plaws fuel rest with
      | Some tail => pform_body fuel tail
      | None => None
      end
  | _ => pform_body fuel input
  end.

Definition pform (fuel : nat) (input : list tok) : out :=
  match input with
  | TForm :: TName :: TKind :: TLbrack :: rest =>
      match pkpars fuel rest with
      | Some (TSize :: TLbrack :: sized) =>
          match pnames fuel sized with
          | Some rest => pform_size fuel rest
          | None => None
          end
      | Some rest => pform_body fuel rest
      | None => None
      end
  | TForm :: TName :: TSize :: TLbrack :: rest =>
      match pnames fuel rest with
      | Some rest => pform_size fuel rest
      | None => None
      end
  | TForm :: TName :: rest => pform_body fuel rest
  | _ => None
  end.

Fixpoint ptypes (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match pty fuel' input with
      | Some (TComma :: rest) => ptypes fuel' rest
      | Some (TRbrack :: rest) => Some rest
      | _ => None
      end
  end.

Fixpoint pidxs (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match pidx_add fuel' input with
      | Some (TComma :: rest) => pidxs fuel' rest
      | Some (TRbrack :: rest) => Some rest
      | _ => None
      end
  end.

Definition puse_body (fuel : nat) (input : list tok) : out :=
  match input with
  | TLbrack :: rest =>
      match pactuals fuel rest with
      | Some (TLparen :: rest) =>
          match pexpr fuel rest with
          | Some (TRparen :: TAs :: rest) =>
              match pbind fuel rest with
              | Some (TIn :: rest) => Some rest
              | _ => None
              end
          | _ => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition puse (fuel : nat) (input : list tok) : out :=
  match input with
  | TUse :: TName :: TKind :: TLbrack :: rest =>
      match ptypes fuel rest with
      | Some (TSize :: TLbrack :: sized) =>
          match pidxs fuel sized with
          | Some rest => puse_body fuel rest
          | None => None
          end
      | Some rest => puse_body fuel rest
      | None => None
      end
  | TUse :: TName :: TSize :: TLbrack :: rest =>
      match pidxs fuel rest with
      | Some rest => puse_body fuel rest
      | None => None
      end
  | TUse :: TName :: rest => puse_body fuel rest
  | _ => None
  end.

Fixpoint pflow (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TLet :: rest =>
          match pbind fuel' rest with
          | Some (TEq :: rest) =>
              match pexpr fuel' rest with
              | Some (TIn :: rest) => pflow fuel' rest
              | _ => None
              end
          | _ => None
          end
      | TIf :: rest =>
          match pexpr fuel' rest with
          | Some (TThen :: rest) =>
              match pflow fuel' rest with
              | Some (TElse :: rest) => pflow fuel' rest
              | _ => None
              end
          | _ => None
          end
      | TUse :: _ =>
          match puse fuel' input with
          | Some rest => pflow fuel' rest
          | None => None
          end
      | _ => pexpr fuel' input
      end
  end.

Fixpoint pforms (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TForm :: _ =>
          match pform fuel' input with
          | Some rest => pforms fuel' rest
          | None => None
          end
      | TTerm :: rest => pflow fuel' rest
      | _ => None
      end
  end.

Definition pinput (fuel : nat) (input : list tok) : out := pbind fuel input.

Definition pctor (fuel : nat) (input : list tok) : out :=
  match input with
  | TName :: TLparen :: rest =>
      match pty fuel rest with
      | Some (TRparen :: rest) => Some rest
      | _ => None
      end
  | _ => None
  end.

Fixpoint pctors (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match pctor fuel' input with
      | Some (TBar :: rest) => pctors fuel' rest
      | other => other
      end
  end.

Definition pdata (fuel : nat) (input : list tok) : out :=
  match input with
  | TData :: TName :: TTag :: TNat :: TEq :: rest => pctors fuel rest
  | _ => None
  end.

Fixpoint psfields (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TName :: TColon :: rest =>
          match pty fuel' rest with
          | Some (TComma :: rest) => psfields fuel' rest
          | Some (TRbrace :: rest) => Some rest
          | _ => None
          end
      | _ => None
      end
  end.

Definition pshape (fuel : nat) (input : list tok) : out :=
  match input with
  | TShape :: TName :: TTag :: TNat :: TEq :: TLbrace :: rest =>
      psfields fuel rest
  | _ => None
  end.

Definition ppermit (input : list tok) : out :=
  match input with
  | TPermit :: TCap :: TLbrack :: TNat :: TRbrack :: TEq ::
      TStep :: TPlus :: TClose :: rest => Some rest
  | TPermit :: TCap :: TLbrack :: TNat :: TRbrack :: TEq ::
      TStep :: rest => Some rest
  | TPermit :: TCap :: TLbrack :: TNat :: TRbrack :: TEq ::
      TClose :: rest => Some rest
  | _ => None
  end.

Fixpoint pdecls (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TData :: _ =>
          match pdata fuel' input with
          | Some rest => pdecls fuel' rest
          | None => None
          end
      | TShape :: _ =>
          match pshape fuel' input with
          | Some rest => pdecls fuel' rest
          | None => None
          end
      | TInput :: rest =>
          match pinput fuel' rest with
          | Some rest => pdecls fuel' rest
          | None => None
          end
      | TPermit :: _ =>
          match ppermit input with
          | Some rest => pdecls fuel' rest
          | None => None
          end
      | TForm :: _ => pforms fuel' input
      | TTerm :: rest => pflow fuel' rest
      | _ => None
      end
  end.

Fixpoint pheads (fuel : nat) (input : list tok) {struct fuel} : out :=
  match fuel with
  | O => None
  | S fuel' =>
      match input with
      | TSize :: TName :: TEq :: TNat :: rest => pheads fuel' rest
      | TMeasure :: TName :: TEq :: rest =>
          match pidx_add fuel' rest with
          | Some rest => pheads fuel' rest
          | None => None
          end
      | TLaw :: rest =>
          match pidx_add fuel' rest with
          | Some (TEq :: rest) | Some (TLe :: rest) =>
              match pidx_add fuel' rest with
              | Some rest => pheads fuel' rest
              | None => None
              end
          | _ => None
          end
      | TInput :: rest =>
          match pinput fuel' rest with
          | Some rest => pheads fuel' rest
          | None => None
          end
      | TPermit :: _ => pdecls fuel' input
      | TData :: _ => pdecls fuel' input
      | TShape :: _ => pdecls fuel' input
      | TForm :: _ => pforms fuel' input
      | TTerm :: rest => pflow fuel' rest
      | _ => None
      end
  end.

Definition fuel (input : list tok) : nat := 8 * S (length input).

Fixpoint profile_b (input : list tok) : bool :=
  match input with
  | [] => true
  | THold item :: rest => allow item && profile_b rest
  | _ :: rest => profile_b rest
  end.

Definition parse_raw (input : list tok) : out :=
  match input with
  | TProgram :: TName :: TLbrace :: rest =>
      match pheads (fuel input) rest with
      | Some (TRbrace :: TEof :: []) => Some []
      | _ => None
      end
  | _ => None
  end.

Definition parse (input : list tok) : out :=
  if profile_b input then parse_raw input else None.

Definition accept (input : list tok) : bool :=
  match parse input with
  | Some [] => true
  | _ => false
  end.

Inductive grammar : list tok -> Prop :=
| Grammar : forall input, parse input = Some [] -> grammar input.

Theorem accept_sound : forall input,
  accept input = true -> grammar input.
Proof.
  intros input H.
  unfold accept in H.
  destruct (parse input) as [rest |] eqn:Hparse; try discriminate.
  destruct rest; try discriminate.
  constructor. exact Hparse.
Qed.

Theorem accept_complete : forall input,
  grammar input -> accept input = true.
Proof.
  intros input H.
  inversion H as [tokens Hparse]. subst.
  unfold accept. rewrite Hparse. reflexivity.
Qed.

Theorem accept_exact : forall input,
  accept input = true -> parse input = Some [].
Proof.
  intros input H.
  apply accept_sound in H.
  inversion H. assumption.
Qed.

Theorem held_refused : forall item input,
  held item = true ->
  accept (THold item :: input) = false.
Proof.
  intros item input H.
  destruct item; simpl in H |- *; try discriminate; reflexivity.
Qed.