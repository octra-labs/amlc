(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Require Import Uni.
Require Import Bin.

Import ListNotations.

Fixpoint list_code {A : Type} (put : A -> code) (values : list A) : code :=
  match values with
  | [] => CNil
  | first :: rest => CCons (put first) (list_code put rest)
  end.

Fixpoint list_get {A : Type} (get : code -> option A) (input : code)
    : option (list A) :=
  match input with
  | CNil => Some []
  | CCons first rest =>
      match get first, list_get get rest with
      | Some value, Some values => Some (value :: values)
      | _, _ => None
      end
  | _ => None
  end.

Lemma list_get_code : forall (A : Type) (put : A -> code)
    (get : code -> option A) (values : list A),
  (forall value, In value values -> get (put value) = Some value) ->
  list_get get (list_code put values) = Some values.
Proof.
  intros A put get values exact_one.
  induction values; simpl.
  - reflexivity.
  - rewrite exact_one, IHvalues.
    + reflexivity.
    + intros value present.
      apply exact_one.
      right.
      exact present.
    + left.
      reflexivity.
Qed.

Definition num_get (input : code) : option nat :=
  match input with
  | CNum value => Some value
  | _ => None
  end.

Lemma num_get_code : forall value, num_get (CNum value) = Some value.
Proof.
  intros value.
  reflexivity.
Qed.

Fixpoint ty_code (typ : ty) : code :=
  match typ with
  | TUnit => CTag 0 CNil
  | TBool => CTag 1 CNil
  | TInt => CTag 2 CNil
  | TBytes len => CTag 3 (CNum len)
  | TVec len elem => CTag 4 (CCons (CNum len) (CCons (ty_code elem) CNil))
  | TCap kind => CTag 5 (CNum kind)
  | TPair first second =>
      CTag 6 (CCons (ty_code first) (CCons (ty_code second) CNil))
  | TSum first second =>
      CTag 7 (CCons (ty_code first) (CCons (ty_code second) CNil))
  | TEnc key rem => CTag 8 (CCons (CNum key) (CCons (CNum rem) CNil))
  end.

Fixpoint ty_get (input : code) : option ty :=
  match input with
  | CTag 0 CNil => Some TUnit
  | CTag 1 CNil => Some TBool
  | CTag 2 CNil => Some TInt
  | CTag 3 (CNum len) => Some (TBytes len)
  | CTag 4 (CCons (CNum len) (CCons elem CNil)) =>
      match ty_get elem with
      | Some typ => Some (TVec len typ)
      | None => None
      end
  | CTag 5 (CNum kind) => Some (TCap kind)
  | CTag 6 (CCons first (CCons second CNil)) =>
      match ty_get first, ty_get second with
      | Some first_ty, Some second_ty => Some (TPair first_ty second_ty)
      | _, _ => None
      end
  | CTag 7 (CCons first (CCons second CNil)) =>
      match ty_get first, ty_get second with
      | Some first_ty, Some second_ty => Some (TSum first_ty second_ty)
      | _, _ => None
      end
  | CTag 8 (CCons (CNum key) (CCons (CNum rem) CNil)) =>
      Some (TEnc key rem)
  | _ => None
  end.

Lemma ty_get_code : forall typ, ty_get (ty_code typ) = Some typ.
Proof.
  induction typ; simpl; rewrite ?IHtyp, ?IHtyp1, ?IHtyp2; reflexivity.
Qed.

Definition atom_code (action : atom) : code :=
  match action with
  | ARead kind => CTag 0 (CNum kind)
  | AWrite kind => CTag 1 (CNum kind)
  | AEmit kind => CTag 2 (CNum kind)
  | AFail kind => CTag 3 (CNum kind)
  | AClose kind => CTag 4 (CNum kind)
  end.

Definition atom_get (input : code) : option atom :=
  match input with
  | CTag 0 (CNum kind) => Some (ARead kind)
  | CTag 1 (CNum kind) => Some (AWrite kind)
  | CTag 2 (CNum kind) => Some (AEmit kind)
  | CTag 3 (CNum kind) => Some (AFail kind)
  | CTag 4 (CNum kind) => Some (AClose kind)
  | _ => None
  end.

Lemma atom_get_code : forall action,
  atom_get (atom_code action) = Some action.
Proof.
  intros action.
  destruct action; reflexivity.
Qed.

Fixpoint value_code (item : value) : code :=
  match item with
  | VUnit => CTag 0 CNil
  | VBool false => CTag 1 (CNum 0)
  | VBool true => CTag 1 (CNum 1)
  | VInt number => CTag 2 (CInt number)
  | VBytes bytes => CTag 3 (list_code CNum bytes)
  | VVec values => CTag 4 (list_code value_code values)
  | VCap kind id => CTag 5 (CCons (CNum kind) (CCons (CNum id) CNil))
  | VPair first second =>
      CTag 6 (CCons (value_code first) (CCons (value_code second) CNil))
  | VInl value => CTag 7 (value_code value)
  | VInr value => CTag 8 (value_code value)
  | VEnc key rem field =>
      CTag 9 (CCons (CNum key) (CCons (CNum rem) (CCons (CInt field) CNil)))
  end.

Fixpoint value_get (input : code) : option value :=
  match input with
  | CTag 0 CNil => Some VUnit
  | CTag 1 (CNum 0) => Some (VBool false)
  | CTag 1 (CNum 1) => Some (VBool true)
  | CTag 2 (CInt number) => Some (VInt number)
  | CTag 3 body =>
      match list_get num_get body with
      | Some bytes => Some (VBytes bytes)
      | None => None
      end
  | CTag 4 body =>
      match list_get value_get body with
      | Some values => Some (VVec values)
      | None => None
      end
  | CTag 5 (CCons (CNum kind) (CCons (CNum id) CNil)) =>
      Some (VCap kind id)
  | CTag 6 (CCons first (CCons second CNil)) =>
      match value_get first, value_get second with
      | Some first_value, Some second_value =>
          Some (VPair first_value second_value)
      | _, _ => None
      end
  | CTag 7 body =>
      match value_get body with
      | Some value => Some (VInl value)
      | None => None
      end
  | CTag 8 body =>
      match value_get body with
      | Some value => Some (VInr value)
      | None => None
      end
  | CTag 9 (CCons (CNum key) (CCons (CNum rem) (CCons (CInt field) CNil))) =>
      Some (VEnc key rem field)
  | _ => None
  end.

Fixpoint vsize (item : value) : nat :=
  match item with
  | VUnit | VBool _ | VInt _ | VBytes _ | VCap _ _ | VEnc _ _ _ => 1
  | VVec values =>
      S (fold_right (fun value size => vsize value + size) 0 values)
  | VPair first second => S (vsize first + vsize second)
  | VInl value | VInr value => S (vsize value)
  end.

Lemma vsize_in : forall item values,
  In item values ->
  vsize item <= fold_right (fun value size => vsize value + size) 0 values.
Proof.
  intros item values present.
  induction values as [|first rest repeat]; simpl in *.
  - contradiction.
  - destruct present as [same | present].
    + subst first.
      lia.
    + pose proof (repeat present).
      lia.
Qed.

Lemma value_get_code : forall item,
  value_get (value_code item) = Some item.
Proof.
  intros item.
  remember (vsize item) as size eqn:exact_size.
  revert item exact_size.
  induction size using lt_wf_ind.
  intros item exact_size.
  destruct item; simpl in exact_size; simpl.
  - reflexivity.
  - destruct b; reflexivity.
  - reflexivity.
  - rewrite list_get_code.
    + reflexivity.
    + intros value _.
      apply num_get_code.
  - rewrite list_get_code.
    + reflexivity.
    + intros value present.
      apply H with (m := vsize value).
      * rewrite exact_size.
        simpl.
        pose proof (vsize_in value l present).
        lia.
      * reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite (H (vsize item1)), (H (vsize item2)); try reflexivity;
      rewrite exact_size; simpl; lia.
  - rewrite (H (vsize item)); try reflexivity;
      rewrite exact_size; simpl; lia.
  - rewrite (H (vsize item)); try reflexivity;
      rewrite exact_size; simpl; lia.
Qed.

Definition res_code (value : res) : code :=
  CTag 0 (CCons (CNum (rsteps value))
    (CCons (CNum (rdepth value)) (CCons (CNum (rwork value)) CNil))).

Definition res_get (input : code) : option res :=
  match input with
  | CTag 0 (CCons (CNum steps)
      (CCons (CNum depth) (CCons (CNum work) CNil))) =>
      Some (Res steps depth work)
  | _ => None
  end.

Lemma res_get_code : forall value, res_get (res_code value) = Some value.
Proof.
  intros [steps depth work].
  reflexivity.
Qed.

Inductive snap : Type :=
| Refuse : snap
| Reject : reject -> snap
| Accept : ty -> list atom -> res -> value -> list atom -> res -> snap.

Definition reject_code (reason : reject) : code :=
  match reason with
  | DivideZero => CNum 0
  | ModuloZero => CNum 1
  end.

Definition reject_get (input : code) : option reject :=
  match input with
  | CNum 0 => Some DivideZero
  | CNum 1 => Some ModuloZero
  | _ => None
  end.

Lemma reject_get_code : forall reason,
  reject_get (reject_code reason) = Some reason.
Proof.
  intros reason.
  destruct reason; reflexivity.
Qed.

Definition snap_code (value : snap) : code :=
  match value with
  | Refuse => CTag 0 CNil
  | Reject reason => CTag 2 (reject_code reason)
  | Accept typ row limit out plan used =>
      CTag 1 (CCons (ty_code typ)
        (CCons (list_code atom_code row)
          (CCons (res_code limit)
            (CCons (value_code out)
              (CCons (list_code atom_code plan)
                (CCons (res_code used) CNil))))))
  end.

Definition snap_get (input : code) : option snap :=
  match input with
  | CTag 0 CNil => Some Refuse
  | CTag 2 body =>
      match reject_get body with
      | Some reason => Some (Reject reason)
      | None => None
      end
  | CTag 1 (CCons typ
      (CCons row (CCons limit (CCons out (CCons plan (CCons used CNil)))))) =>
      match ty_get typ, list_get atom_get row, res_get limit,
        value_get out, list_get atom_get plan, res_get used with
      | Some out_ty, Some out_row, Some out_limit,
          Some out_value, Some out_plan, Some out_used =>
          Some (Accept out_ty out_row out_limit out_value out_plan out_used)
      | _, _, _, _, _, _ => None
      end
  | _ => None
  end.

Lemma snap_get_code : forall value, snap_get (snap_code value) = Some value.
Proof.
  intros value.
  destruct value; simpl.
  - reflexivity.
  - rewrite reject_get_code.
    reflexivity.
  - destruct r, r0; simpl.
    rewrite ty_get_code, list_get_code, value_get_code, list_get_code.
    + reflexivity.
    + intros action _.
      apply atom_get_code.
    + intros action _.
      apply atom_get_code.
Qed.

Definition enc {A : Type} (put : A -> code) (value : A) : bits :=
  put_code (put value).

Definition dec {A : Type} (put : A -> code) (get : code -> option A)
    (input : bits) : option A :=
  match get_code input with
  | Some shape =>
      match get shape with
      | Some value =>
          if code_eqb (put value) shape then Some value else None
      | None => None
      end
  | None => None
  end.

Lemma dec_enc : forall (A : Type) (put : A -> code)
    (get : code -> option A) value,
  get (put value) = Some value ->
  dec put get (enc put value) = Some value.
Proof.
  intros A put get value exact_value.
  unfold dec, enc.
  rewrite get_code_put, exact_value.
  rewrite (proj2 (code_eqb_eq (put value) (put value)) eq_refl).
  reflexivity.
Qed.

Lemma enc_dec : forall (A : Type) (put : A -> code)
    (get : code -> option A) input value,
  dec put get input = Some value ->
  enc put value = input.
Proof.
  intros A put get input value accepted.
  unfold dec in accepted.
  destruct (get_code input) as [shape |] eqn:shape_ok; try discriminate.
  destruct (get shape) as [found |] eqn:value_ok; try discriminate.
  destruct (code_eqb (put found) shape) eqn:same; try discriminate.
  inversion accepted; subst.
  unfold enc.
  apply code_eqb_eq in same.
  rewrite same.
  apply put_code_get.
  exact shape_ok.
Qed.

Definition enc_ty := enc ty_code.
Definition dec_ty := dec ty_code ty_get.
Definition enc_value := enc value_code.
Definition dec_value := dec value_code value_get.
Definition row_code := list_code atom_code.
Definition row_get := list_get atom_get.
Definition enc_row := enc row_code.
Definition dec_row := dec row_code row_get.
Definition enc_res := enc res_code.
Definition dec_res := dec res_code res_get.
Definition enc_snap := enc snap_code.
Definition dec_snap := dec snap_code snap_get.

Theorem ty_decode_encode : forall value,
  dec_ty (enc_ty value) = Some value.
Proof.
  intros value.
  apply dec_enc.
  apply ty_get_code.
Qed.

Theorem ty_encode_decode : forall input value,
  dec_ty input = Some value -> enc_ty value = input.
Proof.
  apply enc_dec.
Qed.

Theorem value_decode_encode : forall value,
  dec_value (enc_value value) = Some value.
Proof.
  intros value.
  apply dec_enc.
  apply value_get_code.
Qed.

Theorem value_encode_decode : forall input value,
  dec_value input = Some value -> enc_value value = input.
Proof.
  apply enc_dec.
Qed.

Theorem row_decode_encode : forall value,
  dec_row (enc_row value) = Some value.
Proof.
  intros value.
  apply dec_enc.
  apply list_get_code.
  intros action _.
  apply atom_get_code.
Qed.

Theorem row_encode_decode : forall input value,
  dec_row input = Some value -> enc_row value = input.
Proof.
  apply enc_dec.
Qed.

Theorem res_decode_encode : forall value,
  dec_res (enc_res value) = Some value.
Proof.
  intros value.
  apply dec_enc.
  apply res_get_code.
Qed.

Theorem res_encode_decode : forall input value,
  dec_res input = Some value -> enc_res value = input.
Proof.
  apply enc_dec.
Qed.

Theorem snap_decode_encode : forall value,
  dec_snap (enc_snap value) = Some value.
Proof.
  intros value.
  apply dec_enc.
  apply snap_get_code.
Qed.

Theorem snap_encode_decode : forall input value,
  dec_snap input = Some value -> enc_snap value = input.
Proof.
  apply enc_dec.
Qed.