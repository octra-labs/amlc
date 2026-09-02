(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Uni.
Require Import Dec.
Require Import Lim.
Require Import Bin.
Require Import Ser.
Require Import Low.
Require Import Rule.

Import ListNotations.

Definition program := (list bind * tm)%type.

Definition mul_code (value : mul) : code :=
  match value with
  | M0 => CTag 0 CNil
  | M1 => CTag 1 CNil
  | MM => CTag 2 CNil
  end.

Definition mul_get (input : code) : option mul :=
  match input with
  | CTag 0 CNil => Some M0
  | CTag 1 CNil => Some M1
  | CTag 2 CNil => Some MM
  | _ => None
  end.

Lemma mul_get_code : forall value,
  mul_get (mul_code value) = Some value.
Proof.
  intros value. destruct value; reflexivity.
Qed.

Definition rel_code (value : rel) : code :=
  match value with
  | RLt => CTag 0 CNil
  | RLe => CTag 1 CNil
  | RGt => CTag 2 CNil
  | RGe => CTag 3 CNil
  end.

Definition rel_get (input : code) : option rel :=
  match input with
  | CTag 0 CNil => Some RLt
  | CTag 1 CNil => Some RLe
  | CTag 2 CNil => Some RGt
  | CTag 3 CNil => Some RGe
  | _ => None
  end.

Lemma rel_get_code : forall value,
  rel_get (rel_code value) = Some value.
Proof.
  intros value. destruct value; reflexivity.
Qed.

Definition bind_code (value : bind) : code :=
  CTag 0 (CCons (CNum (bid value))
    (CCons (mul_code (bmul value)) (CCons (ty_code (bty value)) CNil))).

Definition bind_get (input : code) : option bind :=
  match input with
  | CTag 0 (CCons (CNum id) (CCons mode (CCons typ CNil))) =>
      match mul_get mode, ty_get typ with
      | Some mode', Some typ' => Some (Bind id mode' typ')
      | _, _ => None
      end
  | _ => None
  end.

Lemma bind_get_code : forall value,
  bind_get (bind_code value) = Some value.
Proof.
  intros [id mode typ]. simpl.
  rewrite mul_get_code, ty_get_code. reflexivity.
Qed.

Fixpoint tm_code (term : tm) : code :=
  match term with
  | K value typ =>
      CTag 0 (CCons (value_code value) (CCons (ty_code typ) CNil))
  | Bytes bytes => CTag 1 (list_code CNum bytes)
  | Vnil elem => CTag 2 (ty_code elem)
  | Var id => CTag 3 (CNum id)
  | Let binder value body =>
      CTag 4 (CCons (bind_code binder)
        (CCons (tm_code value) (CCons (tm_code body) CNil)))
  | If guard yes no =>
      CTag 5 (CCons (tm_code guard)
        (CCons (tm_code yes) (CCons (tm_code no) CNil)))
  | Pair first second =>
      CTag 6 (CCons (tm_code first) (CCons (tm_code second) CNil))
  | Unpair product first second body =>
      CTag 7 (CCons (tm_code product)
        (CCons (bind_code first)
          (CCons (bind_code second) (CCons (tm_code body) CNil))))
  | Fst value => CTag 8 (tm_code value)
  | Snd value => CTag 9 (tm_code value)
  | Inl value other =>
      CTag 10 (CCons (tm_code value) (CCons (ty_code other) CNil))
  | Inr other value =>
      CTag 11 (CCons (ty_code other) (CCons (tm_code value) CNil))
  | Case value first yes second no =>
      CTag 12 (CCons (tm_code value)
        (CCons (bind_code first)
          (CCons (tm_code yes)
            (CCons (bind_code second) (CCons (tm_code no) CNil)))))
  | Act action body =>
      CTag 13 (CCons (atom_code action) (CCons (tm_code body) CNil))
  | Add first second =>
      CTag 14 (CCons (tm_code first) (CCons (tm_code second) CNil))
  | Eq typ first second =>
      CTag 15 (CCons (ty_code typ)
        (CCons (tm_code first) (CCons (tm_code second) CNil)))
  | Cat first second =>
      CTag 16 (CCons (tm_code first) (CCons (tm_code second) CNil))
  | Take len value =>
      CTag 17 (CCons (CNum len) (CCons (tm_code value) CNil))
  | Drop len value =>
      CTag 18 (CCons (CNum len) (CCons (tm_code value) CNil))
  | Vcons first rest =>
      CTag 19 (CCons (tm_code first) (CCons (tm_code rest) CNil))
  | Vcat first second =>
      CTag 20 (CCons (tm_code first) (CCons (tm_code second) CNil))
  | At index value =>
      CTag 21 (CCons (CNum index) (CCons (tm_code value) CNil))
  | Uncons value => CTag 22 (tm_code value)
  | Fold len vector seed item state body =>
      CTag 23 (CCons (CNum len)
        (CCons (tm_code vector)
          (CCons (tm_code seed)
            (CCons (bind_code item)
              (CCons (bind_code state) (CCons (tm_code body) CNil))))))
  | Step cap value =>
      CTag 24 (CCons (tm_code cap) (CCons (tm_code value) CNil))
  | Close cap => CTag 25 (tm_code cap)
  | Sub first second =>
      CTag 26 (CCons (tm_code first) (CCons (tm_code second) CNil))
  | Mul first second =>
      CTag 27 (CCons (tm_code first) (CCons (tm_code second) CNil))
  | Div first second =>
      CTag 28 (CCons (tm_code first) (CCons (tm_code second) CNil))
  | Mod first second =>
      CTag 29 (CCons (tm_code first) (CCons (tm_code second) CNil))
  | Neg value => CTag 30 (tm_code value)
  | Abs value => CTag 31 (tm_code value)
  | Cmp kind first second =>
      CTag 32 (CCons (rel_code kind)
        (CCons (tm_code first) (CCons (tm_code second) CNil)))
  end.

Fixpoint tm_get (input : code) : option tm :=
  match input with
  | CTag 0 (CCons value (CCons typ CNil)) =>
      match value_get value, ty_get typ with
      | Some value', Some typ' => Some (K value' typ')
      | _, _ => None
      end
  | CTag 1 body =>
      match list_get num_get body with
      | Some bytes => Some (Bytes bytes)
      | None => None
      end
  | CTag 2 elem =>
      match ty_get elem with
      | Some elem' => Some (Vnil elem')
      | None => None
      end
  | CTag 3 (CNum id) => Some (Var id)
  | CTag 4 (CCons binder (CCons value (CCons body CNil))) =>
      match bind_get binder, tm_get value, tm_get body with
      | Some binder', Some value', Some body' =>
          Some (Let binder' value' body')
      | _, _, _ => None
      end
  | CTag 5 (CCons guard (CCons yes (CCons no CNil))) =>
      match tm_get guard, tm_get yes, tm_get no with
      | Some guard', Some yes', Some no' => Some (If guard' yes' no')
      | _, _, _ => None
      end
  | CTag 6 (CCons first (CCons second CNil)) =>
      match tm_get first, tm_get second with
      | Some first', Some second' => Some (Pair first' second')
      | _, _ => None
      end
  | CTag 7 (CCons product
      (CCons first (CCons second (CCons body CNil)))) =>
      match tm_get product, bind_get first, bind_get second, tm_get body with
      | Some product', Some first', Some second', Some body' =>
          Some (Unpair product' first' second' body')
      | _, _, _, _ => None
      end
  | CTag 8 value =>
      match tm_get value with Some value' => Some (Fst value') | None => None end
  | CTag 9 value =>
      match tm_get value with Some value' => Some (Snd value') | None => None end
  | CTag 10 (CCons value (CCons other CNil)) =>
      match tm_get value, ty_get other with
      | Some value', Some other' => Some (Inl value' other')
      | _, _ => None
      end
  | CTag 11 (CCons other (CCons value CNil)) =>
      match ty_get other, tm_get value with
      | Some other', Some value' => Some (Inr other' value')
      | _, _ => None
      end
  | CTag 12 (CCons value
      (CCons first (CCons yes (CCons second (CCons no CNil))))) =>
      match tm_get value, bind_get first, tm_get yes,
        bind_get second, tm_get no with
      | Some value', Some first', Some yes', Some second', Some no' =>
          Some (Case value' first' yes' second' no')
      | _, _, _, _, _ => None
      end
  | CTag 13 (CCons action (CCons body CNil)) =>
      match atom_get action, tm_get body with
      | Some action', Some body' => Some (Act action' body')
      | _, _ => None
      end
  | CTag 14 (CCons first (CCons second CNil)) =>
      match tm_get first, tm_get second with
      | Some first', Some second' => Some (Add first' second')
      | _, _ => None
      end
  | CTag 15 (CCons typ (CCons first (CCons second CNil))) =>
      match ty_get typ, tm_get first, tm_get second with
      | Some typ', Some first', Some second' => Some (Eq typ' first' second')
      | _, _, _ => None
      end
  | CTag 16 (CCons first (CCons second CNil)) =>
      match tm_get first, tm_get second with
      | Some first', Some second' => Some (Cat first' second')
      | _, _ => None
      end
  | CTag 17 (CCons (CNum len) (CCons value CNil)) =>
      match tm_get value with Some value' => Some (Take len value') | None => None end
  | CTag 18 (CCons (CNum len) (CCons value CNil)) =>
      match tm_get value with Some value' => Some (Drop len value') | None => None end
  | CTag 19 (CCons first (CCons rest CNil)) =>
      match tm_get first, tm_get rest with
      | Some first', Some rest' => Some (Vcons first' rest')
      | _, _ => None
      end
  | CTag 20 (CCons first (CCons second CNil)) =>
      match tm_get first, tm_get second with
      | Some first', Some second' => Some (Vcat first' second')
      | _, _ => None
      end
  | CTag 21 (CCons (CNum index) (CCons value CNil)) =>
      match tm_get value with Some value' => Some (At index value') | None => None end
  | CTag 22 value =>
      match tm_get value with Some value' => Some (Uncons value') | None => None end
  | CTag 23 (CCons (CNum len)
      (CCons vector (CCons seed
        (CCons item (CCons state (CCons body CNil)))))) =>
      match tm_get vector, tm_get seed, bind_get item,
        bind_get state, tm_get body with
      | Some vector', Some seed', Some item', Some state', Some body' =>
          Some (Fold len vector' seed' item' state' body')
      | _, _, _, _, _ => None
      end
  | CTag 24 (CCons cap (CCons value CNil)) =>
      match tm_get cap, tm_get value with
      | Some cap', Some value' => Some (Step cap' value')
      | _, _ => None
      end
  | CTag 25 cap =>
      match tm_get cap with Some cap' => Some (Close cap') | None => None end
  | CTag 26 (CCons first (CCons second CNil)) =>
      match tm_get first, tm_get second with
      | Some first', Some second' => Some (Sub first' second')
      | _, _ => None
      end
  | CTag 27 (CCons first (CCons second CNil)) =>
      match tm_get first, tm_get second with
      | Some first', Some second' => Some (Mul first' second')
      | _, _ => None
      end
  | CTag 28 (CCons first (CCons second CNil)) =>
      match tm_get first, tm_get second with
      | Some first', Some second' => Some (Div first' second')
      | _, _ => None
      end
  | CTag 29 (CCons first (CCons second CNil)) =>
      match tm_get first, tm_get second with
      | Some first', Some second' => Some (Mod first' second')
      | _, _ => None
      end
  | CTag 30 value =>
      match tm_get value with Some value' => Some (Neg value') | None => None end
  | CTag 31 value =>
      match tm_get value with Some value' => Some (Abs value') | None => None end
  | CTag 32 (CCons kind (CCons first (CCons second CNil))) =>
      match rel_get kind, tm_get first, tm_get second with
      | Some kind', Some first', Some second' => Some (Cmp kind' first' second')
      | _, _, _ => None
      end
  | _ => None
  end.

Lemma nums_get_code : forall values,
  list_get num_get (list_code CNum values) = Some values.
Proof.
  intros values.
  apply list_get_code.
  intros value _.
  apply num_get_code.
Qed.

Lemma tm_get_code : forall term,
  tm_get (tm_code term) = Some term.
Proof.
  induction term; simpl;
    rewrite ?value_get_code, ?ty_get_code, ?nums_get_code,
      ?bind_get_code, ?atom_get_code, ?rel_get_code,
      ?IHterm, ?IHterm1, ?IHterm2, ?IHterm3;
    try reflexivity.
  all: repeat match goal with
  | value : bind |- _ => destruct value
  end; simpl; rewrite ?mul_get_code; reflexivity.
Qed.

Definition prog_code (value : program) : code :=
  let '(binds, term) := value in
  CTag 26 (CCons (list_code bind_code binds) (CCons (tm_code term) CNil)).

Definition prog_shape (input : code) : option program :=
  match input with
  | CTag 26 (CCons binds (CCons term CNil)) =>
      match list_get bind_get binds, tm_get term with
      | Some binds', Some term' => Some (binds', term')
      | _, _ => None
      end
  | _ => None
  end.

Lemma prog_shape_code : forall value,
  prog_shape (prog_code value) = Some value.
Proof.
  intros [binds term]. simpl.
  rewrite list_get_code, tm_get_code.
  - reflexivity.
  - intros binder _.
    apply bind_get_code.
Qed.

Fixpoint ty_depth (typ : ty) : nat :=
  match typ with
  | TUnit | TBool | TInt | TBytes _ | TCap _ | TEnc _ _ => 0
  | TVec _ elem => S (ty_depth elem)
  | TPair first second | TSum first second =>
      S (Nat.max (ty_depth first) (ty_depth second))
  end.

Fixpoint ty_nodes (typ : ty) : nat :=
  match typ with
  | TUnit | TBool | TInt | TBytes _ | TCap _ | TEnc _ _ => 1
  | TVec _ elem => S (ty_nodes elem)
  | TPair first second | TSum first second =>
      S (ty_nodes first + ty_nodes second)
  end.

Definition ty_shape_b (typ : ty) : bool :=
  Nat.leb (ty_depth typ) (rty_depth local)
    && Nat.leb (ty_nodes typ) (rty_nodes local).

Definition bind_shape_b (value : bind) : bool :=
  bind_b value && ty_shape_b (bty value).

Fixpoint tm_image (term : tm) : bool :=
  match term with
  | K VUnit TUnit | K (VBool _) TBool | K (VInt _) TInt => true
  | K _ _ => false
  | Bytes _ | Var _ => true
  | Vnil elem => ty_shape_b elem
  | Vcons first rest => tm_image first && vec_image rest
  | Let binder value body =>
      bind_shape_b binder && tm_image value && tm_image body
  | If guard yes no => tm_image guard && tm_image yes && tm_image no
  | Pair first second | Add first second | Sub first second
  | Mul first second | Div first second | Mod first second | Cat first second
  | Vcat first second | Step first second => tm_image first && tm_image second
  | Unpair product first second body =>
      tm_image product && bind_shape_b first && bind_shape_b second
        && tm_image body
  | Fst value | Snd value | Neg value | Abs value
  | Uncons value | Close value => tm_image value
  | Inl value other => tm_image value && ty_shape_b other
  | Inr other value => ty_shape_b other && tm_image value
  | Case value first yes second no =>
      tm_image value && bind_shape_b first && tm_image yes
        && bind_shape_b second && tm_image no
  | Act _ body => tm_image body
  | Eq typ first second =>
      ty_shape_b typ && tm_image first && tm_image second
  | Cmp _ first second => tm_image first && tm_image second
  | Take _ value | Drop _ value | At _ value => tm_image value
  | Fold _ vector seed item state body =>
      tm_image vector && tm_image seed && bind_shape_b item
        && bind_shape_b state && tm_image body
  end
with vec_image (term : tm) : bool :=
  match term with
  | Vnil elem => ty_shape_b elem
  | Vcons first rest => tm_image first && vec_image rest
  | _ => false
  end.

Fixpoint tm_depth (term : tm) : nat :=
  match term with
  | K _ _ | Bytes _ | Vnil _ | Var _ => 0
  | Let _ value body | Pair value body | Add value body | Sub value body
  | Mul value body | Div value body | Mod value body | Cat value body
  | Vcat value body | Step value body =>
      S (Nat.max (tm_depth value) (tm_depth body))
  | If guard yes no =>
      S (Nat.max (tm_depth guard) (Nat.max (tm_depth yes) (tm_depth no)))
  | Unpair product _ _ body =>
      S (Nat.max (tm_depth product) (tm_depth body))
  | Fst value | Snd value | Neg value | Abs value
  | Inl value _ | Inr _ value | Act _ value
  | Take _ value | Drop _ value | At _ value | Uncons value | Close value =>
      S (tm_depth value)
  | Case value _ yes _ no =>
      S (Nat.max (tm_depth value) (Nat.max (tm_depth yes) (tm_depth no)))
  | Eq _ first second | Cmp _ first second =>
      S (Nat.max (tm_depth first) (tm_depth second))
  | Vcons first rest => S (Nat.max (tm_depth first) (vec_depth rest))
  | Fold _ vector seed _ _ body =>
      S (Nat.max (tm_depth vector)
        (Nat.max (tm_depth seed) (tm_depth body)))
  end
with vec_depth (term : tm) : nat :=
  match term with
  | Vnil _ => 0
  | Vcons first rest => Nat.max (tm_depth first) (vec_depth rest)
  | _ => 0
  end.

Fixpoint tm_nodes (term : tm) : nat :=
  match term with
  | K _ _ | Bytes _ | Vnil _ | Var _ => 1
  | Let _ value body | Pair value body | Add value body | Sub value body
  | Mul value body | Div value body | Mod value body | Cat value body
  | Vcat value body | Step value body =>
      S (tm_nodes value + tm_nodes body)
  | If guard yes no => S (tm_nodes guard + tm_nodes yes + tm_nodes no)
  | Unpair product _ _ body => S (tm_nodes product + tm_nodes body)
  | Fst value | Snd value | Neg value | Abs value
  | Inl value _ | Inr _ value | Act _ value
  | Take _ value | Drop _ value | At _ value | Uncons value | Close value =>
      S (tm_nodes value)
  | Case value _ yes _ no =>
      S (tm_nodes value + tm_nodes yes + tm_nodes no)
  | Eq _ first second | Cmp _ first second =>
      S (tm_nodes first + tm_nodes second)
  | Vcons first rest => S (tm_nodes first + vec_nodes rest)
  | Fold _ vector seed _ _ body =>
      S (tm_nodes vector + tm_nodes seed + tm_nodes body)
  end
with vec_nodes (term : tm) : nat :=
  match term with
  | Vnil _ => 0
  | Vcons first rest => tm_nodes first + vec_nodes rest
  | _ => 0
  end.

Definition checked_b (binds : list bind) (term : tm) : bool :=
  match opens [] binds with
  | Some gamma =>
      match checkb gamma term with
      | Some (_, _, _, next) => doneb next
      | None => false
      end
  | None => false
  end.

Definition prog_b (value : program) : bool :=
  let '(binds, term) := value in
  Nat.leb (length binds) (rinputs local)
    && forallb bind_shape_b binds
    && tm_b term
    && tm_image term
    && Nat.leb (tm_depth term) (rtm_depth local)
    && Nat.leb (tm_nodes term) (rtm_nodes local)
    && checked_b binds term
    && Nat.leb (length (put_code (prog_code value))) (rstr local).

Definition prog_get (input : code) : option program :=
  match prog_shape input with
  | Some value => if prog_b value then Some value else None
  | None => None
  end.

Lemma prog_get_code : forall value,
  prog_b value = true ->
  prog_get (prog_code value) = Some value.
Proof.
  intros value valid.
  unfold prog_get.
  rewrite prog_shape_code, valid.
  reflexivity.
Qed.

Lemma prog_get_b : forall input value,
  prog_get input = Some value ->
  prog_b value = true.
Proof.
  intros input value accepted.
  unfold prog_get in accepted.
  destruct (prog_shape input) as [found |] eqn:shape; try discriminate.
  destruct (prog_b found) eqn:valid; try discriminate.
  inversion accepted; subst.
  exact valid.
Qed.

Definition enc_prog (value : program) : option bits :=
  if prog_b value then Some (enc prog_code value) else None.

Definition dec_prog : bits -> option program := dec prog_code prog_get.

Theorem prog_decode_encode : forall value input,
  enc_prog value = Some input ->
  dec_prog input = Some value.
Proof.
  intros value input encoded.
  unfold enc_prog in encoded.
  destruct (prog_b value) eqn:valid; try discriminate.
  inversion encoded; subst input.
  unfold dec_prog.
  apply dec_enc.
  apply prog_get_code.
  exact valid.
Qed.

Theorem prog_encode_decode : forall input value,
  dec_prog input = Some value ->
  enc_prog value = Some input.
Proof.
  intros input value decoded.
  assert (valid : prog_b value = true).
  {
    unfold dec_prog, dec in decoded.
    destruct (get_code input) as [shape |] eqn:shape_ok; try discriminate.
    destruct (prog_get shape) as [found |] eqn:value_ok; try discriminate.
    destruct (code_eqb (prog_code found) shape) eqn:exact; try discriminate.
    inversion decoded; subst.
    apply prog_get_b with (input := shape).
    exact value_ok.
  }
  pose proof (enc_dec program prog_code prog_get input value decoded) as exact.
  unfold enc_prog.
  rewrite valid, exact.
  reflexivity.
Qed.