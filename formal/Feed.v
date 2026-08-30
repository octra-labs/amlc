(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.

Require Import Uni.
Require Import Lim.
Require Import Rule.
Require Import Bin.
Require Import Ser.
Require Import Low.
Require Import Host.
Require Import Sess.

Import ListNotations.

Definition values_code (values : list value) : code :=
  list_code value_code values.

Definition values_get (input : code) : option (list value) :=
  list_get value_get input.

Lemma values_get_code : forall values,
  values_get (values_code values) = Some values.
Proof.
  intros values.
  apply list_get_code.
  intros value _.
  apply value_get_code.
Qed.

Definition caps_b (values : list value) : bool :=
  match Host.caps values with
  | Some _ => true
  | None => false
  end.

Definition feed_b (values : list value) : bool :=
  forallb Host.shape values && caps_b values.

Definition feed_bits (values : list value) : bits :=
  Ser.enc values_code values.

Definition bit_octet (value : bool) : nat := if value then 49 else 48.

Fixpoint octet_bits (input : list nat) : option bits :=
  match input with
  | [] => Some []
  | 48 :: rest =>
      match octet_bits rest with
      | Some out => Some (false :: out)
      | None => None
      end
  | 49 :: rest =>
      match octet_bits rest with
      | Some out => Some (true :: out)
      | None => None
      end
  | _ => None
  end.

Lemma octet_bits_map : forall input,
  octet_bits (map bit_octet input) = Some input.
Proof.
  induction input as [|value rest IH]; simpl.
  - reflexivity.
  - destruct value; simpl; rewrite IH; reflexivity.
Qed.

Definition feed_file (values : list value) : list nat :=
  [65; 70; 49; 10] ++ map bit_octet (feed_bits values).

Definition file_bits (input : list nat) : option bits :=
  match input with
  | 65 :: 70 :: 49 :: 10 :: rest => octet_bits rest
  | _ => None
  end.

Lemma file_bits_feed : forall values,
  file_bits (feed_file values) = Some (feed_bits values).
Proof.
  intros values.
  change
    (octet_bits (map bit_octet (feed_bits values)) = Some (feed_bits values)).
  apply octet_bits_map.
Qed.

Definition feed_fit (values : list value) : bool :=
  feed_b values && Nat.leb (length (feed_file values)) (rstr local).

Definition enc_feed (values : list value) : option (list nat) :=
  if feed_fit values then Some (feed_file values) else None.

Definition dec_feed (input : list nat) : option (list value) :=
  if Nat.leb (length input) (rstr local) then
    match file_bits input with
    | Some body =>
        match Ser.dec values_code values_get body with
        | Some values =>
            if feed_b values && Sess.bytes_eqb (feed_file values) input
            then Some values else None
        | None => None
        end
    | None => None
    end
  else None.

Theorem feed_decode_encode : forall values,
  feed_fit values = true ->
  dec_feed (feed_file values) = Some values.
Proof.
  intros values valid.
  unfold feed_fit in valid.
  apply andb_true_iff in valid.
  destruct valid as [shape size].
  unfold dec_feed.
  rewrite size, file_bits_feed.
  unfold feed_bits.
  rewrite Ser.dec_enc.
  - rewrite shape, Sess.bytes_eqb_refl.
    reflexivity.
  - apply values_get_code.
Qed.

Theorem feed_encode_decode : forall input values,
  dec_feed input = Some values -> enc_feed values = Some input.
Proof.
  intros input values accepted.
  unfold dec_feed in accepted.
  destruct (Nat.leb (length input) (rstr local)) eqn:size; try discriminate.
  destruct (file_bits input) as [body |] eqn:framed; try discriminate.
  destruct (Ser.dec values_code values_get body) as [found |] eqn:decoded;
    try discriminate.
  destruct (feed_b found && Sess.bytes_eqb (feed_file found) input)
    eqn:valid; try discriminate.
  inversion accepted; subst found.
  apply andb_true_iff in valid.
  destruct valid as [shape exact].
  apply Sess.bytes_eqb_eq in exact.
  unfold enc_feed, feed_fit.
  rewrite shape, exact, size.
  reflexivity.
Qed.

Definition load (binds : list bind) (values : list value) : option env :=
  if feed_b values then Host.load [] binds values else None.

Theorem load_ok : forall binds values gamma sigma,
  opens [] binds = Some gamma ->
  load binds values = Some sigma ->
  env_ok gamma sigma.
Proof.
  intros binds values gamma sigma opened loaded.
  unfold load in loaded.
  destruct (feed_b values) eqn:valid; try discriminate.
  apply Host.load_ok with (binds := binds) (values := values)
    (gamma := []) (sigma := []).
  - exact opened.
  - exact loaded.
  - constructor.
Qed.

Definition sub := list (nat * tm).

Fixpoint collect {A B : Type} (f : A -> option B) (values : list A)
    : option (list B) :=
  match values with
  | [] => Some []
  | value :: rest =>
      match f value, collect f rest with
      | Some out, Some more => Some (out :: more)
      | _, _ => None
      end
  end.

Fixpoint term_of (typ : ty) (item : value) {struct typ} : option tm :=
  if Host.typed typ item then
    match typ, item with
    | TUnit, VUnit => Some (K VUnit TUnit)
    | TBool, VBool flag => Some (K (VBool flag) TBool)
    | TInt, VInt number => Some (K (VInt number) TInt)
    | TBytes _, VBytes raw => Some (Bytes raw)
    | TVec _ elem, VVec values =>
        match collect (term_of elem) values with
        | Some terms => Some (vlist elem terms)
        | None => None
        end
    | TPair left_ty right_ty, VPair left_value right_value =>
        match term_of left_ty left_value, term_of right_ty right_value with
        | Some left_term, Some right_term => Some (Pair left_term right_term)
        | _, _ => None
        end
    | TSum left_ty right_ty, VInl left_value =>
        match term_of left_ty left_value with
        | Some left_term => Some (Inl left_term right_ty)
        | None => None
        end
    | TSum left_ty right_ty, VInr right_value =>
        match term_of right_ty right_value with
        | Some right_term => Some (Inr left_ty right_term)
        | None => None
        end
    | _, _ => None
    end
  else None.

Theorem term_of_typed : forall typ item term,
  term_of typ item = Some term -> Host.typed typ item = true.
Proof.
  intros typ item term accepted.
  destruct typ; destruct item; cbn [term_of] in accepted |- *;
    try discriminate; try reflexivity;
    match type of accepted with
    | context [if ?test then _ else _] =>
        destruct test; try discriminate; reflexivity
    end.
Qed.

Corollary term_of_value : forall typ item term,
  term_of typ item = Some term -> hasv item typ.
Proof.
  intros typ item term accepted.
  apply Host.typed_sound.
  eapply term_of_typed.
  exact accepted.
Qed.

Theorem term_of_check : forall typ item term,
  term_of typ item = Some term ->
  forall gamma, exists cost, check gamma term typ [] cost gamma.
Proof.
  induction typ as [| | |len|len elem repeat|kind|key rem
    |left_ty left_ih right_ty right_ih
    |left_ty left_ih right_ty right_ih];
    intros item term accepted gamma;
    destruct item as [|flag|number|bytes|vector_values|cap_kind cap_id
      |enc_key enc_rem cipher|pair_left pair_right|sum_left|sum_right];
    cbn [term_of] in accepted; try discriminate.
  - inversion accepted; subst.
    exists rone.
    apply CK; constructor.
  - inversion accepted; subst.
    exists rone.
    apply CK; constructor.
  - inversion accepted; subst.
    exists rone.
    apply CK; constructor.
  - destruct (Host.typed (TBytes len) (VBytes bytes)) eqn:valid;
      try discriminate.
    inversion accepted; subst.
    pose proof (Host.typed_sound (TBytes len) (VBytes bytes) valid) as value_ok.
    inversion value_ok; subst.
    exists (rsucc (rscan (length bytes))).
    apply CBytes.
    assumption.
  - destruct (Host.typed (TVec len elem) (VVec vector_values)) eqn:valid;
      try discriminate.
    destruct (collect (term_of elem) vector_values) as [terms |] eqn:converted;
      try discriminate.
    inversion accepted; subst.
    pose proof
      (Host.typed_sound (TVec len elem) (VVec vector_values) valid)
      as value_ok.
    inversion value_ok; subst.
    assert (checked : forall values outs,
      collect (term_of elem) values = Some outs ->
      forall sigma, exists cost,
        check sigma (vlist elem outs) (TVec (length values) elem) [] cost sigma).
    {
      induction values as [|value values again];
        intros outs gathered sigma.
      - cbn [collect] in gathered.
        inversion gathered; subst.
        exists rone.
        apply CVnil.
      - cbn [collect] in gathered.
        destruct (term_of elem value) as [first |] eqn:first_ok;
          try discriminate.
        destruct (collect (term_of elem) values) as [rest |] eqn:rest_ok;
          try discriminate.
        inversion gathered; subst.
        destruct (repeat value first first_ok sigma) as [first_cost first_check].
        destruct (again rest eq_refl sigma) as [rest_cost rest_check].
        exists (rsucc (radd first_cost rest_cost)).
        cbn [vlist length].
        eapply CVcons with (mid := sigma) (rowf := []) (rowr := [])
          (costf := first_cost) (costr := rest_cost).
        + exact first_check.
        + exact rest_check.
    }
    apply checked with (values := vector_values).
    exact converted.
  - destruct (Host.typed _ _); discriminate.
  - destruct (Host.typed _ _); discriminate.
  - destruct (Host.typed (TPair left_ty right_ty) (VPair pair_left pair_right))
      eqn:valid; try discriminate.
    destruct (term_of left_ty pair_left) as [left_term |] eqn:left_ok;
      try discriminate.
    destruct (term_of right_ty pair_right) as [right_term |] eqn:right_ok;
      try discriminate.
    inversion accepted; subst.
    destruct (left_ih pair_left left_term left_ok gamma)
      as [left_cost left_check].
    destruct (right_ih pair_right right_term right_ok gamma)
      as [right_cost right_check].
    exists (rsucc (radd left_cost right_cost)).
    eapply CPair with (mid := gamma) (rowl := []) (rowr := [])
      (costl := left_cost) (costr := right_cost).
    + exact left_check.
    + exact right_check.
  - destruct (Host.typed (TSum left_ty right_ty) (VInl sum_left)) eqn:valid;
      try discriminate.
    destruct (term_of left_ty sum_left) as [left_term |] eqn:left_ok;
      try discriminate.
    inversion accepted; subst.
    destruct (left_ih sum_left left_term left_ok gamma)
      as [left_cost left_check].
    exists (rsucc left_cost).
    apply CInl.
    exact left_check.
  - destruct (Host.typed (TSum left_ty right_ty) (VInr sum_right)) eqn:valid;
      try discriminate.
    destruct (term_of right_ty sum_right) as [right_term |] eqn:right_ok;
      try discriminate.
    inversion accepted; subst.
    destruct (right_ih sum_right right_term right_ok gamma)
      as [right_cost right_check].
    exists (rsucc right_cost).
    apply CInr.
    exact right_check.
Qed.

Theorem term_of_eval : forall typ item term,
  term_of typ item = Some term ->
  forall sigma, exists out,
    evalR sigma term out sigma /\ rv out = item /\ rp out = [].
Proof.
  induction typ as [| | |len|len elem repeat|kind|key rem
    |left_ty left_ih right_ty right_ih
    |left_ty left_ih right_ty right_ih];
    intros item term accepted sigma;
    destruct item as [|flag|number|bytes|vector_values|cap_kind cap_id
      |enc_key enc_rem cipher|pair_left pair_right|sum_left|sum_right];
    cbn [term_of] in accepted; try discriminate.
  - inversion accepted; subst.
    exists (one VUnit).
    repeat split; try apply EK; reflexivity.
  - inversion accepted; subst.
    exists (one (VBool flag)).
    repeat split; try apply EK; reflexivity.
  - inversion accepted; subst.
    exists (one (VInt number)).
    repeat split; try apply EK; reflexivity.
  - destruct (Host.typed (TBytes len) (VBytes bytes)); try discriminate.
    inversion accepted; subst.
    exists (Run (VBytes bytes) [] (S (length bytes)) (S (length bytes))).
    repeat split; try apply EBytes; reflexivity.
  - destruct (Host.typed (TVec len elem) (VVec vector_values));
      try discriminate.
    destruct (collect (term_of elem) vector_values) as [terms |]
      eqn:converted;
      try discriminate.
    inversion accepted; subst.
    assert (ran : forall values outs,
      collect (term_of elem) values = Some outs ->
      forall state, exists out,
        evalR state (vlist elem outs) out state /\
        rv out = VVec values /\ rp out = []).
    {
      induction values as [|value values again];
        intros outs gathered state.
      - cbn [collect] in gathered.
        inversion gathered; subst.
        exists (one (VVec [])).
        repeat split; try apply EVnil; reflexivity.
      - cbn [collect] in gathered.
        destruct (term_of elem value) as [first |] eqn:first_ok;
          try discriminate.
        destruct (collect (term_of elem) values) as [rest |] eqn:rest_ok;
          try discriminate.
        inversion gathered; subst.
        destruct (repeat value first first_ok state)
          as [first_out [first_run [first_value first_plan]]].
        destruct (again rest eq_refl state)
          as [rest_out [rest_run [rest_value rest_plan]]].
        exists (seq first_out rest_out (VVec (rv first_out :: values))).
        split.
        + cbn [vlist].
          eapply EVcons with (mid := state) (values := values).
          * exact first_run.
          * exact rest_run.
          * exact rest_value.
        + split.
          * cbn [seq].
            rewrite first_value.
            reflexivity.
          * change (rp first_out ++ rp rest_out = []).
            rewrite first_plan, rest_plan.
            reflexivity.
    }
    apply ran with (values := vector_values).
    exact converted.
  - destruct (Host.typed _ _); discriminate.
  - destruct (Host.typed _ _); discriminate.
  - destruct (Host.typed (TPair left_ty right_ty) (VPair pair_left pair_right));
      try discriminate.
    destruct (term_of left_ty pair_left) as [left_term |] eqn:left_ok;
      try discriminate.
    destruct (term_of right_ty pair_right) as [right_term |] eqn:right_ok;
      try discriminate.
    inversion accepted; subst.
    destruct (left_ih pair_left left_term left_ok sigma)
      as [left_out [left_run [left_value left_plan]]].
    destruct (right_ih pair_right right_term right_ok sigma)
      as [right_out [right_run [right_value right_plan]]].
    exists (seq left_out right_out (VPair (rv left_out) (rv right_out))).
    split.
    + eapply EPair with (mid := sigma).
      * exact left_run.
      * exact right_run.
    + split.
      * cbn [seq].
        rewrite left_value, right_value.
        reflexivity.
      * change (rp left_out ++ rp right_out = []).
        rewrite left_plan, right_plan.
        reflexivity.
  - destruct (Host.typed (TSum left_ty right_ty) (VInl sum_left));
      try discriminate.
    destruct (term_of left_ty sum_left) as [left_term |] eqn:left_ok;
      try discriminate.
    inversion accepted; subst.
    destruct (left_ih sum_left left_term left_ok sigma)
      as [left_out [left_run [left_value left_plan]]].
    exists
      (Run (VInl (rv left_out)) (rp left_out)
        (S (rs left_out)) (S (rw left_out))).
    split.
    + apply EInl.
      exact left_run.
    + split.
      * cbn.
        rewrite left_value.
        reflexivity.
      * cbn.
        exact left_plan.
  - destruct (Host.typed (TSum left_ty right_ty) (VInr sum_right));
      try discriminate.
    destruct (term_of right_ty sum_right) as [right_term |] eqn:right_ok;
      try discriminate.
    inversion accepted; subst.
    destruct (right_ih sum_right right_term right_ok sigma)
      as [right_out [right_run [right_value right_plan]]].
    exists
      (Run (VInr (rv right_out)) (rp right_out)
        (S (rs right_out)) (S (rw right_out))).
    split.
    + apply EInr.
      exact right_run.
    + split.
      * cbn.
        rewrite right_value.
        reflexivity.
      * cbn.
        exact right_plan.
Qed.

Fixpoint sub_get (id : nat) (values : sub) : option tm :=
  match values with
  | [] => None
  | (key, value) :: rest =>
      if Nat.eqb id key then Some value else sub_get id rest
  end.

Fixpoint sub_drop (id : nat) (values : sub) : sub :=
  match values with
  | [] => []
  | (key, value) :: rest =>
      if Nat.eqb id key then sub_drop id rest
      else (key, value) :: sub_drop id rest
  end.

Fixpoint subst (values : sub) (term : tm) : tm :=
  match term with
  | K value typ => K value typ
  | Bytes raw => Bytes raw
  | Vnil elem => Vnil elem
  | Var id =>
      match sub_get id values with
      | Some value => value
      | None => Var id
      end
  | Let binder value body =>
      Let binder (subst values value) (subst (sub_drop (bid binder) values) body)
  | If guard yes no =>
      If (subst values guard) (subst values yes) (subst values no)
  | Pair lhs rhs => Pair (subst values lhs) (subst values rhs)
  | Unpair tuple lhs rhs body =>
      Unpair (subst values tuple) lhs rhs
        (subst (sub_drop (bid rhs) (sub_drop (bid lhs) values)) body)
  | Fst value => Fst (subst values value)
  | Snd value => Snd (subst values value)
  | Inl value rhs => Inl (subst values value) rhs
  | Inr lhs value => Inr lhs (subst values value)
  | Case value lhs yes rhs no =>
      Case (subst values value) lhs
        (subst (sub_drop (bid lhs) values) yes) rhs
        (subst (sub_drop (bid rhs) values) no)
  | Act action body => Act action (subst values body)
  | Add lhs rhs => Add (subst values lhs) (subst values rhs)
  | Sub lhs rhs => Sub (subst values lhs) (subst values rhs)
  | Mul lhs rhs => Mul (subst values lhs) (subst values rhs)
  | Div lhs rhs => Div (subst values lhs) (subst values rhs)
  | Mod lhs rhs => Mod (subst values lhs) (subst values rhs)
  | Neg value => Neg (subst values value)
  | Abs value => Abs (subst values value)
  | Eq typ lhs rhs => Eq typ (subst values lhs) (subst values rhs)
  | Cat lhs rhs => Cat (subst values lhs) (subst values rhs)
  | Take len value => Take len (subst values value)
  | Drop len value => Drop len (subst values value)
  | Vcons first rest => Vcons (subst values first) (subst values rest)
  | Vcat lhs rhs => Vcat (subst values lhs) (subst values rhs)
  | At index value => At index (subst values value)
  | Uncons value => Uncons (subst values value)
  | Fold len vector seed item state body =>
      Fold len (subst values vector) (subst values seed) item state
        (subst (sub_drop (bid state) (sub_drop (bid item) values)) body)
  | Step cap value => Step (subst values cap) (subst values value)
  | Close cap => Close (subst values cap)
  end.

Fixpoint sub_of (binds : list bind) (values : list value) : option sub :=
  match binds, values with
  | [], [] => Some []
  | binder :: rest, item :: more =>
      match sub_of rest more with
      | Some out =>
          match bmul binder with
          | M0 =>
              if Host.typed (bty binder) item then Some out else None
          | M1 | MM =>
              match term_of (bty binder) item with
              | Some term => Some ((bid binder, term) :: out)
              | None => None
              end
          end
      | None => None
      end
  | _, _ => None
  end.

Definition close (binds : list bind) (values : list value) (term : tm)
    : option tm :=
  match sub_of binds values with
  | Some input => Some (subst input term)
  | None => None
  end.

Theorem close_unique : forall binds values term left right,
  close binds values term = Some left ->
  close binds values term = Some right ->
  left = right.
Proof.
  intros binds values term left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.