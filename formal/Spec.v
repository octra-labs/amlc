(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Uni.
Require Import Lim.
Require Import Surf.
Require Import Idx.
Require Import Law.
Require Import Raw.
Require Import Norm.
Require Import Low.
Require Import Fun.

Import ListNotations.

Record ibind : Type := IBind {
  ibname : nat;
  ibmul : mul;
  ibtype : ity
}.

Record iarr : Type := IArr {
  imul : mul;
  icaps : list ibind;
  iarg : ibind;
  iout : ity;
  ieff : list atom;
  ilim : option res
}.

Record ifn : Type := IFn {
  iname : nat;
  ipars : list nat;
  ilaws : list law;
  iarr0 : iarr;
  ibody : rtm
}.

Fixpoint nhas (name : nat) (names : list nat) : bool :=
  match names with
  | [] => false
  | item :: rest => Nat.eqb name item || nhas name rest
  end.

Fixpoint names_b (seen names : list nat) : bool :=
  match names with
  | [] => true
  | name :: rest => negb (nhas name seen) && names_b (name :: seen) rest
  end.

Definition ifn_b (item : ifn) : bool :=
  let spec := iarr0 item in
  let names := ipars item ++ map ibname (icaps spec) ++ [ibname (iarg spec)] in
  Nat.leb (length (ipars item)) pmax && names_b [] names
    && laws_b (ilaws item).

Fixpoint ivals (env : ienv) (terms : list ix) : option (list nat) :=
  match terms with
  | [] => Some []
  | term :: rest =>
      match ieval env term, ivals env rest with
      | Some value, Some values => Some (value :: values)
      | _, _ => None
      end
  end.

Fixpoint izip (env : ienv) (names values : list nat) : option ienv :=
  match names, values with
  | [], [] => Some env
  | name :: names, value :: values =>
      match iput env name (ILit value) with
      | Some next => izip next names values
      | None => None
      end
  | _, _ => None
  end.

Definition ibind_elab (env : ienv) (item : ibind) : option sbind :=
  match yelab env (ibtype item) with
  | Some typ => Some (SBind (ibname item) (ibmul item) typ)
  | None => None
  end.

Fixpoint ibinds_elab (env : ienv) (items : list ibind)
    : option (list sbind) :=
  match items with
  | [] => Some []
  | item :: rest =>
      match ibind_elab env item, ibinds_elab env rest with
      | Some bind, Some binds => Some (bind :: binds)
      | _, _ => None
      end
  end.

Definition iarr_elab (env : ienv) (item : iarr) : option arr :=
  match ibinds_elab env (icaps item), ibind_elab env (iarg item),
      yelab env (iout item) with
  | Some caps, Some arg, Some out =>
      Some (Arr (imul item) caps arg out (ieff item) (ilim item))
  | _, _, _ => None
  end.

Definition fspec (base : ienv) (name : nat) (item : ifn)
    (actuals : list ix) : option fn :=
  if ifn_b item && Nat.eqb (length actuals) (length (ipars item)) then
    match ivals base actuals with
    | Some values =>
        match izip base (ipars item) values with
        | Some env =>
            match lholds env (ilaws item) with
            | Some tt =>
                match iarr_elab env (iarr0 item) with
                | Some spec =>
                    match nelab env (acaps spec ++ [aarg spec]) (ibody item) with
                    | Some body => Some (Fn name spec body)
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
  else None.

Definition fspec_check (base : ienv) (name : nat) (item : ifn)
    (actuals : list ix) : option fn :=
  match fspec base name item actuals with
  | Some out => if fcheckb out then Some out else None
  | None => None
  end.

Lemma ivals_length : forall env terms values,
  ivals env terms = Some values -> length terms = length values.
Proof.
  intros env terms.
  induction terms as [|term rest IH]; intros values accepted; simpl in accepted.
  - inversion accepted. reflexivity.
  - destruct (ieval env term); try discriminate.
    destruct (ivals env rest) as [tail |] eqn:run; try discriminate.
    inversion accepted; subst.
    simpl. f_equal. apply IH. reflexivity.
Qed.

Lemma izip_length : forall env names values out,
  izip env names values = Some out -> length names = length values.
Proof.
  intros env names.
  revert env.
  induction names as [|name names IH]; intros env values out accepted;
    destruct values as [|value values]; simpl in accepted; try discriminate;
    try reflexivity.
  destruct (iput env name (ILit value)) as [next |] eqn:put; try discriminate.
  simpl. f_equal. eapply IH. exact accepted.
Qed.

Theorem fspec_arity : forall base name item actuals out,
  fspec base name item actuals = Some out ->
  length actuals = length (ipars item).
Proof.
  intros base name item actuals out accepted.
  unfold fspec in accepted.
  destruct (ifn_b item && Nat.eqb (length actuals) (length (ipars item)))
    eqn:head; try discriminate.
  apply andb_true_iff in head as [_ arity].
  apply Nat.eqb_eq. exact arity.
Qed.

Theorem fspec_erased : forall base name item actuals out,
  fspec base name item actuals = Some out ->
  exists values env caps arg typ body,
    ivals base actuals = Some values /\
    izip base (ipars item) values = Some env /\
    lholds env (ilaws item) = Some tt /\
    ibinds_elab env (icaps (iarr0 item)) = Some caps /\
    ibind_elab env (iarg (iarr0 item)) = Some arg /\
    yelab env (iout (iarr0 item)) = Some typ /\
    nelab env (caps ++ [arg]) (ibody item) = Some body /\
    out = Fn name
      (Arr (imul (iarr0 item)) caps arg typ
        (ieff (iarr0 item)) (ilim (iarr0 item)))
      body.
Proof.
  intros base name item actuals out accepted.
  unfold fspec in accepted.
  destruct (ifn_b item && Nat.eqb (length actuals) (length (ipars item)));
    try discriminate.
  destruct (ivals base actuals) as [values |] eqn:run; try discriminate.
  destruct (izip base (ipars item) values) as [env |] eqn:limit;
    try discriminate.
  destruct (lholds env (ilaws item)) as [[] |] eqn:laws_ok;
    try discriminate.
  unfold iarr_elab in accepted.
  destruct (ibinds_elab env (icaps (iarr0 item))) as [caps |] eqn:caps_ok;
    try discriminate.
  destruct (ibind_elab env (iarg (iarr0 item))) as [arg |] eqn:arg_ok;
    try discriminate.
  destruct (yelab env (iout (iarr0 item))) as [typ |] eqn:out_ok;
    try discriminate.
  cbn in accepted.
  destruct (nelab env (caps ++ [arg]) (ibody item)) as [body |] eqn:body_ok;
    try discriminate.
  inversion accepted; subst.
  exists values, env, caps, arg, typ, body.
  repeat split; try assumption; try reflexivity.
Qed.

Theorem fspec_laws : forall base name item actuals out,
  fspec base name item actuals = Some out ->
  exists values env,
    ivals base actuals = Some values /\
    izip base (ipars item) values = Some env /\
    lawsR env (ilaws item).
Proof.
  intros base name item actuals out accepted.
  apply fspec_erased in accepted as
    [values [env [caps [arg [typ [body [ran [limit [held _]]]]]]]]].
  exists values, env. repeat split; try assumption.
  eapply lholds_sound. exact held.
Qed.

Theorem fspec_check_part : forall base name item actuals out,
  fspec_check base name item actuals = Some out ->
  fspec base name item actuals = Some out /\ fcheckb out = true.
Proof.
  intros base name item actuals out accepted.
  unfold fspec_check in accepted.
  destruct (fspec base name item actuals) as [value |] eqn:made;
    try discriminate.
  destruct (fcheckb value) eqn:checked; try discriminate.
  inversion accepted; subst. auto.
Qed.

Theorem fspec_check_marks : forall base name item actuals out typ row cost next,
  fspec_check base name item actuals = Some out ->
  pcheck (acaps (farr out) ++ [aarg (farr out)]) (fbody out) =
    Some (typ, row, cost, next) ->
  forallb atom_b (aeff (farr out)) = true /\ within row (aeff (farr out)).
Proof.
  intros base name item actuals out typ row cost next accepted checked.
  apply fspec_check_part in accepted as [_ valid].
  eapply fcheck_marks; eauto.
Qed.

Theorem fspec_check_under : forall base name item actuals out
    typ row cost next limit,
  fspec_check base name item actuals = Some out ->
  pcheck (acaps (farr out) ++ [aarg (farr out)]) (fbody out) =
    Some (typ, row, cost, next) ->
  alim (farr out) = Some limit ->
  res_b limit = true /\ rle cost limit.
Proof.
  intros base name item actuals out typ row cost next limit
    accepted checked declared.
  apply fspec_check_part in accepted as [_ valid].
  eapply fcheck_under; eauto.
Qed.

Theorem fspec_many : forall base name item actuals out,
  fspec_check base name item actuals = Some out ->
  amul (farr out) = MM ->
  Forall (fun cap => smul cap = MM) (acaps (farr out)).
Proof.
  intros base name item actuals out accepted mode.
  apply fspec_check_part in accepted as [_ valid].
  eapply repeated_captures; eauto.
Qed.

Theorem fspec_linear : forall base name item actuals out cap,
  fspec_check base name item actuals = Some out ->
  In cap (acaps (farr out)) ->
  smul cap = M1 ->
  amul (farr out) = M1.
Proof.
  intros base name item actuals out cap accepted found linear.
  apply fspec_check_part in accepted as [_ valid].
  eapply linear_capture; eauto.
Qed.