(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.

Require Import Uni.
Require Import Lim.
Require Import Surf.
Require Import Low.
Require Import Fun.
Require Import Idx.
Require Import Raw.
Require Import Rnom.
Require Import Data.
Require Import Law.
Require Import Spec.

Import ListNotations.

Inductive pkind : Type := PData | PRes.

Record ppar : Type := PPar {
  ppname : nat;
  ppkind : pkind
}.

Record pfn : Type := PFn {
  ppars : list ppar;
  pbase : ifn
}.

Definition penv := list (nat * ity).

Fixpoint phas (name : nat) (env : penv) : bool :=
  match env with
  | [] => false
  | (key, _) :: rest => Nat.eqb name key || phas name rest
  end.

Fixpoint pfind (name : nat) (env : penv) : option ity :=
  match env with
  | [] => None
  | (key, value) :: rest =>
      if Nat.eqb name key then Some value else pfind name rest
  end.

Definition pkind_b (kind : pkind) (typ : ty) : bool :=
  match kind with
  | PData => data_b typ
  | PRes => negb (data_b typ)
  end.

Definition pnorm (base : ienv) (kind : pkind) (raw : ity) : option ity :=
  match yelab base raw with
  | Some typ => if pkind_b kind typ then ylift typ else None
  | None => None
  end.

Inductive pvalsR (base : ienv) : list ppar -> list ity -> list ity -> Prop :=
| PRNil : pvalsR base [] [] []
| PRCons : forall par pars raw actuals typ out vals,
    yelab base raw = Some typ ->
    pkind_b (ppkind par) typ = true ->
    ylift typ = Some out ->
    pvalsR base pars actuals vals ->
    pvalsR base (par :: pars) (raw :: actuals) (out :: vals).

Fixpoint pvals (base : ienv) (pars : list ppar) (actuals : list ity)
    : option (list ity) :=
  match pars, actuals with
  | [], [] => Some []
  | par :: rest, raw :: tail =>
      match pnorm base (ppkind par) raw, pvals base rest tail with
      | Some typ, Some types => Some (typ :: types)
      | _, _ => None
      end
  | _, _ => None
  end.

Fixpoint ptys (values : list ity) : option (list ty) :=
  match values with
  | [] => Some []
  | value :: rest =>
      match yelab [] value, ptys rest with
      | Some typ, Some types => Some (typ :: types)
      | _, _ => None
      end
  end.

Fixpoint pzip (pars : list ppar) (types : list ity) : option penv :=
  match pars, types with
  | [], [] => Some []
  | par :: rest, typ :: tail =>
      match pzip rest tail with
      | Some env => Some ((ppname par, typ) :: env)
      | None => None
      end
  | _, _ => None
  end.

Fixpoint ysub (env : penv) (typ : ity) : option ity :=
  match typ with
  | YUnit => Some YUnit
  | YBool => Some YBool
  | YInt => Some YInt
  | YVar name => pfind name env
  | YBytes index => Some (YBytes index)
  | YVec index elem =>
      match ysub env elem with
      | Some out => Some (YVec index out)
      | None => None
      end
  | YCap kind => Some (YCap kind)
  | YPair lhs rhs =>
      match ysub env lhs, ysub env rhs with
      | Some lout, Some rout => Some (YPair lout rout)
      | _, _ => None
      end
  | YSum lhs rhs =>
      match ysub env lhs, ysub env rhs with
      | Some lout, Some rout => Some (YSum lout rout)
      | _, _ => None
      end
  end.

Definition rbsub (env : penv) (item : rbind) : option rbind :=
  match ysub env (rbtype item) with
  | Some typ => Some (RBind (rbname item) (rbmul item) typ)
  | None => None
  end.

Fixpoint rsub (env : penv) (term : rtm) : option rtm :=
  match term with
  | RUnit => Some RUnit
  | RBool value => Some (RBool value)
  | RInt value => Some (RInt value)
  | RBytes value => Some (RBytes value)
  | RVnil typ =>
      match ysub env typ with
      | Some out => Some (RVnil out)
      | None => None
      end
  | RVcons value rest =>
      match rsub env value, rsub env rest with
      | Some out, Some tail => Some (RVcons out tail)
      | _, _ => None
      end
  | RVar name => Some (RVar name)
  | RLet item value body =>
      match rbsub env item, rsub env value, rsub env body with
      | Some bind, Some out, Some rest => Some (RLet bind out rest)
      | _, _, _ => None
      end
  | RIf guard yes no =>
      match rsub env guard, rsub env yes, rsub env no with
      | Some g, Some y, Some n => Some (RIf g y n)
      | _, _, _ => None
      end
  | RPair lhs rhs =>
      match rsub env lhs, rsub env rhs with
      | Some lout, Some rout => Some (RPair lout rout)
      | _, _ => None
      end
  | RUnpair value lhs rhs body =>
      match rsub env value, rbsub env lhs, rbsub env rhs, rsub env body with
      | Some out, Some lout, Some rout, Some rest =>
          Some (RUnpair out lout rout rest)
      | _, _, _, _ => None
      end
  | RFst value =>
      match rsub env value with Some out => Some (RFst out) | None => None end
  | RSnd value =>
      match rsub env value with Some out => Some (RSnd out) | None => None end
  | RInl value typ =>
      match rsub env value, ysub env typ with
      | Some out, Some rout => Some (RInl out rout)
      | _, _ => None
      end
  | RInr typ value =>
      match ysub env typ, rsub env value with
      | Some lout, Some out => Some (RInr lout out)
      | _, _ => None
      end
  | RCase value lhs yes rhs no =>
      match rsub env value, rbsub env lhs, rsub env yes,
          rbsub env rhs, rsub env no with
      | Some out, Some lout, Some y, Some rout, Some n =>
          Some (RCase out lout y rout n)
      | _, _, _, _, _ => None
      end
  | RAct atom body =>
      match rsub env body with
      | Some out => Some (RAct atom out)
      | None => None
      end
  | RAdd lhs rhs =>
      match rsub env lhs, rsub env rhs with
      | Some lout, Some rout => Some (RAdd lout rout)
      | _, _ => None
      end
  | RSub lhs rhs =>
      match rsub env lhs, rsub env rhs with
      | Some lout, Some rout => Some (RSub lout rout)
      | _, _ => None
      end
  | RMul lhs rhs =>
      match rsub env lhs, rsub env rhs with
      | Some lout, Some rout => Some (RMul lout rout)
      | _, _ => None
      end
  | RDiv lhs rhs =>
      match rsub env lhs, rsub env rhs with
      | Some lout, Some rout => Some (RDiv lout rout)
      | _, _ => None
      end
  | RMod lhs rhs =>
      match rsub env lhs, rsub env rhs with
      | Some lout, Some rout => Some (RMod lout rout)
      | _, _ => None
      end
  | RNeg value =>
      match rsub env value with
      | Some out => Some (RNeg out)
      | None => None
      end
  | RAbs value =>
      match rsub env value with
      | Some out => Some (RAbs out)
      | None => None
      end
  | REq typ lhs rhs =>
      match ysub env typ, rsub env lhs, rsub env rhs with
      | Some out, Some lout, Some rout => Some (REq out lout rout)
      | _, _, _ => None
      end
  | RCat lhs rhs =>
      match rsub env lhs, rsub env rhs with
      | Some lout, Some rout => Some (RCat lout rout)
      | _, _ => None
      end
  | RTake pos value =>
      match rsub env value with
      | Some out => Some (RTake pos out)
      | None => None
      end
  | RDrop pos value =>
      match rsub env value with
      | Some out => Some (RDrop pos out)
      | None => None
      end
  | RVcat lhs rhs =>
      match rsub env lhs, rsub env rhs with
      | Some lout, Some rout => Some (RVcat lout rout)
      | _, _ => None
      end
  | RAt pos value =>
      match rsub env value with
      | Some out => Some (RAt pos out)
      | None => None
      end
  | RUncons value =>
      match rsub env value with
      | Some out => Some (RUncons out)
      | None => None
      end
  | RFold count vector seed item state body =>
      match rsub env vector, rsub env seed, rbsub env item,
          rbsub env state, rsub env body with
      | Some values, Some init, Some elem, Some carry, Some out =>
          Some (RFold count values init elem carry out)
      | _, _, _, _, _ => None
      end
  | RFoldI vector seed item state body =>
      match rsub env vector, rsub env seed, rbsub env item,
          rbsub env state, rsub env body with
      | Some values, Some init, Some elem, Some carry, Some out =>
          Some (RFoldI values init elem carry out)
      | _, _, _, _, _ => None
      end
  | RQuant mode source item body =>
      match rsub env source, rbsub env item, rsub env body with
      | Some value, Some bind, Some out => Some (RQuant mode value bind out)
      | _, _, _ => None
      end
  | RStep cap value =>
      match rsub env cap, rsub env value with
      | Some lout, Some rout => Some (RStep lout rout)
      | _, _ => None
      end
  | RClose value =>
      match rsub env value with
      | Some out => Some (RClose out)
      | None => None
      end
  | RWeave count typ source item body =>
      match ysub env typ, rsub env source, rbsub env item, rsub env body with
      | Some out, Some value, Some bind, Some term =>
          Some (RWeave count out value bind term)
      | _, _, _, _ => None
      end
  | RBraid count typ lhs rhs first second body =>
      match ysub env typ, rsub env lhs, rsub env rhs, rbsub env first,
          rbsub env second, rsub env body with
      | Some out, Some lout, Some rout, Some one, Some two, Some term =>
          Some (RBraid count out lout rout one two term)
      | _, _, _, _, _, _ => None
      end
  | RLoom count typ item body =>
      match ysub env typ, rbsub env item, rsub env body with
      | Some out, Some bind, Some term => Some (RLoom count out bind term)
      | _, _, _ => None
      end
  | ROrbit count seed item body =>
      match rsub env seed, rbsub env item, rsub env body with
      | Some value, Some bind, Some term => Some (ROrbit count value bind term)
      | _, _, _ => None
      end
  | RWake count seed item body =>
      match rsub env seed, rbsub env item, rsub env body with
      | Some value, Some bind, Some term => Some (RWake count value bind term)
      | _, _, _ => None
      end
  | RRift cut rest elem source =>
      match ysub env elem, rsub env source with
      | Some out, Some value => Some (RRift cut rest out value)
      | _, _ => None
      end
  | RExact raw typ body =>
      match rbsub env raw, rsub env body with
      | Some item, Some out => Some (RExact item typ out)
      | _, _ => None
      end
  | RReject => Some RReject
  end.

Definition ibsub (env : penv) (item : ibind) : option ibind :=
  match ysub env (ibtype item) with
  | Some typ => Some (IBind (ibname item) (ibmul item) typ)
  | None => None
  end.

Fixpoint ibssub (env : penv) (items : list ibind) : option (list ibind) :=
  match items with
  | [] => Some []
  | item :: rest =>
      match ibsub env item, ibssub env rest with
      | Some bind, Some binds => Some (bind :: binds)
      | _, _ => None
      end
  end.

Definition iasub (env : penv) (item : iarr) : option iarr :=
  match ibssub env (icaps item), ibsub env (iarg item),
      ysub env (iout item) with
  | Some caps, Some arg, Some out =>
      Some (IArr (imul item) caps arg out (ieff item) (ilim item))
  | _, _, _ => None
  end.

Definition ifsub (env : penv) (item : ifn) : option ifn :=
  match iasub env (iarr0 item), rsub env (ibody item) with
  | Some spec, Some body =>
      Some (IFn (iname item) (ipars item) (ilaws item) spec body)
  | _, _ => None
  end.

Definition pnames (item : pfn) : list nat :=
  map ppname (ppars item).

Definition pfn_b (item : pfn) : bool :=
  let base := pbase item in
  let spec := iarr0 base in
  let names := pnames item ++ ipars base ++
    map ibname (icaps spec) ++ [ibname (iarg spec)] in
  Nat.leb (length (ppars item)) pmax && names_b [] names && ifn_b base.

Definition pspec (base : ienv) (name : nat) (item : pfn)
    (types : list ity) (sizes : list ix) : option fn :=
  if pfn_b item && Nat.eqb (length types) (length (ppars item)) then
    match pvals base (ppars item) types with
    | Some vals =>
        match pzip (ppars item) vals with
        | Some env =>
            match ifsub env (pbase item) with
            | Some mono => fspec_check base name mono sizes
            | None => None
            end
        | None => None
        end
    | None => None
    end
  else None.

Lemma pvals_length : forall base pars actuals vals,
  pvals base pars actuals = Some vals ->
  length pars = length actuals /\ length actuals = length vals.
Proof.
  intros base pars.
  induction pars as [|par rest IH]; intros actuals vals accepted;
    destruct actuals as [|raw tail]; simpl in accepted; try discriminate.
  - inversion accepted. auto.
  - destruct (pnorm base (ppkind par) raw) as [typ |] eqn:one;
      try discriminate.
    destruct (pvals base rest tail) as [types |] eqn:more; try discriminate.
    inversion accepted; subst.
    apply IH in more as [Hpars Hvals].
    simpl. auto.
Qed.

Lemma ptys_length : forall values types,
  ptys values = Some types -> length values = length types.
Proof.
  induction values as [|value rest IH]; intros types accepted;
    simpl in accepted.
  - inversion accepted. reflexivity.
  - destruct (yelab [] value); try discriminate.
    destruct (ptys rest) as [tail |] eqn:made; try discriminate.
    inversion accepted. simpl. f_equal. apply IH. reflexivity.
Qed.

Theorem pvals_sound : forall base pars actuals vals,
  pvals base pars actuals = Some vals -> pvalsR base pars actuals vals.
Proof.
  intros base pars.
  induction pars as [|par rest IH]; intros actuals vals accepted;
    destruct actuals as [|raw tail]; simpl in accepted; try discriminate.
  - inversion accepted. constructor.
  - destruct (pnorm base (ppkind par) raw) as [typ |] eqn:one;
      try discriminate.
    destruct (pvals base rest tail) as [types |] eqn:more; try discriminate.
    inversion accepted; subst.
    unfold pnorm in one.
    destruct (yelab base raw) as [kind |] eqn:typed; try discriminate.
    destruct (pkind_b (ppkind par) kind) eqn:kind_ok; try discriminate.
    econstructor; eauto.
Qed.

Theorem pvals_complete : forall base pars actuals vals,
  pvalsR base pars actuals vals -> pvals base pars actuals = Some vals.
Proof.
  intros base pars actuals vals accepted.
  induction accepted; simpl.
  - reflexivity.
  - unfold pnorm. rewrite H, H0, H1, IHaccepted. reflexivity.
Qed.

Lemma pzip_length : forall pars vals env,
  pzip pars vals = Some env -> length pars = length vals.
Proof.
  induction pars as [|par rest IH]; intros vals env accepted;
    destruct vals as [|typ tail]; simpl in accepted; try discriminate;
    try reflexivity.
  destruct (pzip rest tail) as [next |] eqn:more; try discriminate.
  simpl. f_equal. eapply IH. exact more.
Qed.

Theorem pnorm_kind : forall base kind raw out,
  pnorm base kind raw = Some out ->
  exists typ,
    yelab base raw = Some typ /\
    pkind_b kind typ = true /\
    ylift typ = Some out.
Proof.
  intros base kind raw out accepted.
  unfold pnorm in accepted.
  destruct (yelab base raw) as [typ |] eqn:typed; try discriminate.
  destruct (pkind_b kind typ) eqn:kind_ok; try discriminate.
  exists typ. auto.
Qed.

Lemma ifsub_pars : forall env item out,
  ifsub env item = Some out -> ipars out = ipars item.
Proof.
  intros env item out accepted.
  unfold ifsub in accepted.
  destruct (iasub env (iarr0 item)) as [spec |]; try discriminate.
  destruct (rsub env (ibody item)) as [body |]; try discriminate.
  inversion accepted. reflexivity.
Qed.

Lemma ifsub_laws : forall env item out,
  ifsub env item = Some out -> ilaws out = ilaws item.
Proof.
  intros env item out accepted.
  unfold ifsub in accepted.
  destruct (iasub env (iarr0 item)) as [spec |]; try discriminate.
  destruct (rsub env (ibody item)) as [body |]; try discriminate.
  inversion accepted. reflexivity.
Qed.

Theorem pspec_arity : forall base name item types sizes out,
  pspec base name item types sizes = Some out ->
  length types = length (ppars item) /\
  length sizes = length (ipars (pbase item)).
Proof.
  intros base name item types sizes out accepted.
  unfold pspec in accepted.
  destruct (pfn_b item && Nat.eqb (length types) (length (ppars item)))
    eqn:head; try discriminate.
  apply andb_true_iff in head as [_ arity].
  destruct (pvals base (ppars item) types) as [vals |] eqn:values;
    try discriminate.
  destruct (pzip (ppars item) vals) as [env |] eqn:limit; try discriminate.
  destruct (ifsub env (pbase item)) as [mono |] eqn:subbed; try discriminate.
  split.
  - apply Nat.eqb_eq. exact arity.
  - apply fspec_check_part in accepted as [made _].
    pose proof (fspec_arity _ _ _ _ _ made) as size_arity.
    pose proof (ifsub_pars _ _ _ subbed) as same_pars.
    rewrite same_pars in size_arity.
    exact size_arity.
Qed.

Theorem pspec_erased : forall base name item types sizes out,
  pspec base name item types sizes = Some out ->
  exists vals env mono,
    pvals base (ppars item) types = Some vals /\
    pzip (ppars item) vals = Some env /\
    ifsub env (pbase item) = Some mono /\
    fspec_check base name mono sizes = Some out.
Proof.
  intros base name item types sizes out accepted.
  unfold pspec in accepted.
  destruct (pfn_b item && Nat.eqb (length types) (length (ppars item)));
    try discriminate.
  destruct (pvals base (ppars item) types) as [vals |] eqn:values;
    try discriminate.
  destruct (pzip (ppars item) vals) as [env |] eqn:limit; try discriminate.
  destruct (ifsub env (pbase item)) as [mono |] eqn:subbed; try discriminate.
  exists vals, env, mono. auto.
Qed.

Theorem pspec_kinds : forall base name item types sizes out,
  pspec base name item types sizes = Some out ->
  exists vals, pvalsR base (ppars item) types vals.
Proof.
  intros base name item types sizes out accepted.
  apply pspec_erased in accepted as [vals [env [mono [values _]]]].
  exists vals. eapply pvals_sound. exact values.
Qed.

Theorem pspec_laws : forall base name item types sizes out,
  pspec base name item types sizes = Some out ->
  exists vals penv mono svals ienv,
    pvals base (ppars item) types = Some vals /\
    pzip (ppars item) vals = Some penv /\
    ifsub penv (pbase item) = Some mono /\
    ivals base sizes = Some svals /\
    izip base (ipars (pbase item)) svals = Some ienv /\
    lawsR ienv (ilaws (pbase item)).
Proof.
  intros base name item types sizes out accepted.
  apply pspec_erased in accepted as
    [vals [penv [mono [types_ok [limit [subbed made]]]]]].
  apply fspec_check_part in made as [specialized _].
  apply fspec_laws in specialized as
    [svals [ienv [sizes_ok [slimit laws_ok]]]].
  exists vals, penv, mono, svals, ienv.
  repeat split; try assumption.
  rewrite <- (ifsub_pars _ _ _ subbed). exact slimit.
  rewrite <- (ifsub_laws _ _ _ subbed). exact laws_ok.
Qed.

Theorem pspec_marks : forall base name item types sizes out typ row cost next,
  pspec base name item types sizes = Some out ->
  pcheck (acaps (farr out) ++ [aarg (farr out)]) (fbody out) =
    Some (typ, row, cost, next) ->
  forallb atom_b (aeff (farr out)) = true /\ within row (aeff (farr out)).
Proof.
  intros base name item types sizes out typ row cost next accepted checked.
  apply pspec_erased in accepted as [vals [env [mono [_ [_ [_ made]]]]]].
  eapply fspec_check_marks; eauto.
Qed.

Theorem pspec_under : forall base name item types sizes out
    typ row cost next limit,
  pspec base name item types sizes = Some out ->
  pcheck (acaps (farr out) ++ [aarg (farr out)]) (fbody out) =
    Some (typ, row, cost, next) ->
  alim (farr out) = Some limit ->
  res_b limit = true /\ rle cost limit.
Proof.
  intros base name item types sizes out typ row cost next limit
    accepted checked declared.
  apply pspec_erased in accepted as [vals [env [mono [_ [_ [_ made]]]]]].
  eapply fspec_check_under; eauto.
Qed.

Theorem pspec_many : forall base name item types sizes out,
  pspec base name item types sizes = Some out ->
  amul (farr out) = MM ->
  Forall (fun cap => smul cap = MM) (acaps (farr out)).
Proof.
  intros base name item types sizes out accepted mode.
  apply pspec_erased in accepted as [vals [env [mono [_ [_ [_ made]]]]]].
  eapply fspec_many; eauto.
Qed.

Theorem pspec_linear : forall base name item types sizes out cap,
  pspec base name item types sizes = Some out ->
  In cap (acaps (farr out)) ->
  smul cap = M1 ->
  amul (farr out) = M1.
Proof.
  intros base name item types sizes out cap accepted found linear.
  apply pspec_erased in accepted as [vals [env [mono [_ [_ [_ made]]]]]].
  eapply fspec_linear; eauto.
Qed.