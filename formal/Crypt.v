(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.

Require Import Fp.
Require Import Fhe.
Require Import Param.

Import ListNotations.

Record ct : Type := Ct {
  cty : enc;
  cval : Z
}.

Definition cenv := list (nat * ct).

Fixpoint cfind (name : nat) (env : cenv) : option ct :=
  match env with
  | [] => None
  | (id, value) :: rest =>
      if Nat.eqb name id then Some value else cfind name rest
  end.

Fixpoint tenv (env : cenv) : fenv :=
  match env with
  | [] => []
  | (name, value) :: rest => (name, cty value) :: tenv rest
  end.

Fixpoint vals_b (env : cenv) : bool :=
  match env with
  | [] => true
  | (_, value) :: rest => Fp.valid (cval value) && vals_b rest
  end.

Definition cenv_b (profile : fprofile) (env : cenv) : bool :=
  env_b profile (tenv env) && vals_b env.

Definition dec (value : ct) : Z := cval value.

Definition ctrim (profile : fprofile) (rem : nat) (prior : ct)
    : option ct :=
  if Nat.leb rem (erem (cty prior)) then
    match cfg_find (ekey (cty prior)) profile with
    | Some _ => Some (Ct (Enc (ekey (cty prior)) rem) (cval prior))
    | None => None
    end
  else None.

Definition cadd (profile : fprofile) (left right : ct) : option ct :=
  if enc_eqb (cty left) (cty right) then
    match cfg_find (ekey (cty left)) profile with
    | Some _ => Some (Ct (cty left) (Fp.add (dec left) (dec right)))
    | None => None
    end
  else None.

Definition cmul (profile : fprofile) (left right : ct) : option ct :=
  if enc_eqb (cty left) (cty right) then
    match erem (cty left) with
    | 0 => None
    | S rem =>
        match cfg_find (ekey (cty left)) profile with
        | Some _ =>
            Some (Ct (Enc (ekey (cty left)) rem)
              (Fp.mul (dec left) (dec right)))
        | None => None
        end
    end
  else None.

Definition cre (profile : fprofile) (prior : ct) : option ct :=
  if Nat.eqb (erem (cty prior)) 0 then
    match cfg_find (ekey (cty prior)) profile with
    | Some cfg =>
        Some (Ct (Enc (ekey (cty prior)) (cfull cfg)) (cval prior))
    | None => None
    end
  else None.

Fixpoint plain (env : cenv) (term : ftm) : option Z :=
  match term with
  | FVar name =>
      match cfind name env with
      | Some value => Some (dec value)
      | None => None
      end
  | FTrim _ body => plain env body
  | FAdd lhs rhs =>
      match plain env lhs, plain env rhs with
      | Some lhs, Some rhs => Some (Fp.add lhs rhs)
      | _, _ => None
      end
  | FMul lhs rhs =>
      match plain env lhs, plain env rhs with
      | Some lhs, Some rhs => Some (Fp.mul lhs rhs)
      | _, _ => None
      end
  | FRe body => plain env body
  end.

Fixpoint crun (profile : fprofile) (env : cenv) (term : ftm)
    : option ct :=
  match term with
  | FVar name => cfind name env
  | FTrim rem body =>
      match crun profile env body with
      | Some prior => ctrim profile rem prior
      | None => None
      end
  | FAdd lhs rhs =>
      match crun profile env lhs, crun profile env rhs with
      | Some lhs, Some rhs => cadd profile lhs rhs
      | _, _ => None
      end
  | FMul lhs rhs =>
      match crun profile env lhs, crun profile env rhs with
      | Some lhs, Some rhs => cmul profile lhs rhs
      | _, _ => None
      end
  | FRe body =>
      match crun profile env body with
      | Some prior => cre profile prior
      | None => None
      end
  end.

Record xout : Type := Xout {
  xinfo : finfo;
  xparam : fparam;
  xct : ct
}.

Definition exec (profile : fprofile) (catalog : fcatalog)
    (env : cenv) (term : ftm) : option xout :=
  if cenv_b profile env then
    if catalog_b catalog then
      match fcheck profile (tenv env) term with
      | Some info =>
          match params catalog info with
          | Some param =>
              match crun profile env term with
              | Some value =>
                  if enc_eqb (cty value) (ety info) then
                    Some (Xout info param value)
                  else None
              | None => None
              end
          | None => None
          end
      | None => None
      end
    else None
  else None.

Lemma ctrim_dec : forall profile rem prior out,
  ctrim profile rem prior = Some out -> dec out = dec prior.
Proof.
  intros profile rem prior out H. unfold ctrim in H.
  destruct (Nat.leb rem (erem (cty prior))); try discriminate.
  destruct (cfg_find (ekey (cty prior)) profile); inversion H. reflexivity.
Qed.

Lemma cadd_dec : forall profile left right out,
  cadd profile left right = Some out ->
  dec out = Fp.add (dec left) (dec right).
Proof.
  intros profile left right out H. unfold cadd in H.
  destruct (enc_eqb (cty left) (cty right)); try discriminate.
  destruct (cfg_find (ekey (cty left)) profile); inversion H. reflexivity.
Qed.

Lemma cmul_dec : forall profile left right out,
  cmul profile left right = Some out ->
  dec out = Fp.mul (dec left) (dec right).
Proof.
  intros profile left right out H. unfold cmul in H.
  destruct (enc_eqb (cty left) (cty right)); try discriminate.
  destruct (erem (cty left)); try discriminate.
  destruct (cfg_find (ekey (cty left)) profile); inversion H. reflexivity.
Qed.

Lemma cre_dec : forall profile prior out,
  cre profile prior = Some out -> dec out = dec prior.
Proof.
  intros profile prior out H. unfold cre in H.
  destruct (Nat.eqb (erem (cty prior)) 0); try discriminate.
  destruct (cfg_find (ekey (cty prior)) profile); inversion H. reflexivity.
Qed.

Lemma cfind_valid : forall env name out,
  vals_b env = true ->
  cfind name env = Some out ->
  Fp.valid (cval out) = true.
Proof.
  induction env as [|[id value] rest IH]; intros name out Hvals Hfind.
  - discriminate.
  - simpl in Hvals, Hfind.
    apply andb_true_iff in Hvals. destruct Hvals as [Hvalue Hrest].
    destruct (Nat.eqb name id).
    + inversion Hfind; subst. exact Hvalue.
    + eapply IH; eauto.
Qed.

Lemma ctrim_valid : forall profile rem prior out,
  Fp.valid (cval prior) = true ->
  ctrim profile rem prior = Some out ->
  Fp.valid (cval out) = true.
Proof.
  intros profile rem prior out Hvalid Hrun.
  change (Fp.valid (dec prior) = true) in Hvalid.
  change (Fp.valid (dec out) = true).
  rewrite (ctrim_dec profile rem prior out Hrun). exact Hvalid.
Qed.

Lemma cadd_valid : forall profile left right out,
  cadd profile left right = Some out ->
  Fp.valid (cval out) = true.
Proof.
  intros profile left right out Hrun.
  change (Fp.valid (dec out) = true).
  rewrite (cadd_dec profile left right out Hrun). apply Fp.add_valid.
Qed.

Lemma cmul_valid : forall profile left right out,
  cmul profile left right = Some out ->
  Fp.valid (cval out) = true.
Proof.
  intros profile left right out Hrun.
  change (Fp.valid (dec out) = true).
  rewrite (cmul_dec profile left right out Hrun). apply Fp.mul_valid.
Qed.

Lemma cre_valid : forall profile prior out,
  Fp.valid (cval prior) = true ->
  cre profile prior = Some out ->
  Fp.valid (cval out) = true.
Proof.
  intros profile prior out Hvalid Hrun.
  change (Fp.valid (dec prior) = true) in Hvalid.
  change (Fp.valid (dec out) = true).
  rewrite (cre_dec profile prior out Hrun). exact Hvalid.
Qed.

Theorem crun_plain : forall profile env term out,
  crun profile env term = Some out ->
  plain env term = Some (dec out).
Proof.
  intros profile env term.
  induction term as [name | rem body IH | left IHl right IHr
    | left IHl right IHr | body IH]; intros out H; simpl in H |- *.
  - destruct (cfind name env) as [value |] eqn:Hfind; try discriminate.
    inversion H. reflexivity.
  - destruct (crun profile env body) as [prior |] eqn:Hrun;
      try discriminate.
    specialize (IH prior eq_refl).
    rewrite IH. f_equal. symmetry. eapply ctrim_dec. exact H.
  - destruct (crun profile env left) as [lhs |] eqn:Hl; try discriminate.
    destruct (crun profile env right) as [rhs |] eqn:Hr; try discriminate.
    specialize (IHl lhs eq_refl). specialize (IHr rhs eq_refl).
    rewrite IHl, IHr. f_equal. symmetry. eapply cadd_dec. exact H.
  - destruct (crun profile env left) as [lhs |] eqn:Hl; try discriminate.
    destruct (crun profile env right) as [rhs |] eqn:Hr; try discriminate.
    specialize (IHl lhs eq_refl). specialize (IHr rhs eq_refl).
    rewrite IHl, IHr. f_equal. symmetry. eapply cmul_dec. exact H.
  - destruct (crun profile env body) as [prior |] eqn:Hrun;
      try discriminate.
    specialize (IH prior eq_refl).
    rewrite IH. f_equal. symmetry. eapply cre_dec. exact H.
Qed.

Theorem crun_value : forall profile env term out,
  vals_b env = true ->
  crun profile env term = Some out ->
  Fp.valid (cval out) = true.
Proof.
  intros profile env term.
  induction term as [name | rem body IH | left IHl right IHr
    | left IHl right IHr | body IH]; intros out Hvals H; simpl in H |- *.
  - eapply cfind_valid; eauto.
  - destruct (crun profile env body) as [prior |] eqn:Hrun;
      try discriminate.
    eapply ctrim_valid; [eapply IH; eauto | exact H].
  - destruct (crun profile env left) as [lhs |] eqn:Hl; try discriminate.
    destruct (crun profile env right) as [rhs |] eqn:Hr; try discriminate.
    eapply cadd_valid. exact H.
  - destruct (crun profile env left) as [lhs |] eqn:Hl; try discriminate.
    destruct (crun profile env right) as [rhs |] eqn:Hr; try discriminate.
    eapply cmul_valid. exact H.
  - destruct (crun profile env body) as [prior |] eqn:Hrun;
      try discriminate.
    eapply cre_valid; [eapply IH; eauto | exact H].
Qed.

Theorem crun_det : forall profile env term left right,
  crun profile env term = Some left ->
  crun profile env term = Some right ->
  left = right.
Proof.
  intros profile env term left right Hl Hr.
  rewrite Hl in Hr. inversion Hr. reflexivity.
Qed.

Lemma enc_eqb_eq : forall left right,
  enc_eqb left right = true -> left = right.
Proof.
  intros [lk lr] [rk rr] H. simpl in H.
  apply andb_true_iff in H. destruct H as [Hk Hr].
  apply Nat.eqb_eq in Hk. apply Nat.eqb_eq in Hr.
  cbn in Hk, Hr. subst. reflexivity.
Qed.

Theorem exec_check : forall profile catalog env term out,
  exec profile catalog env term = Some out ->
  fcheck profile (tenv env) term = Some (xinfo out).
Proof.
  intros profile catalog env term out H. unfold exec in H.
  destruct (cenv_b profile env); try discriminate.
  destruct (catalog_b catalog); try discriminate.
  destruct (fcheck profile (tenv env) term) as [info |] eqn:Hcheck;
    try discriminate.
  destruct (params catalog info); try discriminate.
  destruct (crun profile env term); try discriminate.
  destruct (enc_eqb (cty c) (ety info)); inversion H; subst.
  reflexivity.
Qed.

Theorem exec_param : forall profile catalog env term out,
  exec profile catalog env term = Some out ->
  pkey (xparam out) = ekey (ety (xinfo out)) /\
  fpeak (xinfo out) <= pcap (xparam out).
Proof.
  intros profile catalog env term out H. unfold exec in H.
  destruct (cenv_b profile env); try discriminate.
  destruct (catalog_b catalog); try discriminate.
  destruct (fcheck profile (tenv env) term) as [info |] eqn:Hcheck;
    try discriminate.
  destruct (params catalog info) as [param |] eqn:Hparam; try discriminate.
  destruct (crun profile env term); try discriminate.
  destruct (enc_eqb (cty c) (ety info)); inversion H; subst.
  cbn. eapply params_sound. exact Hparam.
Qed.

Theorem exec_type : forall profile catalog env term out,
  exec profile catalog env term = Some out ->
  cty (xct out) = ety (xinfo out).
Proof.
  intros profile catalog env term out H. unfold exec in H.
  destruct (cenv_b profile env); try discriminate.
  destruct (catalog_b catalog); try discriminate.
  destruct (fcheck profile (tenv env) term); try discriminate.
  destruct (params catalog f); try discriminate.
  destruct (crun profile env term) as [value |] eqn:Hrun; try discriminate.
  destruct (enc_eqb (cty value) (ety f)) eqn:Htype; inversion H; subst.
  cbn. apply enc_eqb_eq. exact Htype.
Qed.

Theorem exec_value : forall profile catalog env term out,
  exec profile catalog env term = Some out ->
  Fp.valid (cval (xct out)) = true.
Proof.
  intros profile catalog env term out H. unfold exec in H.
  destruct (cenv_b profile env) eqn:Henv; try discriminate.
  destruct (catalog_b catalog); try discriminate.
  destruct (fcheck profile (tenv env) term); try discriminate.
  destruct (params catalog f); try discriminate.
  destruct (crun profile env term) as [value |] eqn:Hrun; try discriminate.
  destruct (enc_eqb (cty value) (ety f)); inversion H; subst. cbn.
  unfold cenv_b in Henv. apply andb_true_iff in Henv.
  destruct Henv as [_ Hvals]. eapply crun_value; eauto.
Qed.

Theorem exec_det : forall profile catalog env term left right,
  exec profile catalog env term = Some left ->
  exec profile catalog env term = Some right ->
  left = right.
Proof.
  intros profile catalog env term left right Hl Hr.
  rewrite Hl in Hr. inversion Hr. reflexivity.
Qed.

Theorem decrypt_exact : forall profile catalog env term out,
  exec profile catalog env term = Some out ->
  plain env term = Some (dec (xct out)).
Proof.
  intros profile catalog env term out H. unfold exec in H.
  destruct (cenv_b profile env); try discriminate.
  destruct (catalog_b catalog); try discriminate.
  destruct (fcheck profile (tenv env) term); try discriminate.
  destruct (params catalog f); try discriminate.
  destruct (crun profile env term) as [value |] eqn:Hrun; try discriminate.
  destruct (enc_eqb (cty value) (ety f)); inversion H; subst.
  cbn. eapply crun_plain. exact Hrun.
Qed.