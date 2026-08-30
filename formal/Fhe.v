(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Lim.

Import ListNotations.

Inductive fop : Type :=
| OpMul : nat -> fop
| OpRe : nat -> fop.

Record fcfg : Type := Fcfg {
  cfull : nat;
  cadd : nat;
  cmul : nat;
  cre : nat
}.

Definition fprofile := list (nat * fcfg).

Record enc : Type := Enc {
  ekey : nat;
  erem : nat
}.

Definition fenv := list (nat * enc).

Inductive ftm : Type :=
| FVar : nat -> ftm
| FTrim : nat -> ftm -> ftm
| FAdd : ftm -> ftm -> ftm
| FMul : ftm -> ftm -> ftm
| FRe : ftm -> ftm.

Record finfo : Type := Finfo {
  ety : enc;
  fsteps : nat;
  fwork : nat;
  fpeak : nat;
  fplan : list fop
}.

Definition fcount_max : nat := 4096.
Definition fdepth_max : nat := 4096.
Definition fnodes_max : nat := 100000.

Definition ffit (value : nat) : bool := Nat.leb value lim.

Fixpoint cfg_find (key : nat) (profile : fprofile) : option fcfg :=
  match profile with
  | [] => None
  | (id, cfg) :: rest =>
      if Nat.eqb key id then Some cfg else cfg_find key rest
  end.

Fixpoint key_has (key : nat) (profile : fprofile) : bool :=
  match profile with
  | [] => false
  | (id, _) :: rest => Nat.eqb key id || key_has key rest
  end.

Fixpoint key_uniq (profile : fprofile) : bool :=
  match profile with
  | [] => true
  | (key, _) :: rest => negb (key_has key rest) && key_uniq rest
  end.

Definition cfg_b (cfg : fcfg) : bool :=
  ffit (cfull cfg)
    && ffit (cadd cfg) && negb (Nat.eqb (cadd cfg) 0)
    && ffit (cmul cfg) && negb (Nat.eqb (cmul cfg) 0)
    && ffit (cre cfg) && negb (Nat.eqb (cre cfg) 0).

Fixpoint cfgs_b (profile : fprofile) : bool :=
  match profile with
  | [] => true
  | (key, cfg) :: rest => ffit key && cfg_b cfg && cfgs_b rest
  end.

Definition profile_b (profile : fprofile) : bool :=
  Nat.leb (length profile) fcount_max && key_uniq profile && cfgs_b profile.

Definition enc_eqb (left right : enc) : bool :=
  Nat.eqb (ekey left) (ekey right) && Nat.eqb (erem left) (erem right).

Definition legal_b (profile : fprofile) (typ : enc) : bool :=
  match cfg_find (ekey typ) profile with
  | Some cfg => Nat.leb (erem typ) (cfull cfg)
  | None => false
  end.

Fixpoint env_find (name : nat) (env : fenv) : option enc :=
  match env with
  | [] => None
  | (id, typ) :: rest =>
      if Nat.eqb name id then Some typ else env_find name rest
  end.

Fixpoint env_has (name : nat) (env : fenv) : bool :=
  match env with
  | [] => false
  | (id, _) :: rest => Nat.eqb name id || env_has name rest
  end.

Fixpoint env_uniq (env : fenv) : bool :=
  match env with
  | [] => true
  | (name, _) :: rest => negb (env_has name rest) && env_uniq rest
  end.

Fixpoint env_vals_b (profile : fprofile) (env : fenv) : bool :=
  match env with
  | [] => true
  | (_, typ) :: rest => legal_b profile typ && env_vals_b profile rest
  end.

Definition env_b (profile : fprofile) (env : fenv) : bool :=
  Nat.leb (length env) fcount_max && env_uniq env && env_vals_b profile env.

Fixpoint ftdepth (term : ftm) : nat :=
  match term with
  | FVar _ => 0
  | FTrim _ body => S (ftdepth body)
  | FAdd lhs rhs =>
      S (Nat.max (ftdepth lhs) (ftdepth rhs))
  | FMul lhs rhs =>
      S (Nat.max (ftdepth lhs) (ftdepth rhs))
  | FRe body => S (ftdepth body)
  end.

Fixpoint ftnodes (term : ftm) : nat :=
  match term with
  | FVar _ => 1
  | FTrim _ body => S (ftnodes body)
  | FAdd lhs rhs => S (ftnodes lhs + ftnodes rhs)
  | FMul lhs rhs => S (ftnodes lhs + ftnodes rhs)
  | FRe body => S (ftnodes body)
  end.

Definition ftm_b (term : ftm) : bool :=
  Nat.leb (ftdepth term) fdepth_max && Nat.leb (ftnodes term) fnodes_max.

Definition nmax (left right : nat) : nat :=
  if Nat.leb left right then right else left.

Definition used (cfg : fcfg) (rem : nat) : nat := cfull cfg - rem.

Definition sum2 (left right : nat) : option nat :=
  let value := left + right in
  if ffit value then Some value else None.

Definition sum3 (left right op : nat) : option nat :=
  let value := left + right + op in
  if ffit value then Some value else None.

Definition ftrim (profile : fprofile) (rem : nat) (out : finfo)
    : option finfo :=
  if Nat.leb rem (erem (ety out)) then
    match cfg_find (ekey (ety out)) profile with
    | Some cfg =>
        Some (Finfo (Enc (ekey (ety out)) rem)
          (fsteps out) (fwork out) (nmax (fpeak out) (used cfg rem))
          (fplan out))
    | None => None
    end
  else None.

Definition fadd (profile : fprofile) (left right : finfo) : option finfo :=
  if enc_eqb (ety left) (ety right) then
    match cfg_find (ekey (ety left)) profile,
        sum3 (fsteps left) (fsteps right) 1 with
    | Some cfg, Some steps =>
        match sum3 (fwork left) (fwork right) (cadd cfg) with
        | Some work => Some (Finfo (ety left) steps work
            (nmax (fpeak left) (fpeak right))
            (fplan left ++ fplan right))
        | None => None
        end
    | _, _ => None
    end
  else None.

Definition fmul (profile : fprofile) (left right : finfo) : option finfo :=
  if enc_eqb (ety left) (ety right) then
    match erem (ety left) with
    | 0 => None
    | S rem =>
        match cfg_find (ekey (ety left)) profile,
            sum3 (fsteps left) (fsteps right) 1 with
        | Some cfg, Some steps =>
            match sum3 (fwork left) (fwork right) (cmul cfg) with
            | Some work =>
                let typ := Enc (ekey (ety left)) rem in
                Some (Finfo typ steps work
                  (nmax (nmax (fpeak left) (fpeak right)) (used cfg rem))
                  (fplan left ++ fplan right ++ [OpMul (ekey typ)]))
            | None => None
            end
        | _, _ => None
        end
    end
  else None.

Definition fre (profile : fprofile) (out : finfo) : option finfo :=
  if Nat.eqb (erem (ety out)) 0 then
    match cfg_find (ekey (ety out)) profile,
        sum2 (fsteps out) 1 with
    | Some cfg, Some steps =>
        match sum2 (fwork out) (cre cfg) with
        | Some work => Some (Finfo (Enc (ekey (ety out)) (cfull cfg))
            steps work (nmax (fpeak out) (cfull cfg))
            (fplan out ++ [OpRe (ekey (ety out))]))
        | None => None
        end
    | _, _ => None
    end
  else None.

Fixpoint frun (profile : fprofile) (env : fenv) (term : ftm) : option finfo :=
  match term with
  | FVar name =>
      match env_find name env with
      | Some typ =>
          match cfg_find (ekey typ) profile with
          | Some cfg =>
              if legal_b profile typ then
                Some (Finfo typ 0 0 (used cfg (erem typ)) [])
              else None
          | None => None
          end
      | None => None
      end
  | FTrim rem term =>
      match frun profile env term with
      | Some out => ftrim profile rem out
      | None => None
      end
  | FAdd lhs rhs =>
      match frun profile env lhs, frun profile env rhs with
      | Some lout, Some rout => fadd profile lout rout
      | _, _ => None
      end
  | FMul lhs rhs =>
      match frun profile env lhs, frun profile env rhs with
      | Some lout, Some rout => fmul profile lout rout
      | _, _ => None
      end
  | FRe term =>
      match frun profile env term with
      | Some out => fre profile out
      | None => None
      end
  end.

Definition fcheck (profile : fprofile) (env : fenv) (term : ftm)
    : option finfo :=
  if profile_b profile then
    if env_b profile env then
      if ftm_b term then frun profile env term else None
    else None
  else None.

Inductive frunR (profile : fprofile) (env : fenv) : ftm -> finfo -> Prop :=
| FRVar : forall name typ cfg,
    env_find name env = Some typ ->
    cfg_find (ekey typ) profile = Some cfg ->
    legal_b profile typ = true ->
    frunR profile env (FVar name) (Finfo typ 0 0 (used cfg (erem typ)) [])
| FRTrim : forall rem term prior out,
    frunR profile env term prior ->
    ftrim profile rem prior = Some out ->
    frunR profile env (FTrim rem term) out
| FRAdd : forall left right lout rout out,
    frunR profile env left lout ->
    frunR profile env right rout ->
    fadd profile lout rout = Some out ->
    frunR profile env (FAdd left right) out
| FRMul : forall left right lout rout out,
    frunR profile env left lout ->
    frunR profile env right rout ->
    fmul profile lout rout = Some out ->
    frunR profile env (FMul left right) out
| FRRe : forall term prior out,
    frunR profile env term prior ->
    fre profile prior = Some out ->
    frunR profile env (FRe term) out.

Theorem frun_sound : forall profile env term out,
  frun profile env term = Some out -> frunR profile env term out.
Proof.
  intros profile env term.
  induction term as [name | rem term IH | left IHl right IHr
    | left IHl right IHr | term IH]; intros out H; simpl in H.
  - destruct (env_find name env) as [typ |] eqn:Henv; try discriminate.
    destruct (cfg_find (ekey typ) profile) as [cfg |] eqn:Hcfg; try discriminate.
    destruct (legal_b profile typ) eqn:Hlegal; inversion H; subst.
    econstructor; eauto.
  - destruct (frun profile env term) as [prior |] eqn:Hrun; try discriminate.
    eapply FRTrim; eauto.
  - destruct (frun profile env left) as [lout |] eqn:Hl; try discriminate.
    destruct (frun profile env right) as [rout |] eqn:Hr; try discriminate.
    eapply FRAdd; eauto.
  - destruct (frun profile env left) as [lout |] eqn:Hl; try discriminate.
    destruct (frun profile env right) as [rout |] eqn:Hr; try discriminate.
    eapply FRMul; eauto.
  - destruct (frun profile env term) as [prior |] eqn:Hrun; try discriminate.
    eapply FRRe; eauto.
Qed.

Theorem frun_complete : forall profile env term out,
  frunR profile env term out -> frun profile env term = Some out.
Proof.
  intros profile env term out H.
  induction H; simpl.
  - rewrite H, H0, H1. reflexivity.
  - rewrite IHfrunR, H0. reflexivity.
  - rewrite IHfrunR1, IHfrunR2, H1. reflexivity.
  - rewrite IHfrunR1, IHfrunR2, H1. reflexivity.
  - rewrite IHfrunR, H0. reflexivity.
Qed.

Theorem frun_unique : forall profile env term left right,
  frunR profile env term left ->
  frunR profile env term right ->
  left = right.
Proof.
  intros profile env term left right Hl Hr.
  pose proof (frun_complete _ _ _ _ Hl) as El.
  pose proof (frun_complete _ _ _ _ Hr) as Er.
  rewrite El in Er. inversion Er. reflexivity.
Qed.

Theorem fcheck_sound : forall profile env term out,
  fcheck profile env term = Some out ->
  profile_b profile = true /\
  env_b profile env = true /\
  ftm_b term = true /\
  frunR profile env term out.
Proof.
  intros profile env term out H.
  unfold fcheck in H.
  destruct (profile_b profile) eqn:Hp; try discriminate.
  destruct (env_b profile env) eqn:He; try discriminate.
  destruct (ftm_b term) eqn:Ht; try discriminate.
  repeat split; try assumption.
  eapply frun_sound. exact H.
Qed.

Theorem fcheck_complete : forall profile env term out,
  profile_b profile = true ->
  env_b profile env = true ->
  ftm_b term = true ->
  frunR profile env term out ->
  fcheck profile env term = Some out.
Proof.
  intros profile env term out Hp He Ht Hrun.
  unfold fcheck. rewrite Hp, He, Ht.
  apply frun_complete. exact Hrun.
Qed.

Theorem ftrim_no_gain : forall profile rem prior out,
  ftrim profile rem prior = Some out ->
  ekey (ety out) = ekey (ety prior) /\
  erem (ety out) <= erem (ety prior).
Proof.
  intros profile rem prior out H.
  unfold ftrim in H.
  destruct (Nat.leb rem (erem (ety prior))) eqn:Hle; try discriminate.
  destruct (cfg_find (ekey (ety prior)) profile); inversion H; subst.
  split; simpl.
  - reflexivity.
  - apply Nat.leb_le. exact Hle.
Qed.

Theorem ftrim_legal : forall profile rem prior out,
  legal_b profile (ety prior) = true ->
  ftrim profile rem prior = Some out ->
  legal_b profile (ety out) = true.
Proof.
  intros profile rem prior out Hprior Hrun.
  unfold ftrim in Hrun.
  destruct (Nat.leb rem (erem (ety prior))) eqn:Hle; try discriminate.
  destruct (cfg_find (ekey (ety prior)) profile) as [cfg |] eqn:Hcfg;
    try discriminate.
  inversion Hrun; subst. clear Hrun.
  unfold legal_b in *. simpl.
  rewrite Hcfg in Hprior. rewrite Hcfg.
  apply Nat.leb_le in Hle. apply Nat.leb_le in Hprior.
  apply Nat.leb_le. eapply Nat.le_trans; eauto.
Qed.

Theorem fadd_depth : forall profile left right out,
  fadd profile left right = Some out ->
  ety out = ety left /\ ety left = ety right.
Proof.
  intros profile left right out H.
  unfold fadd in H.
  destruct (enc_eqb (ety left) (ety right)) eqn:Heq; try discriminate.
  destruct (cfg_find (ekey (ety left)) profile); try discriminate.
  destruct (sum3 (fsteps left) (fsteps right) 1); try discriminate.
  destruct (sum3 (fwork left) (fwork right) (cadd f)); inversion H; subst.
  split; auto.
  unfold enc_eqb in Heq.
  destruct (Nat.eqb (ekey (ety left)) (ekey (ety right))) eqn:Hkey;
    try discriminate.
  apply Nat.eqb_eq in Hkey.
  apply Nat.eqb_eq in Heq.
  destruct (ety left), (ety right); simpl in *. subst. reflexivity.
Qed.

Theorem fadd_legal : forall profile left right out,
  legal_b profile (ety left) = true ->
  fadd profile left right = Some out ->
  legal_b profile (ety out) = true.
Proof.
  intros profile left right out Hlegal Hrun.
  destruct (fadd_depth profile left right out Hrun) as [Hout _].
  rewrite Hout. exact Hlegal.
Qed.

Theorem fmul_depth : forall profile left right out,
  fmul profile left right = Some out ->
  ekey (ety out) = ekey (ety left) /\
  erem (ety left) = S (erem (ety out)) /\
  ety left = ety right.
Proof.
  intros profile left right out H.
  unfold fmul in H.
  destruct (enc_eqb (ety left) (ety right)) eqn:Heq; try discriminate.
  destruct (erem (ety left)) as [|rem] eqn:Hrem; try discriminate.
  destruct (cfg_find (ekey (ety left)) profile); try discriminate.
  destruct (sum3 (fsteps left) (fsteps right) 1); try discriminate.
  destruct (sum3 (fwork left) (fwork right) (cmul f)); inversion H; subst.
  simpl. repeat split; auto.
  unfold enc_eqb in Heq.
  destruct (Nat.eqb (ekey (ety left)) (ekey (ety right))) eqn:Hkey;
    try discriminate.
  apply Nat.eqb_eq in Hkey.
  apply Nat.eqb_eq in Heq.
  destruct (ety left), (ety right); simpl in *. subst. reflexivity.
Qed.

Theorem fmul_legal : forall profile left right out,
  legal_b profile (ety left) = true ->
  fmul profile left right = Some out ->
  legal_b profile (ety out) = true.
Proof.
  intros profile left right out Hlegal Hrun.
  destruct (fmul_depth profile left right out Hrun)
    as [Hkey [Hrem _]].
  unfold legal_b in *.
  destruct (cfg_find (ekey (ety left)) profile) as [cfg |] eqn:Hcfg;
    try discriminate.
  rewrite Hkey. rewrite Hcfg.
  apply Nat.leb_le in Hlegal. apply Nat.leb_le.
  rewrite Hrem in Hlegal.
  eapply Nat.le_trans.
  - apply Nat.le_succ_diag_r.
  - exact Hlegal.
Qed.

Theorem fre_depth : forall profile prior out,
  fre profile prior = Some out ->
  erem (ety prior) = 0 /\
  exists cfg,
    cfg_find (ekey (ety prior)) profile = Some cfg /\
    ekey (ety out) = ekey (ety prior) /\
    erem (ety out) = cfull cfg.
Proof.
  intros profile prior out H.
  unfold fre in H.
  destruct (Nat.eqb (erem (ety prior)) 0) eqn:Hrem; try discriminate.
  destruct (cfg_find (ekey (ety prior)) profile) as [cfg |] eqn:Hcfg;
    try discriminate.
  destruct (sum2 (fsteps prior) 1); try discriminate.
  destruct (sum2 (fwork prior) (cre cfg)); inversion H; subst.
  apply Nat.eqb_eq in Hrem.
  split; [exact Hrem |].
  exists cfg. repeat split; auto.
Qed.

Theorem fre_legal : forall profile prior out,
  fre profile prior = Some out ->
  legal_b profile (ety out) = true.
Proof.
  intros profile prior out Hrun.
  destruct (fre_depth profile prior out Hrun)
    as [_ [cfg [Hcfg [Hkey Hrem]]]].
  unfold legal_b. rewrite Hkey, Hcfg, Hrem.
  apply Nat.leb_refl.
Qed.

Theorem frun_legal : forall profile env term out,
  frunR profile env term out ->
  legal_b profile (ety out) = true.
Proof.
  intros profile env term out Hrun.
  induction Hrun; eauto using ftrim_legal, fadd_legal, fmul_legal, fre_legal.
Qed.

Corollary fcheck_legal : forall profile env term out,
  fcheck profile env term = Some out ->
  legal_b profile (ety out) = true.
Proof.
  intros profile env term out Hcheck.
  destruct (fcheck_sound profile env term out Hcheck) as [_ [_ [_ Hrun]]].
  eapply frun_legal. exact Hrun.
Qed.