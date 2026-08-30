(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Fhe.

Import ListNotations.

Inductive htm : Type :=
| HArg : nat -> enc -> htm
| HTrim : nat -> htm -> enc -> htm
| HAdd : htm -> htm -> enc -> htm
| HMul : htm -> htm -> enc -> htm
| HRe : htm -> enc -> htm.

Definition hty (term : htm) : enc :=
  match term with
  | HArg _ typ | HTrim _ _ typ | HAdd _ _ typ
  | HMul _ _ typ | HRe _ typ => typ
  end.

Fixpoint herase (term : htm) : ftm :=
  match term with
  | HArg name _ => FVar name
  | HTrim rem body _ => FTrim rem (herase body)
  | HAdd lhs rhs _ => FAdd (herase lhs) (herase rhs)
  | HMul lhs rhs _ => FMul (herase lhs) (herase rhs)
  | HRe body _ => FRe (herase body)
  end.

Definition ht_trim (profile : fprofile) (rem : nat) (prior : enc)
    : option enc :=
  if Nat.leb rem (erem prior) then
    match cfg_find (ekey prior) profile with
    | Some _ => Some (Enc (ekey prior) rem)
    | None => None
    end
  else None.

Definition ht_add (profile : fprofile) (left right : enc) : option enc :=
  if enc_eqb left right then
    match cfg_find (ekey left) profile with
    | Some _ => Some left
    | None => None
    end
  else None.

Definition ht_mul (profile : fprofile) (left right : enc) : option enc :=
  if enc_eqb left right then
    match erem left with
    | 0 => None
    | S rem =>
        match cfg_find (ekey left) profile with
        | Some _ => Some (Enc (ekey left) rem)
        | None => None
        end
    end
  else None.

Definition ht_re (profile : fprofile) (prior : enc) : option enc :=
  if Nat.eqb (erem prior) 0 then
    match cfg_find (ekey prior) profile with
    | Some cfg => Some (Enc (ekey prior) (cfull cfg))
    | None => None
    end
  else None.

Fixpoint hval (profile : fprofile) (env : fenv) (term : htm) : option enc :=
  match term with
  | HArg name out =>
      match env_find name env with
      | Some typ => if enc_eqb typ out then Some out else None
      | None => None
      end
  | HTrim rem body out =>
      match hval profile env body with
      | Some prior =>
          match ht_trim profile rem prior with
          | Some typ => if enc_eqb typ out then Some out else None
          | None => None
          end
      | None => None
      end
  | HAdd lhs rhs out =>
      match hval profile env lhs, hval profile env rhs with
      | Some lhs, Some rhs =>
          match ht_add profile lhs rhs with
          | Some typ => if enc_eqb typ out then Some out else None
          | None => None
          end
      | _, _ => None
      end
  | HMul lhs rhs out =>
      match hval profile env lhs, hval profile env rhs with
      | Some lhs, Some rhs =>
          match ht_mul profile lhs rhs with
          | Some typ => if enc_eqb typ out then Some out else None
          | None => None
          end
      | _, _ => None
      end
  | HRe body out =>
      match hval profile env body with
      | Some prior =>
          match ht_re profile prior with
          | Some typ => if enc_eqb typ out then Some out else None
          | None => None
          end
      | None => None
      end
  end.

Fixpoint hem (profile : fprofile) (env : fenv) (term : ftm)
    : option (htm * finfo) :=
  match term with
  | FVar name =>
      match frun profile env term with
      | Some out => Some (HArg name (ety out), out)
      | None => None
      end
  | FTrim rem body =>
      match hem profile env body with
      | Some (prior_plan, prior) =>
          match ftrim profile rem prior with
          | Some out => Some (HTrim rem prior_plan (ety out), out)
          | None => None
          end
      | None => None
      end
  | FAdd lhs rhs =>
      match hem profile env lhs, hem profile env rhs with
      | Some (lhs_plan, lhs_out), Some (rhs_plan, rhs_out) =>
          match fadd profile lhs_out rhs_out with
          | Some out => Some (HAdd lhs_plan rhs_plan (ety out), out)
          | None => None
          end
      | _, _ => None
      end
  | FMul lhs rhs =>
      match hem profile env lhs, hem profile env rhs with
      | Some (lhs_plan, lhs_out), Some (rhs_plan, rhs_out) =>
          match fmul profile lhs_out rhs_out with
          | Some out => Some (HMul lhs_plan rhs_plan (ety out), out)
          | None => None
          end
      | _, _ => None
      end
  | FRe body =>
      match hem profile env body with
      | Some (prior_plan, prior) =>
          match fre profile prior with
          | Some out => Some (HRe prior_plan (ety out), out)
          | None => None
          end
      | None => None
      end
  end.

Definition lower (profile : fprofile) (env : fenv) (term : ftm) : option htm :=
  match fcheck profile env term with
  | Some _ =>
      match hem profile env term with
      | Some (plan, _) => Some plan
      | None => None
      end
  | None => None
  end.

Lemma enc_eqb_refl : forall typ, enc_eqb typ typ = true.
Proof.
  intros [key rem]. unfold enc_eqb. simpl.
  rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

Lemma ftrim_ht : forall profile rem prior out,
  ftrim profile rem prior = Some out ->
  ht_trim profile rem (ety prior) = Some (ety out).
Proof.
  intros profile rem prior out run.
  unfold ftrim in run. unfold ht_trim.
  destruct (Nat.leb rem (erem (ety prior))); try discriminate.
  destruct (cfg_find (ekey (ety prior)) profile); inversion run.
  reflexivity.
Qed.

Lemma fadd_ht : forall profile left right out,
  fadd profile left right = Some out ->
  ht_add profile (ety left) (ety right) = Some (ety out).
Proof.
  intros profile left right out run.
  unfold fadd in run. unfold ht_add.
  destruct (enc_eqb (ety left) (ety right)) eqn:same; try discriminate.
  destruct (cfg_find (ekey (ety left)) profile) eqn:cfg; try discriminate.
  destruct (sum3 (fsteps left) (fsteps right) 1); try discriminate.
  destruct (sum3 (fwork left) (fwork right) (cadd f)); inversion run.
  reflexivity.
Qed.

Lemma fmul_ht : forall profile left right out,
  fmul profile left right = Some out ->
  ht_mul profile (ety left) (ety right) = Some (ety out).
Proof.
  intros profile left right out run.
  unfold fmul in run. unfold ht_mul.
  destruct (enc_eqb (ety left) (ety right)) eqn:same; try discriminate.
  destruct (erem (ety left)) as [|rem] eqn:depth; try discriminate.
  destruct (cfg_find (ekey (ety left)) profile) eqn:cfg; try discriminate.
  destruct (sum3 (fsteps left) (fsteps right) 1); try discriminate.
  destruct (sum3 (fwork left) (fwork right) (cmul f)); inversion run.
  reflexivity.
Qed.

Lemma fre_ht : forall profile prior out,
  fre profile prior = Some out ->
  ht_re profile (ety prior) = Some (ety out).
Proof.
  intros profile prior out run.
  unfold fre in run. unfold ht_re.
  destruct (Nat.eqb (erem (ety prior)) 0) eqn:depth; try discriminate.
  destruct (cfg_find (ekey (ety prior)) profile) eqn:cfg; try discriminate.
  destruct (sum2 (fsteps prior) 1); try discriminate.
  destruct (sum2 (fwork prior) (cre f)); inversion run.
  reflexivity.
Qed.

Theorem hem_sound : forall profile env term plan out,
  hem profile env term = Some (plan, out) ->
  frun profile env term = Some out.
Proof.
  intros profile env term.
  induction term as [name | rem body IH | lhs IHl rhs IHr
    | lhs IHl rhs IHr | body IH]; intros plan out lowered; simpl in lowered.
  - simpl.
    destruct (env_find name env) as [typ |]; try discriminate.
    destruct (cfg_find (ekey typ) profile); try discriminate.
    destruct (legal_b profile typ); inversion lowered. reflexivity.
  - destruct (hem profile env body) as [[prior_plan prior] |] eqn:prior_run;
      try discriminate.
    destruct (ftrim profile rem prior) eqn:step; inversion lowered; subst.
    simpl. rewrite (IH _ _ eq_refl), step. reflexivity.
  - destruct (hem profile env lhs) as [[left_plan left_out] |] eqn:left_run;
      try discriminate.
    destruct (hem profile env rhs) as [[right_plan right_out] |] eqn:right_run;
      try discriminate.
    destruct (fadd profile left_out right_out) eqn:step; inversion lowered; subst.
    simpl. rewrite (IHl _ _ eq_refl), (IHr _ _ eq_refl), step. reflexivity.
  - destruct (hem profile env lhs) as [[left_plan left_out] |] eqn:left_run;
      try discriminate.
    destruct (hem profile env rhs) as [[right_plan right_out] |] eqn:right_run;
      try discriminate.
    destruct (fmul profile left_out right_out) eqn:step; inversion lowered; subst.
    simpl. rewrite (IHl _ _ eq_refl), (IHr _ _ eq_refl), step. reflexivity.
  - destruct (hem profile env body) as [[prior_plan prior] |] eqn:prior_run;
      try discriminate.
    destruct (fre profile prior) eqn:step; inversion lowered; subst.
    simpl. rewrite (IH _ _ eq_refl), step. reflexivity.
Qed.

Theorem hem_complete : forall profile env term out,
  frun profile env term = Some out ->
  exists plan, hem profile env term = Some (plan, out).
Proof.
  intros profile env term.
  induction term as [name | rem body IH | lhs IHl rhs IHr
    | lhs IHl rhs IHr | body IH]; intros out run; simpl in run.
  - exists (HArg name (ety out)). simpl. rewrite run. reflexivity.
  - destruct (frun profile env body) as [prior |] eqn:prior_run; try discriminate.
    destruct (ftrim profile rem prior) as [next |] eqn:step; try discriminate.
    inversion run; subst.
    destruct (IH prior eq_refl) as [prior_plan lowered].
    exists (HTrim rem prior_plan (ety out)). simpl.
    rewrite lowered, step. reflexivity.
  - destruct (frun profile env lhs) as [left_out |] eqn:left_run;
      try discriminate.
    destruct (frun profile env rhs) as [right_out |] eqn:right_run;
      try discriminate.
    destruct (fadd profile left_out right_out) as [next |] eqn:step;
      try discriminate.
    inversion run; subst.
    destruct (IHl left_out eq_refl) as [left_plan left_lower].
    destruct (IHr right_out eq_refl) as [right_plan right_lower].
    exists (HAdd left_plan right_plan (ety out)). simpl.
    rewrite left_lower, right_lower, step. reflexivity.
  - destruct (frun profile env lhs) as [left_out |] eqn:left_run;
      try discriminate.
    destruct (frun profile env rhs) as [right_out |] eqn:right_run;
      try discriminate.
    destruct (fmul profile left_out right_out) as [next |] eqn:step;
      try discriminate.
    inversion run; subst.
    destruct (IHl left_out eq_refl) as [left_plan left_lower].
    destruct (IHr right_out eq_refl) as [right_plan right_lower].
    exists (HMul left_plan right_plan (ety out)). simpl.
    rewrite left_lower, right_lower, step. reflexivity.
  - destruct (frun profile env body) as [prior |] eqn:prior_run; try discriminate.
    destruct (fre profile prior) as [next |] eqn:step; try discriminate.
    inversion run; subst.
    destruct (IH prior eq_refl) as [prior_plan lowered].
    exists (HRe prior_plan (ety out)). simpl.
    rewrite lowered, step. reflexivity.
Qed.

Theorem hem_type : forall profile env term plan out,
  hem profile env term = Some (plan, out) -> hty plan = ety out.
Proof.
  intros profile env term.
  induction term as [name | rem body IH | lhs IHl rhs IHr
    | lhs IHl rhs IHr | body IH]; intros plan out lowered; simpl in lowered.
  - destruct (env_find name env) as [typ |]; try discriminate.
    destruct (cfg_find (ekey typ) profile); try discriminate.
    destruct (legal_b profile typ); inversion lowered; subst. reflexivity.
  - destruct (hem profile env body) as [[prior_plan prior] |]; try discriminate.
    destruct (ftrim profile rem prior); inversion lowered; subst. reflexivity.
  - destruct (hem profile env lhs) as [[left_plan left_out] |]; try discriminate.
    destruct (hem profile env rhs) as [[right_plan right_out] |]; try discriminate.
    destruct (fadd profile left_out right_out); inversion lowered; subst. reflexivity.
  - destruct (hem profile env lhs) as [[left_plan left_out] |]; try discriminate.
    destruct (hem profile env rhs) as [[right_plan right_out] |]; try discriminate.
    destruct (fmul profile left_out right_out); inversion lowered; subst. reflexivity.
  - destruct (hem profile env body) as [[prior_plan prior] |]; try discriminate.
    destruct (fre profile prior); inversion lowered; subst. reflexivity.
Qed.

Theorem hem_erase : forall profile env term plan out,
  hem profile env term = Some (plan, out) -> herase plan = term.
Proof.
  intros profile env term.
  induction term as [name | rem body IH | lhs IHl rhs IHr
    | lhs IHl rhs IHr | body IH]; intros plan out lowered; simpl in lowered.
  - destruct (env_find name env) as [typ |]; try discriminate.
    destruct (cfg_find (ekey typ) profile); try discriminate.
    destruct (legal_b profile typ); inversion lowered; subst. reflexivity.
  - destruct (hem profile env body) as [[prior_plan prior] |] eqn:prior_run;
      try discriminate.
    destruct (ftrim profile rem prior); inversion lowered; subst. simpl.
    rewrite (IH _ _ eq_refl). reflexivity.
  - destruct (hem profile env lhs) as [[left_plan left_out] |] eqn:left_run;
      try discriminate.
    destruct (hem profile env rhs) as [[right_plan right_out] |] eqn:right_run;
      try discriminate.
    destruct (fadd profile left_out right_out); inversion lowered; subst. simpl.
    rewrite (IHl _ _ eq_refl), (IHr _ _ eq_refl). reflexivity.
  - destruct (hem profile env lhs) as [[left_plan left_out] |] eqn:left_run;
      try discriminate.
    destruct (hem profile env rhs) as [[right_plan right_out] |] eqn:right_run;
      try discriminate.
    destruct (fmul profile left_out right_out); inversion lowered; subst. simpl.
    rewrite (IHl _ _ eq_refl), (IHr _ _ eq_refl). reflexivity.
  - destruct (hem profile env body) as [[prior_plan prior] |] eqn:prior_run;
      try discriminate.
    destruct (fre profile prior); inversion lowered; subst. simpl.
    rewrite (IH _ _ eq_refl). reflexivity.
Qed.

Theorem hem_valid : forall profile env term plan out,
  hem profile env term = Some (plan, out) ->
  hval profile env plan = Some (ety out).
Proof.
  intros profile env term.
  induction term as [name | rem body IH | lhs IHl rhs IHr
    | lhs IHl rhs IHr | body IH]; intros plan out lowered; simpl in lowered.
  - simpl.
    destruct (env_find name env) as [typ |] eqn:found; try discriminate.
    destruct (cfg_find (ekey typ) profile); try discriminate.
    destruct (legal_b profile typ); inversion lowered; subst.
    simpl. rewrite found, enc_eqb_refl. reflexivity.
  - destruct (hem profile env body) as [[prior_plan prior] |] eqn:prior_run;
      try discriminate.
    destruct (ftrim profile rem prior) as [next |] eqn:step; try discriminate.
    inversion lowered; subst. simpl.
    rewrite (IH _ _ eq_refl), (ftrim_ht _ _ _ _ step), enc_eqb_refl.
    reflexivity.
  - destruct (hem profile env lhs) as [[left_plan left_out] |] eqn:left_run;
      try discriminate.
    destruct (hem profile env rhs) as [[right_plan right_out] |] eqn:right_run;
      try discriminate.
    destruct (fadd profile left_out right_out) as [next |] eqn:step;
      try discriminate.
    inversion lowered; subst. simpl.
    rewrite (IHl _ _ eq_refl), (IHr _ _ eq_refl),
      (fadd_ht _ _ _ _ step), enc_eqb_refl.
    reflexivity.
  - destruct (hem profile env lhs) as [[left_plan left_out] |] eqn:left_run;
      try discriminate.
    destruct (hem profile env rhs) as [[right_plan right_out] |] eqn:right_run;
      try discriminate.
    destruct (fmul profile left_out right_out) as [next |] eqn:step;
      try discriminate.
    inversion lowered; subst. simpl.
    rewrite (IHl _ _ eq_refl), (IHr _ _ eq_refl),
      (fmul_ht _ _ _ _ step), enc_eqb_refl.
    reflexivity.
  - destruct (hem profile env body) as [[prior_plan prior] |] eqn:prior_run;
      try discriminate.
    destruct (fre profile prior) as [next |] eqn:step; try discriminate.
    inversion lowered; subst. simpl.
    rewrite (IH _ _ eq_refl), (fre_ht _ _ _ step), enc_eqb_refl.
    reflexivity.
Qed.

Theorem lower_sound : forall profile env term plan,
  lower profile env term = Some plan ->
  exists out,
    fcheck profile env term = Some out /\
    hty plan = ety out /\
    herase plan = term /\
    hval profile env plan = Some (ety out).
Proof.
  intros profile env term plan lowered.
  unfold lower in lowered.
  destruct (fcheck profile env term) as [out |] eqn:checked; try discriminate.
  destruct (hem profile env term) as [[made raw] |] eqn:emitted;
    try discriminate.
  inversion lowered; subst.
  pose proof (hem_sound _ _ _ _ _ emitted) as raw_run.
  destruct (fcheck_sound _ _ _ _ checked) as [_ [_ [_ checked_run]]].
  pose proof (frun_complete _ _ _ _ checked_run) as info_run.
  rewrite raw_run in info_run. inversion info_run; subst.
  exists out. split.
  - reflexivity.
  - split.
    + eapply hem_type. exact emitted.
    + split.
      * eapply hem_erase. exact emitted.
      * eapply hem_valid. exact emitted.
Qed.

Theorem lower_complete : forall profile env term out,
  fcheck profile env term = Some out ->
  exists plan,
    lower profile env term = Some plan /\ hty plan = ety out.
Proof.
  intros profile env term out checked.
  destruct (fcheck_sound _ _ _ _ checked) as [_ [_ [_ run_rel]]].
  pose proof (frun_complete _ _ _ _ run_rel) as run.
  destruct (hem_complete _ _ _ _ run) as [plan emitted].
  exists plan. split.
  - unfold lower. rewrite checked, emitted. reflexivity.
  - eapply hem_type. exact emitted.
Qed.

Corollary lower_erase : forall profile env term plan,
  lower profile env term = Some plan -> herase plan = term.
Proof.
  intros profile env term plan lowered.
  destruct (lower_sound _ _ _ _ lowered) as [out [_ [_ [same _]]]].
  exact same.
Qed.

Corollary lower_valid : forall profile env term plan,
  lower profile env term = Some plan ->
  hval profile env plan = Some (hty plan).
Proof.
  intros profile env term plan lowered.
  destruct (lower_sound _ _ _ _ lowered) as [out [_ [same [_ valid]]]].
  rewrite same. exact valid.
Qed.

Theorem lower_unique : forall profile env term left right,
  lower profile env term = Some left ->
  lower profile env term = Some right -> left = right.
Proof.
  intros profile env term left right lhs rhs.
  rewrite lhs in rhs. inversion rhs. reflexivity.
Qed.