(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Lim.
Require Import Fhe.

Import ListNotations.

Record hadm : Type := Hadm {
  hid : nat;
  hmax : nat;
  hout : nat;
  hslot_max : nat;
  hquery_max : nat;
  halpha : nat;
  hrow : nat
}.

Inductive hproof : Type := Hfield.

Record hprof : Type := Hprof {
  hrounds : nat;
  hsound : nat;
  hcommits : nat;
  hopens : nat;
  htrace : nat;
  hcbytes : nat;
  hobytes : nat;
  htbytes : nat;
  htotal : nat
}.

Record hcert : Type := Hcert {
  hproof_id : hproof;
  hbits : nat;
  htraces : nat;
  htags : nat;
  hbytes : nat;
  hproof_plan : hprof
}.

Record hshape : Type := Hshape {
  hterms : nat;
  hslots : nat;
  hquery : nat;
  htag_count : nat
}.

Definition henv := list (nat * hshape).

Record hinfo : Type := Hinfo {
  hstate : hshape;
  hpeak : nat;
  hpeak_tags : nat;
  hresets : nat
}.

Definition hdiv_up (value unit : nat) : nat :=
  (value + unit - 1) / unit.

Definition hunit_bytes (units : nat) : nat := units * 32 + 128.

Definition hplan (bits : nat) : hprof :=
  let rounds := hdiv_up (bits * 1000) 584 in
  let sound := rounds * 584 / 1000 in
  let commits := rounds * 3 in
  let opens := rounds in
  let trace := commits + opens in
  let cbytes := hunit_bytes commits in
  let obytes := hunit_bytes opens in
  let tbytes := hunit_bytes trace in
  Hprof rounds sound commits opens trace cbytes obytes tbytes
    (cbytes + obytes + tbytes).

Definition prod : hadm := Hadm 1 32 4 8 64 8 8.
Definition prod_cert : hcert :=
  Hcert Hfield 128 1024 64 1048576 (hplan 128).

Definition posb (value : nat) : bool := negb (Nat.eqb value 0).

Definition hadm_b (adm : hadm) : bool :=
  ffit (hid adm)
    && ffit (hmax adm) && posb (hmax adm)
    && ffit (hout adm) && posb (hout adm)
    && Nat.leb (hout adm) (hmax adm)
    && ffit (hslot_max adm) && posb (hslot_max adm)
    && ffit (hquery_max adm) && posb (hquery_max adm)
    && ffit (halpha adm) && posb (halpha adm)
    && ffit (hrow adm) && posb (hrow adm).

Definition hprof_b (bits : nat) (prof : hprof) : bool :=
  let expected := hplan bits in
  Nat.eqb (hrounds prof) (hrounds expected)
    && Nat.eqb (hsound prof) (hsound expected)
    && Nat.eqb (hcommits prof) (hcommits expected)
    && Nat.eqb (hopens prof) (hopens expected)
    && Nat.eqb (htrace prof) (htrace expected)
    && Nat.eqb (hcbytes prof) (hcbytes expected)
    && Nat.eqb (hobytes prof) (hobytes expected)
    && Nat.eqb (htbytes prof) (htbytes expected)
    && Nat.eqb (htotal prof) (htotal expected).

Definition hcert_b (cert : hcert) : bool :=
  Nat.leb 128 (hbits cert)
    && posb (htraces cert)
    && posb (htags cert)
    && posb (hbytes cert)
    && hprof_b (hbits cert) (hproof_plan cert)
    && Nat.leb (hbits cert) (hsound (hproof_plan cert))
    && Nat.leb (htrace (hproof_plan cert)) (htraces cert)
    && Nat.leb (htotal (hproof_plan cert)) (hbytes cert).

Definition hmake (terms slots query : nat) : hshape :=
  Hshape terms slots query (terms * slots).

Definition hshape_b (adm : hadm) (shape : hshape) : bool :=
  ffit (htag_count shape)
    && ffit (hterms shape) && posb (hterms shape)
    && Nat.leb (hterms shape) (hmax adm)
    && ffit (hslots shape) && posb (hslots shape)
    && Nat.leb (hslots shape) (hslot_max adm)
    && ffit (hquery shape)
    && Nat.ltb (hquery shape) (hquery_max adm)
    && Nat.eqb (htag_count shape) (hterms shape * hslots shape).

Fixpoint hfind (name : nat) (env : henv) : option hshape :=
  match env with
  | [] => None
  | (id, shape) :: rest =>
      if Nat.eqb name id then Some shape else hfind name rest
  end.

Fixpoint hhas (name : nat) (env : henv) : bool :=
  match env with
  | [] => false
  | (id, _) :: rest => Nat.eqb name id || hhas name rest
  end.

Fixpoint huniq (env : henv) : bool :=
  match env with
  | [] => true
  | (name, _) :: rest => negb (hhas name rest) && huniq rest
  end.

Fixpoint hvals_b (adm : hadm) (env : henv) : bool :=
  match env with
  | [] => true
  | (_, shape) :: rest => hshape_b adm shape && hvals_b adm rest
  end.

Definition henv_b (adm : hadm) (env : henv) : bool :=
  Nat.leb (length env) fcount_max && huniq env && hvals_b adm env.

Definition hmax2 (left right : nat) : nat :=
  if Nat.leb left right then right else left.

Definition haddn (left right : nat) : option nat :=
  let value := left + right in
  if ffit value then Some value else None.

Definition hmuln (left right : nat) : option nat :=
  let value := left * right in
  if ffit value then Some value else None.

Definition hadd (adm : hadm) (left right : hinfo) : option hinfo :=
  if Nat.eqb (hslots (hstate left)) (hslots (hstate right)) then
    match haddn (hterms (hstate left)) (hterms (hstate right)),
        haddn (hresets left) (hresets right) with
    | Some terms, Some resets =>
        if Nat.leb terms (hmax adm) then
          let query := hmax2 (hquery (hstate left)) (hquery (hstate right)) in
          let shape := hmake terms (hslots (hstate left)) query in
          Some (Hinfo shape
            (hmax2 terms (hmax2 (hpeak left) (hpeak right)))
            (hmax2 (htag_count shape)
              (hmax2 (hpeak_tags left) (hpeak_tags right))) resets)
        else None
    | _, _ => None
    end
  else None.

Definition hmul (adm : hadm) (left right : hinfo) : option hinfo :=
  if Nat.eqb (hslots (hstate left)) (hslots (hstate right)) then
    match hmuln (hterms (hstate left)) (hterms (hstate right)),
        haddn (hresets left) (hresets right) with
    | Some terms, Some resets =>
        if Nat.leb terms (hmax adm) then
          let query := hmax2 (hquery (hstate left)) (hquery (hstate right)) in
          let shape := hmake terms (hslots (hstate left)) query in
          Some (Hinfo shape
            (hmax2 terms (hmax2 (hpeak left) (hpeak right)))
            (hmax2 (htag_count shape)
              (hmax2 (hpeak_tags left) (hpeak_tags right))) resets)
        else None
    | _, _ => None
    end
  else None.

Definition hre (adm : hadm) (prior : hinfo) : option hinfo :=
  match haddn (hquery (hstate prior)) 1, haddn (hresets prior) 1 with
  | Some query, Some resets =>
      if Nat.ltb query (hquery_max adm) then
        let shape := hmake (hout adm) (hslots (hstate prior)) query in
        Some (Hinfo shape (hmax2 (hpeak prior) (hout adm))
          (hmax2 (hpeak_tags prior) (htag_count shape)) resets)
      else None
  | _, _ => None
  end.

Fixpoint hrun (adm : hadm) (env : henv) (term : ftm) : option hinfo :=
  match term with
  | FVar name =>
      match hfind name env with
      | Some shape => Some (Hinfo shape (hterms shape) (htag_count shape) 0)
      | None => None
      end
  | FTrim _ body => hrun adm env body
  | FAdd lhs rhs =>
      match hrun adm env lhs, hrun adm env rhs with
      | Some lout, Some rout => hadd adm lout rout
      | _, _ => None
      end
  | FMul lhs rhs =>
      match hrun adm env lhs, hrun adm env rhs with
      | Some lout, Some rout => hmul adm lout rout
      | _, _ => None
      end
  | FRe body =>
      match hrun adm env body with
      | Some prior => hre adm prior
      | None => None
      end
  end.

Definition hcheck (adm : hadm) (cert : hcert) (env : henv) (term : ftm)
    : option hinfo :=
  if hadm_b adm then
    if hcert_b cert then
      if henv_b adm env then
        if ftm_b term then
          match hrun adm env term with
          | Some out =>
              if hshape_b adm (hstate out) then
                if Nat.leb (htag_count (hstate out)) (htags cert) then
                  Some out
                else None
              else None
          | None => None
          end
        else None
      else None
    else None
  else None.

Inductive hrunR (adm : hadm) (env : henv) : ftm -> hinfo -> Prop :=
| HRVar : forall name shape,
    hfind name env = Some shape ->
    hrunR adm env (FVar name)
      (Hinfo shape (hterms shape) (htag_count shape) 0)
| HRTrim : forall rem body out,
    hrunR adm env body out ->
    hrunR adm env (FTrim rem body) out
| HRAdd : forall left right lout rout out,
    hrunR adm env left lout ->
    hrunR adm env right rout ->
    hadd adm lout rout = Some out ->
    hrunR adm env (FAdd left right) out
| HRMul : forall left right lout rout out,
    hrunR adm env left lout ->
    hrunR adm env right rout ->
    hmul adm lout rout = Some out ->
    hrunR adm env (FMul left right) out
| HRRe : forall body prior out,
    hrunR adm env body prior ->
    hre adm prior = Some out ->
    hrunR adm env (FRe body) out.

Theorem hrun_sound : forall adm env term out,
  hrun adm env term = Some out -> hrunR adm env term out.
Proof.
  intros adm env term.
  induction term as [name | rem body IH | left IHl right IHr
    | left IHl right IHr | body IH]; intros out H; simpl in H.
  - destruct (hfind name env) as [shape |] eqn:Hfind; inversion H; subst.
    constructor. exact Hfind.
  - constructor. eapply IH. exact H.
  - destruct (hrun adm env left) as [lout |] eqn:Hl; try discriminate.
    destruct (hrun adm env right) as [rout |] eqn:Hr; try discriminate.
    eapply HRAdd; eauto.
  - destruct (hrun adm env left) as [lout |] eqn:Hl; try discriminate.
    destruct (hrun adm env right) as [rout |] eqn:Hr; try discriminate.
    eapply HRMul; eauto.
  - destruct (hrun adm env body) as [prior |] eqn:Hbody; try discriminate.
    eapply HRRe; eauto.
Qed.

Theorem hrun_complete : forall adm env term out,
  hrunR adm env term out -> hrun adm env term = Some out.
Proof.
  intros adm env term out H.
  induction H; simpl.
  - rewrite H. reflexivity.
  - exact IHhrunR.
  - rewrite IHhrunR1, IHhrunR2, H1. reflexivity.
  - rewrite IHhrunR1, IHhrunR2, H1. reflexivity.
  - rewrite IHhrunR, H0. reflexivity.
Qed.

Theorem hrun_unique : forall adm env term left right,
  hrunR adm env term left ->
  hrunR adm env term right ->
  left = right.
Proof.
  intros adm env term left right Hl Hr.
  pose proof (hrun_complete _ _ _ _ Hl) as El.
  pose proof (hrun_complete _ _ _ _ Hr) as Er.
  rewrite El in Er. inversion Er. reflexivity.
Qed.

Theorem hadd_exact : forall adm left right out,
  hadd adm left right = Some out ->
  hterms (hstate out) = hterms (hstate left) + hterms (hstate right) /\
  hslots (hstate out) = hslots (hstate left) /\
  hquery (hstate out) = hmax2 (hquery (hstate left)) (hquery (hstate right)) /\
  htag_count (hstate out) =
    (hterms (hstate left) + hterms (hstate right)) * hslots (hstate left) /\
  hpeak_tags out = hmax2 (htag_count (hstate out))
    (hmax2 (hpeak_tags left) (hpeak_tags right)) /\
  hresets out = hresets left + hresets right.
Proof.
  intros adm left right out H. unfold hadd in H.
  destruct (Nat.eqb (hslots (hstate left)) (hslots (hstate right)));
    try discriminate.
  destruct (haddn (hterms (hstate left)) (hterms (hstate right)))
    as [terms |] eqn:Ht; try discriminate.
  destruct (haddn (hresets left) (hresets right)) as [resets |] eqn:Hr;
    try discriminate.
  destruct (Nat.leb terms (hmax adm)); inversion H; subst.
  unfold haddn in Ht, Hr.
  destruct (ffit (hterms (hstate left) + hterms (hstate right)));
    inversion Ht; subst.
  destruct (ffit (hresets left + hresets right)); inversion Hr; subst.
  repeat split; reflexivity.
Qed.

Theorem hmul_exact : forall adm left right out,
  hmul adm left right = Some out ->
  hterms (hstate out) = hterms (hstate left) * hterms (hstate right) /\
  hslots (hstate out) = hslots (hstate left) /\
  hquery (hstate out) = hmax2 (hquery (hstate left)) (hquery (hstate right)) /\
  htag_count (hstate out) =
    (hterms (hstate left) * hterms (hstate right)) * hslots (hstate left) /\
  hpeak_tags out = hmax2 (htag_count (hstate out))
    (hmax2 (hpeak_tags left) (hpeak_tags right)) /\
  hresets out = hresets left + hresets right.
Proof.
  intros adm left right out H. unfold hmul in H.
  destruct (Nat.eqb (hslots (hstate left)) (hslots (hstate right)));
    try discriminate.
  destruct (hmuln (hterms (hstate left)) (hterms (hstate right)))
    as [terms |] eqn:Ht; try discriminate.
  destruct (haddn (hresets left) (hresets right)) as [resets |] eqn:Hr;
    try discriminate.
  destruct (Nat.leb terms (hmax adm)); inversion H; subst.
  unfold hmuln in Ht. unfold haddn in Hr.
  destruct (ffit (hterms (hstate left) * hterms (hstate right)));
    inversion Ht; subst.
  destruct (ffit (hresets left + hresets right)); inversion Hr; subst.
  repeat split; reflexivity.
Qed.

Theorem hre_exact : forall adm prior out,
  hre adm prior = Some out ->
  hterms (hstate out) = hout adm /\
  hslots (hstate out) = hslots (hstate prior) /\
  hquery (hstate out) = hquery (hstate prior) + 1 /\
  htag_count (hstate out) = hout adm * hslots (hstate prior) /\
  hpeak_tags out = hmax2 (hpeak_tags prior) (htag_count (hstate out)) /\
  hresets out = hresets prior + 1.
Proof.
  intros adm prior out H. unfold hre in H.
  destruct (haddn (hquery (hstate prior)) 1) as [query |] eqn:Hq;
    try discriminate.
  destruct (haddn (hresets prior) 1) as [resets |] eqn:Hr;
    try discriminate.
  destruct (Nat.ltb query (hquery_max adm)); inversion H; subst.
  unfold haddn in Hq, Hr.
  destruct (ffit (hquery (hstate prior) + 1)); inversion Hq; subst.
  destruct (ffit (hresets prior + 1)); inversion Hr; subst.
  repeat split; reflexivity.
Qed.

Theorem hshape_tags : forall adm shape,
  hshape_b adm shape = true ->
  htag_count shape = hterms shape * hslots shape.
Proof.
  intros adm shape H. unfold hshape_b in H.
  apply andb_true_iff in H as [_ Htags].
  now apply Nat.eqb_eq.
Qed.

Theorem hcheck_sound : forall adm cert env term out,
  hcheck adm cert env term = Some out ->
  hadm_b adm = true /\
  hcert_b cert = true /\
  henv_b adm env = true /\
  ftm_b term = true /\
  hrunR adm env term out /\
  hshape_b adm (hstate out) = true /\
  Nat.leb (htag_count (hstate out)) (htags cert) = true.
Proof.
  intros adm cert env term out H. unfold hcheck in H.
  destruct (hadm_b adm) eqn:Ha; try discriminate.
  destruct (hcert_b cert) eqn:Hc; try discriminate.
  destruct (henv_b adm env) eqn:He; try discriminate.
  destruct (ftm_b term) eqn:Ht; try discriminate.
  destruct (hrun adm env term) as [found |] eqn:Hr; try discriminate.
  destruct (hshape_b adm (hstate found)) eqn:Hs; try discriminate.
  destruct (Nat.leb (htag_count (hstate found)) (htags cert)) eqn:Htags;
    inversion H; subst.
  repeat split; try assumption.
  eapply hrun_sound. exact Hr.
Qed.

Theorem hcheck_complete : forall adm cert env term out,
  hadm_b adm = true ->
  hcert_b cert = true ->
  henv_b adm env = true ->
  ftm_b term = true ->
  hrunR adm env term out ->
  hshape_b adm (hstate out) = true ->
  Nat.leb (htag_count (hstate out)) (htags cert) = true ->
  hcheck adm cert env term = Some out.
Proof.
  intros adm cert env term out Ha Hc He Ht Hr Hs Htags.
  unfold hcheck. rewrite Ha, Hc, He, Ht.
  rewrite (hrun_complete _ _ _ _ Hr), Hs, Htags. reflexivity.
Qed.

Corollary hcheck_tags : forall adm cert env term out,
  hcheck adm cert env term = Some out ->
  htag_count (hstate out) = hterms (hstate out) * hslots (hstate out) /\
  htag_count (hstate out) <= htags cert.
Proof.
  intros adm cert env term out H.
  pose proof (hcheck_sound _ _ _ _ _ H) as
    [_ [_ [_ [_ [_ [Hshape Htags]]]]]].
  split.
  - now apply hshape_tags with adm.
  - now apply Nat.leb_le.
Qed.

Theorem prod_valid : hadm_b prod = true.
Proof. reflexivity. Qed.

Theorem prod_cert_valid : hcert_b prod_cert = true.
Proof. reflexivity. Qed.

Theorem prod_vals :
  hid prod = 1 /\ hmax prod = 32 /\ hout prod = 4 /\
  hslot_max prod = 8 /\ hquery_max prod = 64 /\
  halpha prod = 8 /\ hrow prod = 8.
Proof. repeat split; reflexivity. Qed.

Theorem prod_cert_vals :
  hproof_id prod_cert = Hfield /\ hbits prod_cert = 128 /\
  htraces prod_cert = 1024 /\
  htags prod_cert = 64 /\ hbytes prod_cert = 1048576.
Proof. repeat split; reflexivity. Qed.

Theorem prod_plan_vals :
  hrounds (hproof_plan prod_cert) = 220 /\
  hsound (hproof_plan prod_cert) = 128 /\
  hcommits (hproof_plan prod_cert) = 660 /\
  hopens (hproof_plan prod_cert) = 220 /\
  htrace (hproof_plan prod_cert) = 880 /\
  hcbytes (hproof_plan prod_cert) = 21248 /\
  hobytes (hproof_plan prod_cert) = 7168 /\
  htbytes (hproof_plan prod_cert) = 28288 /\
  htotal (hproof_plan prod_cert) = 56704.
Proof. repeat split; reflexivity. Qed.

Theorem prod_reset_tags :
  hout prod * hslot_max prod <= htags prod_cert.
Proof. apply Nat.leb_le. reflexivity. Qed.