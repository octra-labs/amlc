(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.

Require Import Fhe.
Require Import Param.
Require Import Hfhe.
Require Import Graph.
Require Import Ent.

Import ListNotations.

Record hset : Type := Hset {
  sid : nat;
  skey : nat;
  sfbits : Z;
  sbasis : Z;
  srows : Z;
  scols : Z;
  shwt : Z;
  sxwt : Z;
  sewt : Z;
  sedges : Z;
  sln : Z;
  slt : Z;
  stn : Z;
  std : Z;
  sprf : Z;
  sadm : hadm;
  scert : hcert
}.

Record hcap : Type := Hcap {
  chbits : Z;
  chwords : Z;
  cperms : Z;
  croots : Z;
  cswords : Z;
  cywords : Z;
  ctwords : Z;
  cewords : Z;
  cevals : Z
}.

Record hlink : Type := Hlink {
  lset : hset;
  lparam : fparam;
  lfhe : finfo;
  lhfhe : hinfo;
  lcap : hcap;
  lgraph : Graph.cfg;
  lent : Ent.eplan
}.

Definition root_b (set : hset) : bool :=
  Z.eqb
    (Z.rem (Z.sub (Z.pow 2 (sfbits set)) 2) (sbasis set)) 0.

Definition zposb (value : Z) : bool := Z.ltb 0 value.

Definition hset_b (set : hset) : bool :=
  ffit (sid set) && posb (sid set)
    && ffit (skey set) && posb (skey set)
    && Nat.eqb (skey set) (hid (sadm set))
    && Z.eqb (sfbits set) 127
    && Z.leb 3 (sbasis set)
    && Z.leb (sbasis set) 65536
    && Nat.eqb (Z.to_nat (sbasis set)) (Ent.ebasis Ent.prod)
    && root_b set
    && zposb (srows set)
    && zposb (scols set)
    && Z.leb 0 (shwt set)
    && Z.leb (shwt set) (srows set)
    && Z.leb 0 (sxwt set)
    && Z.leb (sxwt set) (scols set)
    && Z.leb 0 (sewt set)
    && Z.leb (sewt set) (srows set)
    && zposb (sedges set)
    && zposb (sln set)
    && Z.leb 127 (slt set)
    && zposb (stn set)
    && zposb (std set)
    && Z.leb (stn set) (std set)
    && Z.eqb (sprf set) 4
    && hadm_b (sadm set)
    && hcert_b (scert set)
    && Z.leb (Z.of_nat (htags (scert set))) (sedges set)
    && Z.leb
      (Z.of_nat (hmax (sadm set) * hslot_max (sadm set))) (sedges set)
    && Z.leb
      (Z.of_nat (hout (sadm set) * hslot_max (sadm set)))
      (Z.of_nat (htags (scert set))).

Definition hseal := { set : hset | hset_b set = true }.

Definition hval (sealed : hseal) : hset := proj1_sig sealed.

Definition seal (set : hset) : option hseal :=
  match Bool.bool_dec (hset_b set) true with
  | left valid => Some (exist _ set valid)
  | right _ => None
  end.

Theorem seal_sound : forall set sealed,
  seal set = Some sealed ->
  hval sealed = set /\ hset_b set = true.
Proof.
  intros set sealed H. unfold seal in H.
  destruct (Bool.bool_dec (hset_b set) true) as [valid | invalid].
  - inversion H. subst. split; auto.
  - discriminate.
Qed.

Theorem seal_complete : forall set,
  hset_b set = true -> exists sealed, seal set = Some sealed.
Proof.
  intros set H. unfold seal.
  destruct (Bool.bool_dec (hset_b set) true) as [valid | invalid].
  - exists (exist _ set valid). reflexivity.
  - contradiction.
Qed.

Definition hcatalog := list hseal.

Fixpoint sid_has (id : nat) (sets : hcatalog) : bool :=
  match sets with
  | [] => false
  | sealed :: rest => Nat.eqb id (sid (hval sealed)) || sid_has id rest
  end.

Fixpoint skey_has (key : nat) (sets : hcatalog) : bool :=
  match sets with
  | [] => false
  | sealed :: rest => Nat.eqb key (skey (hval sealed)) || skey_has key rest
  end.

Fixpoint hcatalog_uniq (sets : hcatalog) : bool :=
  match sets with
  | [] => true
  | sealed :: rest =>
      negb (sid_has (sid (hval sealed)) rest)
        && negb (skey_has (skey (hval sealed)) rest)
        && hcatalog_uniq rest
  end.

Definition hcatalog_b (sets : hcatalog) : bool :=
  Nat.leb (length sets) fcount_max
    && hcatalog_uniq sets.

Fixpoint hsel (key : nat) (sets : hcatalog) : option hset :=
  match sets with
  | [] => None
  | sealed :: rest =>
      let set := hval sealed in
      if Nat.eqb key (skey set) then Some set else hsel key rest
  end.

Theorem hsel_in : forall sets key out,
  hsel key sets = Some out ->
  exists sealed, In sealed sets /\ hval sealed = out.
Proof.
  induction sets as [|sealed rest IH]; intros key out H; simpl in H.
  - discriminate.
  - destruct (Nat.eqb key (skey (hval sealed))) eqn:Hkey.
    + inversion H. subst out. exists sealed. split.
      * left. reflexivity.
      * reflexivity.
    + destruct (IH key out H) as [item [Hin Heq]].
      exists item. split.
      * right. exact Hin.
      * exact Heq.
Qed.

Theorem hsel_key : forall sets key out,
  hsel key sets = Some out -> skey out = key.
Proof.
  induction sets as [|sealed rest IH]; intros key out H; simpl in H.
  - discriminate.
  - destruct (Nat.eqb key (skey (hval sealed))) eqn:Hkey.
    + inversion H. subst. apply Nat.eqb_eq in Hkey. symmetry. exact Hkey.
    + eapply IH. exact H.
Qed.

Theorem hsel_complete : forall sets key item,
  In item sets -> skey (hval item) = key ->
  exists out, hsel key sets = Some out.
Proof.
  induction sets as [|sealed rest IH]; intros key item Hin Hkey.
  - inversion Hin.
  - simpl. destruct Hin as [Heq | Hin].
    + subst item. rewrite Hkey, Nat.eqb_refl. eauto.
    + destruct (Nat.eqb key (skey (hval sealed))).
      * eauto.
      * eapply IH; eauto.
Qed.

Lemma skey_has_in : forall sets item,
  In item sets -> skey_has (skey (hval item)) sets = true.
Proof.
  induction sets as [|sealed rest IH]; intros item Hin.
  - inversion Hin.
  - simpl. destruct Hin as [Heq | Hin].
    + subst item. rewrite Nat.eqb_refl. reflexivity.
    + rewrite (IH item Hin). apply Bool.orb_true_r.
Qed.

Theorem hsel_valid : forall sets key out,
  hsel key sets = Some out ->
  hset_b out = true.
Proof.
  induction sets as [|sealed rest IH]; intros key out Hsel.
  - discriminate.
  - cbn [hsel] in Hsel.
    destruct (Nat.eqb key (skey (hval sealed))).
    + inversion Hsel. subst. exact (proj2_sig sealed).
    + eapply IH. exact Hsel.
Qed.

Theorem hsel_unique : forall sets key out item,
  hcatalog_uniq sets = true ->
  hsel key sets = Some out ->
  In item sets ->
  skey (hval item) = key ->
  hval item = out.
Proof.
  induction sets as [|sealed rest IH]; intros key out item Huniq Hsel Hin Hitem.
  - inversion Hin.
  - cbn [hcatalog_uniq] in Huniq.
    cbn [hsel] in Hsel.
    apply andb_true_iff in Huniq as [Hhead Hrest].
    apply andb_true_iff in Hhead as [_ Hfresh].
    destruct (Nat.eqb key (skey (hval sealed))) eqn:Hkey.
    + inversion Hsel. subst out. destruct Hin as [Heq | Hin].
      * subst item. reflexivity.
      * apply Nat.eqb_eq in Hkey.
        pose proof (skey_has_in rest item Hin) as Hhas.
        assert (Heq : skey (hval item) = skey (hval sealed)) by congruence.
        rewrite Heq in Hhas. rewrite Hhas in Hfresh. discriminate.
    + destruct Hin as [Heq | Hin].
      * subst item. rewrite Hitem, Nat.eqb_refl in Hkey. discriminate.
      * eapply IH; eauto.
Qed.

Definition div_up (value unit : Z) : Z :=
  Z.div (Z.sub (Z.add value unit) 1) unit.

Definition words (bits : Z) : Z := div_up bits 64.

Definition caps (set : hset) : hcap :=
  Hcap
    (srows set * scols set)
    (scols set * words (srows set))
    (srows set * 2)
    (sbasis set)
    (words (sln set))
    (words (slt set))
    (words (slt set + 127))
    (sedges set * words (srows set))
    (sedges set * Z.of_nat (hslot_max (sadm set))).

Definition prod_set : hset :=
  Hset 1 1 127%Z 337%Z 8192%Z 16384%Z 192%Z 128%Z 128%Z 1200000%Z
    4096%Z 16384%Z 1%Z 8%Z 4%Z Hfhe.prod prod_cert.

Theorem prod_set_valid : hset_b prod_set = true.
Proof. vm_compute. reflexivity. Qed.

Definition prod_seal : hseal := exist _ prod_set prod_set_valid.

Definition prod_cat : hcatalog := [prod_seal].

Definition gcfg (set : hset) (hout : hinfo) : Graph.cfg :=
  Graph.Cfg (Z.to_nat (sbasis set)) (hslots (hstate hout))
    (Z.to_nat (srows set)) (sedges set).

Definition bind_b (set : hset) (param : fparam) (fout : finfo)
    (hout : hinfo) : bool :=
  Nat.eqb (pkey param) (skey set)
    && (Nat.eqb (ekey (ety fout)) (skey set)
    && (ffit (fpeak fout)
    && (Nat.leb (fpeak fout) (pcap param)
    && (hshape_b (sadm set) (hstate hout)
    && Nat.leb (htag_count (hstate hout)) (htags (scert set)))))).

Definition bind (set : hset) (param : fparam) (fout : finfo)
    (hout : hinfo) : option hlink :=
  if bind_b set param fout hout then
    Some (Hlink set param fout hout (caps set) (gcfg set hout)
      (Ent.build Ent.prod (fpeak fout)))
  else None.

Definition check (set : hset) (catalog : fcatalog) (profile : fprofile)
    (fenv : Fhe.fenv) (henv : Hfhe.henv) (term : ftm) : option hlink :=
  if hset_b set then
    match fcheck profile fenv term with
    | Some fout =>
        match params catalog fout with
        | Some param =>
            match hcheck (sadm set) (scert set) henv term with
            | Some hout => bind set param fout hout
            | None => None
            end
        | None => None
        end
    | None => None
    end
  else None.

Definition check_cat (sets : hcatalog) (catalog : fcatalog)
    (profile : fprofile) (fenv : Fhe.fenv) (henv : Hfhe.henv)
    (term : ftm) : option hlink :=
  if hcatalog_b sets then
    match fcheck profile fenv term with
    | Some fout =>
        match hsel (ekey (ety fout)) sets with
        | Some set =>
            match params catalog fout with
            | Some param =>
                match hcheck (sadm set) (scert set) henv term with
                | Some hout => bind set param fout hout
                | None => None
                end
            | None => None
            end
        | None => None
        end
    | None => None
    end
  else None.

Theorem bind_param_key : forall set param fout hout out,
  bind set param fout hout = Some out ->
  pkey param = skey set.
Proof.
  intros set param fout hout out H. unfold bind in H.
  destruct (bind_b set param fout hout) eqn:Hb; try discriminate.
  inversion H. subst. unfold bind_b in Hb.
  apply andb_true_iff in Hb as [Hb _].
  apply Nat.eqb_eq. exact Hb.
Qed.

Theorem bind_fhe_key : forall set param fout hout out,
  bind set param fout hout = Some out ->
  ekey (ety fout) = skey set.
Proof.
  intros set param fout hout out H. unfold bind in H.
  destruct (bind_b set param fout hout) eqn:Hb; try discriminate.
  inversion H. subst. unfold bind_b in Hb.
  apply andb_true_iff in Hb as [_ Hb].
  apply andb_true_iff in Hb as [Hb _].
  apply Nat.eqb_eq. exact Hb.
Qed.

Theorem bind_room : forall set param fout hout out,
  bind set param fout hout = Some out ->
  fpeak fout <= pcap param.
Proof.
  intros set param fout hout out H. unfold bind in H.
  destruct (bind_b set param fout hout) eqn:Hb; try discriminate.
  inversion H. subst. unfold bind_b in Hb.
  apply andb_true_iff in Hb as [_ Hb].
  apply andb_true_iff in Hb as [_ Hb].
  apply andb_true_iff in Hb as [_ Hb].
  apply andb_true_iff in Hb as [Hb _].
  apply Nat.leb_le. exact Hb.
Qed.

Theorem bind_graph : forall set param fout hout out,
  bind set param fout hout = Some out ->
  lgraph out = gcfg set hout.
Proof.
  intros set param fout hout out H. unfold bind in H.
  destruct (bind_b set param fout hout) eqn:Hb; try discriminate.
  inversion H. reflexivity.
Qed.

Theorem bind_ent : forall set param fout hout out,
  bind set param fout hout = Some out ->
  lent out = Ent.build Ent.prod (fpeak fout).
Proof.
  intros set param fout hout out H. unfold bind in H.
  destruct (bind_b set param fout hout) eqn:Hb; try discriminate.
  inversion H. reflexivity.
Qed.

Theorem check_sound : forall set catalog profile fenv henv term out,
  check set catalog profile fenv henv term = Some out ->
  hset_b set = true /\
  fcheck profile fenv term = Some (lfhe out) /\
  params catalog (lfhe out) = Some (lparam out) /\
  hcheck (sadm set) (scert set) henv term = Some (lhfhe out) /\
  bind set (lparam out) (lfhe out) (lhfhe out) = Some out.
Proof.
  intros set catalog profile fenv henv term out H. unfold check in H.
  destruct (hset_b set) eqn:Hs; try discriminate.
  destruct (fcheck profile fenv term) as [fout |] eqn:Hf; try discriminate.
  destruct (params catalog fout) as [param |] eqn:Hp; try discriminate.
  destruct (hcheck (sadm set) (scert set) henv term) as [hout |] eqn:Hh;
    try discriminate.
  unfold bind in H.
  destruct (bind_b set param fout hout) eqn:Hb; try discriminate.
  inversion H. subst. simpl. repeat split.
  - exact Hp.
  - unfold bind. rewrite Hb. reflexivity.
Qed.

Theorem check_cat_sound : forall sets catalog profile fenv henv term out,
  check_cat sets catalog profile fenv henv term = Some out ->
  hcatalog_b sets = true /\
  hset_b (lset out) = true /\
  fcheck profile fenv term = Some (lfhe out) /\
  hsel (ekey (ety (lfhe out))) sets = Some (lset out) /\
  params catalog (lfhe out) = Some (lparam out) /\
  hcheck (sadm (lset out)) (scert (lset out)) henv term = Some (lhfhe out) /\
  bind (lset out) (lparam out) (lfhe out) (lhfhe out) = Some out.
Proof.
  intros sets catalog profile fenv henv term out H. unfold check_cat in H.
  destruct (hcatalog_b sets) eqn:Hsets; try discriminate.
  destruct (fcheck profile fenv term) as [fout |] eqn:Hf; try discriminate.
  destruct (hsel (ekey (ety fout)) sets) as [set |] eqn:Hs;
    try discriminate.
  pose proof (hsel_valid sets (ekey (ety fout)) set Hs) as Hvalid.
  destruct (params catalog fout) as [param |] eqn:Hp; try discriminate.
  destruct (hcheck (sadm set) (scert set) henv term) as [hout |] eqn:Hh;
    try discriminate.
  unfold bind in H.
  destruct (bind_b set param fout hout) eqn:Hb; try discriminate.
  inversion H. subst. simpl. repeat split; try assumption.
  unfold bind. rewrite Hb. reflexivity.
Qed.

Theorem prod_cat_valid : hcatalog_b prod_cat = true.
Proof. reflexivity. Qed.

Theorem prod_cat_select : hsel 1 prod_cat = Some prod_set.
Proof. reflexivity. Qed.

Theorem prod_root :
  Z.rem (Z.sub (Z.pow 2 127) 2) 337 = Z.zero.
Proof. vm_compute. reflexivity. Qed.

Theorem prod_set_vals :
  sid prod_set = 1 /\ skey prod_set = 1 /\ sfbits prod_set = 127%Z /\
  sbasis prod_set = 337%Z /\ srows prod_set = 8192%Z /\
  scols prod_set = 16384%Z /\ shwt prod_set = 192%Z /\
  sxwt prod_set = 128%Z /\ sewt prod_set = 128%Z /\
  sedges prod_set = 1200000%Z /\ sln prod_set = 4096%Z /\
  slt prod_set = 16384%Z /\ stn prod_set = 1%Z /\ std prod_set = 8%Z /\
  sprf prod_set = 4%Z /\ sadm prod_set = Hfhe.prod /\
  scert prod_set = prod_cert.
Proof. repeat split; reflexivity. Qed.

Theorem prod_cap_vals :
  chbits (caps prod_set) = 134217728%Z /\
  chwords (caps prod_set) = 2097152%Z /\
  cperms (caps prod_set) = 16384%Z /\
  croots (caps prod_set) = 337%Z /\
  cswords (caps prod_set) = 64%Z /\
  cywords (caps prod_set) = 256%Z /\
  ctwords (caps prod_set) = 258%Z /\
  cewords (caps prod_set) = 153600000%Z /\
  cevals (caps prod_set) = 9600000%Z.
Proof. repeat split; reflexivity. Qed.

Theorem prod_graph_vals : forall hout,
  Graph.gbasis (gcfg prod_set hout) = 337 /\
  Graph.gslots (gcfg prod_set hout) = hslots (hstate hout) /\
  Graph.gsigma (gcfg prod_set hout) = 8192 /\
  Graph.gedge_cap (gcfg prod_set hout) = 1200000%Z.
Proof. intros hout. repeat split; reflexivity. Qed.