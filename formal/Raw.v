(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.

Require Import Uni.
Require Import Dec.
Require Import DecRel.
Require Import Surf.
Require Import Idx.
Require Import Data.
Require Import Weave.
Require Import Braid.
Require Import Loom.
Require Import Orbit.
Require Import Wake.
Require Import Rift.
Require Import Quant.
Require Import Cmp.

Import ListNotations.

Record rbind : Type := RBind {
  rbname : nat;
  rbmul : mul;
  rbtype : ity
}.

Inductive rtm : Type :=
| RUnit : rtm
| RBool : bool -> rtm
| RInt : Z -> rtm
| RBytes : list nat -> rtm
| RVnil : ity -> rtm
| RVcons : rtm -> rtm -> rtm
| RVar : nat -> rtm
| RLet : rbind -> rtm -> rtm -> rtm
| RIf : rtm -> rtm -> rtm -> rtm
| RPair : rtm -> rtm -> rtm
| RUnpair : rtm -> rbind -> rbind -> rtm -> rtm
| RFst : rtm -> rtm
| RSnd : rtm -> rtm
| RInl : rtm -> ity -> rtm
| RInr : ity -> rtm -> rtm
| RCase : rtm -> rbind -> rtm -> rbind -> rtm -> rtm
| RAct : atom -> rtm -> rtm
| RAdd : rtm -> rtm -> rtm
| RSub : rtm -> rtm -> rtm
| RMul : rtm -> rtm -> rtm
| RDiv : rtm -> rtm -> rtm
| RMod : rtm -> rtm -> rtm
| RNeg : rtm -> rtm
| RAbs : rtm -> rtm
| REq : ity -> rtm -> rtm -> rtm
| RCmp : Cmp.rel -> rtm -> rtm -> rtm
| RCat : rtm -> rtm -> rtm
| RTake : nat -> rtm -> rtm
| RDrop : nat -> rtm -> rtm
| RVcat : rtm -> rtm -> rtm
| RAt : nat -> rtm -> rtm
| RUncons : rtm -> rtm
| RFold : nat -> rtm -> rtm -> rbind -> rbind -> rtm -> rtm
| RFoldI : rtm -> rtm -> rbind -> rbind -> rtm -> rtm
| RQuant : Quant.qmode -> rtm -> rbind -> rtm -> rtm
| RStep : rtm -> rtm -> rtm
| RClose : rtm -> rtm
| RWeave : ix -> ity -> rtm -> rbind -> rtm -> rtm
| RBraid : ix -> ity -> rtm -> rtm -> rbind -> rbind -> rtm -> rtm
| RLoom : ix -> ity -> rbind -> rtm -> rtm
| ROrbit : ix -> rtm -> rbind -> rtm -> rtm
| ROrbitTo : ix -> rtm -> rtm -> rbind -> rtm -> rtm
| RWake : ix -> rtm -> rbind -> rtm -> rtm
| RRift : ix -> ix -> ity -> rtm -> rtm
| RExact : rbind -> ty -> rtm -> rtm
| RReject : rtm.

Definition rclear (used : list nat) (binds : list sbind)
    (terms : list stm) (name : nat) : bool :=
  forallb (fun value => negb (Nat.eqb name value)) used &&
  forallb (fun item => negb (Nat.eqb name (sname item))) binds &&
  forallb (fun term => negb (has name term)) terms.

Fixpoint rseek (fuel index : nat) (used : list nat) (binds : list sbind)
    (terms : list stm) : option nat :=
  match fuel with
  | O => None
  | S rest =>
      let name := did index in
      if rclear used binds terms name then Some name
      else rseek rest (S index) used binds terms
  end.

Definition rpick (used : list nat) (binds : list sbind)
    (terms : list stm) : option nat :=
  rseek Low.pmax 0 used binds terms.

Definition rcmp (relation : Cmp.rel) (left right : stm) : option stm :=
  match rpick [] [] [left; right] with
  | Some left_name =>
      match rpick [left_name] [] [left; right] with
      | Some right_name =>
          match rpick [left_name; right_name] [] [left; right] with
          | Some delta_name =>
              Some (Cmp.term relation left_name right_name delta_name
                left right)
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Lemma rseek_clear : forall fuel index used binds terms name,
  rseek fuel index used binds terms = Some name ->
  rclear used binds terms name = true.
Proof.
  induction fuel as [|fuel IH]; intros index used binds terms name found;
    simpl in found; try discriminate.
  destruct (rclear used binds terms (did index)) eqn:clear.
  - inversion found; subst. exact clear.
  - eapply IH. exact found.
Qed.

Theorem rpick_clear : forall used binds terms name,
  rpick used binds terms = Some name ->
  rclear used binds terms name = true.
Proof.
  intros used binds terms name found.
  unfold rpick in found.
  eapply rseek_clear. exact found.
Qed.

Definition rb_elab (env : ienv) (item : rbind) : option sbind :=
  match yelab env (rbtype item) with
  | Some typ => Some (SBind (rbname item) (rbmul item) typ)
  | None => None
  end.

Definition rexact (env : ienv) (raw : rbind) (typ : ty) : bool :=
  match rb_elab env raw with
  | Some item =>
      ty_eqb (sty item) typ && meqb (smul item) (paym typ)
  | None => false
  end.

Lemma meqb_eq : forall left right,
  meqb left right = true <-> left = right.
Proof.
  intros left right.
  destruct left, right; simpl; split; intros accepted;
    try discriminate; try reflexivity.
Qed.

Theorem rexact_sound : forall env raw typ,
  rexact env raw typ = true ->
  exists item,
    rb_elab env raw = Some item /\
    sty item = typ /\ smul item = paym typ.
Proof.
  intros env raw typ accepted.
  unfold rexact in accepted.
  destruct (rb_elab env raw) as [item |] eqn:made; try discriminate.
  apply andb_true_iff in accepted as [same_type same_mode].
  apply ty_eqb_eq in same_type.
  apply meqb_eq in same_mode.
  exists item.
  repeat split; assumption.
Qed.

Theorem rexact_complete : forall env raw typ item,
  rb_elab env raw = Some item ->
  sty item = typ ->
  smul item = paym typ ->
  rexact env raw typ = true.
Proof.
  intros env raw typ item made same_type same_mode.
  unfold rexact.
  rewrite made, same_type, same_mode, ty_eqb_refl.
  apply meqb_eq.
  reflexivity.
Qed.

Fixpoint relab (env : ienv) (term : rtm) : option stm :=
  match term with
  | RUnit => Some (SK VUnit TUnit)
  | RBool value => Some (SK (VBool value) TBool)
  | RInt value => Some (SK (VInt value) TInt)
  | RBytes value => Some (SBytes value)
  | RVnil raw =>
      match yelab env raw with
      | Some typ => Some (SVnil typ)
      | None => None
      end
  | RVcons value rest =>
      match relab env value, relab env rest with
      | Some out, Some outs => Some (SVcons out outs)
      | _, _ => None
      end
  | RVar name => Some (SVar name)
  | RLet raw value body =>
      match rb_elab env raw, relab env value, relab env body with
      | Some item, Some out, Some rest => Some (SLet item out rest)
      | _, _, _ => None
      end
  | RIf guard yes no =>
      match relab env guard, relab env yes, relab env no with
      | Some g, Some y, Some n => Some (SIf g y n)
      | _, _, _ => None
      end
  | RPair lhs rhs =>
      match relab env lhs, relab env rhs with
      | Some lhs, Some rhs => Some (SPair lhs rhs)
      | _, _ => None
      end
  | RUnpair value raw_left raw_right body =>
      match relab env value, rb_elab env raw_left, rb_elab env raw_right,
          relab env body with
      | Some out, Some lbind, Some rbind, Some rest =>
          Some (SUnpair out lbind rbind rest)
      | _, _, _, _ => None
      end
  | RFst value =>
      match relab env value with Some out => Some (SFst out) | None => None end
  | RSnd value =>
      match relab env value with Some out => Some (SSnd out) | None => None end
  | RInl value raw =>
      match relab env value, yelab env raw with
      | Some out, Some typ => Some (SInl out typ)
      | _, _ => None
      end
  | RInr raw value =>
      match yelab env raw, relab env value with
      | Some typ, Some out => Some (SInr typ out)
      | _, _ => None
      end
  | RCase value raw_left yes raw_right no =>
      match relab env value, rb_elab env raw_left, relab env yes,
          rb_elab env raw_right, relab env no with
      | Some out, Some lbind, Some y, Some rbind, Some n =>
          Some (SCase out lbind y rbind n)
      | _, _, _, _, _ => None
      end
  | RAct atom body =>
      match relab env body with
      | Some out => Some (SAct atom out)
      | None => None
      end
  | RAdd lhs rhs =>
      match relab env lhs, relab env rhs with
      | Some lhs, Some rhs => Some (SAdd lhs rhs)
      | _, _ => None
      end
  | RSub lhs rhs =>
      match relab env lhs, relab env rhs with
      | Some lhs, Some rhs => Some (SSub lhs rhs)
      | _, _ => None
      end
  | RMul lhs rhs =>
      match relab env lhs, relab env rhs with
      | Some lhs, Some rhs => Some (SMul lhs rhs)
      | _, _ => None
      end
  | RDiv lhs rhs =>
      match relab env lhs, relab env rhs with
      | Some lhs, Some rhs => Some (SDiv lhs rhs)
      | _, _ => None
      end
  | RMod lhs rhs =>
      match relab env lhs, relab env rhs with
      | Some lhs, Some rhs => Some (SMod lhs rhs)
      | _, _ => None
      end
  | RNeg value =>
      match relab env value with
      | Some out => Some (SNeg out)
      | None => None
      end
  | RAbs value =>
      match relab env value with
      | Some out => Some (SAbs out)
      | None => None
      end
  | REq raw lhs rhs =>
      match yelab env raw, relab env lhs, relab env rhs with
      | Some typ, Some lhs, Some rhs => Some (SEq typ lhs rhs)
      | _, _, _ => None
      end
  | RCmp relation lhs rhs =>
      match relab env lhs, relab env rhs with
      | Some lout, Some rout => rcmp relation lout rout
      | _, _ => None
      end
  | RCat lhs rhs =>
      match relab env lhs, relab env rhs with
      | Some lhs, Some rhs => Some (SCat lhs rhs)
      | _, _ => None
      end
  | RTake pos value =>
      match relab env value with
      | Some out => Some (STake pos out)
      | None => None
      end
  | RDrop pos value =>
      match relab env value with
      | Some out => Some (SDrop pos out)
      | None => None
      end
  | RVcat lhs rhs =>
      match relab env lhs, relab env rhs with
      | Some lhs, Some rhs => Some (SVcat lhs rhs)
      | _, _ => None
      end
  | RAt pos value =>
      match relab env value with
      | Some out => Some (SAt pos out)
      | None => None
      end
  | RUncons value =>
      match relab env value with
      | Some out => Some (SUncons out)
      | None => None
      end
  | RFold count vector seed raw_item raw_state body =>
      match relab env vector, relab env seed, rb_elab env raw_item,
          rb_elab env raw_state, relab env body with
      | Some values, Some init, Some item, Some state, Some out =>
          Some (SFold count values init item state out)
      | _, _, _, _, _ => None
      end
  | RFoldI _ _ _ _ _ => None
  | RQuant _ _ _ _ => None
  | RStep cap value =>
      match relab env cap, relab env value with
      | Some lhs, Some rhs => Some (SStep lhs rhs)
      | _, _ => None
      end
  | RClose value =>
      match relab env value with
      | Some out => Some (SClose out)
      | None => None
      end
  | RWeave raw_count raw_out source raw_item body =>
      match ieval env raw_count, yelab env raw_out, relab env source,
          rb_elab env raw_item, relab env body with
      | Some count, Some out, Some value, Some item, Some term =>
          match rpick [] [item] [value; term] with
          | Some source_name =>
              Weave.wterm source_name count out value item term
          | None => None
          end
      | _, _, _, _, _ => None
      end
  | RBraid raw_count raw_out raw_left raw_right raw_first raw_second body =>
      match ieval env raw_count, yelab env raw_out, relab env raw_left,
          relab env raw_right, rb_elab env raw_first, rb_elab env raw_second,
          relab env body with
      | Some count, Some out, Some lhs, Some rhs, Some first, Some second,
          Some term =>
          match rpick [] [first; second] [lhs; rhs; term] with
          | Some left_name =>
              match rpick [left_name] [first; second] [lhs; rhs; term] with
              | Some right_name =>
                  Braid.bterm left_name right_name count out lhs rhs
                    first second term
              | None => None
              end
          | None => None
          end
      | _, _, _, _, _, _, _ => None
      end
  | RLoom raw_count raw_out raw_item body =>
      match ieval env raw_count, yelab env raw_out, rb_elab env raw_item,
          relab env body with
      | Some count, Some out, Some item, Some term =>
          Loom.lterm count out item term
      | _, _, _, _ => None
      end
  | ROrbit raw_count seed raw_item body =>
      match ieval env raw_count, relab env seed, rb_elab env raw_item,
          relab env body with
      | Some count, Some value, Some item, Some term =>
          Orbit.oterm count value item term
      | _, _, _, _ => None
      end
  | ROrbitTo raw_count turns seed raw_item body =>
      match ieval env raw_count, relab env turns, relab env seed,
          rb_elab env raw_item, relab env body with
      | Some count, Some rounds, Some value, Some item, Some term =>
          match rpick [] [item] [rounds; value; term] with
          | Some turn_name =>
              match rpick [turn_name] [item] [rounds; value; term] with
              | Some left_name =>
                  match rpick [turn_name; left_name] [item]
                      [rounds; value; term] with
                  | Some right_name =>
                      match rpick [turn_name; left_name; right_name] [item]
                          [rounds; value; term] with
                      | Some delta_name =>
                          Orbit.oterm_to left_name right_name delta_name
                            turn_name count rounds value item term
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | _, _, _, _, _ => None
      end
  | RWake raw_count seed raw_item body =>
      match ieval env raw_count, relab env seed, rb_elab env raw_item,
          relab env body with
      | Some count, Some value, Some item, Some term =>
          match rpick [] [item] [value; term] with
          | Some keep => Wake.kterm keep count value item term
          | None => None
          end
      | _, _, _, _ => None
      end
  | RRift raw_cut raw_rest raw_elem source =>
      match ieval env raw_cut, ieval env raw_rest, yelab env raw_elem,
          relab env source with
      | Some cut, Some rest, Some elem, Some value =>
          Rift.rift_make cut rest elem value
      | _, _, _, _ => None
      end
  | RExact raw typ body =>
      if rexact env raw typ then relab env body else None
  | RReject => None
  end.

Definition tyR (env : ienv) (raw : ity) (out : ty) : Prop :=
  ity_b raw = true /\ ityR env raw out.

Inductive rbR (env : ienv) : rbind -> sbind -> Prop :=
| RBR : forall name mode raw out,
    tyR env raw out ->
    rbR env (RBind name mode raw) (SBind name mode out).

Inductive relabR (env : ienv) : rtm -> stm -> Prop :=
| RRUnit : relabR env RUnit (SK VUnit TUnit)
| RRBool : forall value, relabR env (RBool value) (SK (VBool value) TBool)
| RRInt : forall value, relabR env (RInt value) (SK (VInt value) TInt)
| RRBytes : forall value, relabR env (RBytes value) (SBytes value)
| RRVnil : forall raw typ,
    tyR env raw typ -> relabR env (RVnil raw) (SVnil typ)
| RRVcons : forall value rest out outs,
    relabR env value out ->
    relabR env rest outs ->
    relabR env (RVcons value rest) (SVcons out outs)
| RRVar : forall name, relabR env (RVar name) (SVar name)
| RRLet : forall raw value body item out rest,
    rbR env raw item ->
    relabR env value out ->
    relabR env body rest ->
    relabR env (RLet raw value body) (SLet item out rest)
| RRIf : forall guard yes no g y n,
    relabR env guard g ->
    relabR env yes y ->
    relabR env no n ->
    relabR env (RIf guard yes no) (SIf g y n)
| RRPair : forall left right lhs rhs,
    relabR env left lhs ->
    relabR env right rhs ->
    relabR env (RPair left right) (SPair lhs rhs)
| RRUnpair : forall value raw_left raw_right body out left right rest,
    relabR env value out ->
    rbR env raw_left left ->
    rbR env raw_right right ->
    relabR env body rest ->
    relabR env (RUnpair value raw_left raw_right body)
      (SUnpair out left right rest)
| RRFst : forall value out,
    relabR env value out -> relabR env (RFst value) (SFst out)
| RRSnd : forall value out,
    relabR env value out -> relabR env (RSnd value) (SSnd out)
| RRInl : forall value raw out typ,
    relabR env value out ->
    tyR env raw typ ->
    relabR env (RInl value raw) (SInl out typ)
| RRInr : forall raw value typ out,
    tyR env raw typ ->
    relabR env value out ->
    relabR env (RInr raw value) (SInr typ out)
| RRCase : forall value raw_left yes raw_right no out left y right n,
    relabR env value out ->
    rbR env raw_left left ->
    relabR env yes y ->
    rbR env raw_right right ->
    relabR env no n ->
    relabR env (RCase value raw_left yes raw_right no)
      (SCase out left y right n)
| RRAct : forall atom body out,
    relabR env body out -> relabR env (RAct atom body) (SAct atom out)
| RRAdd : forall left right lhs rhs,
    relabR env left lhs ->
    relabR env right rhs ->
    relabR env (RAdd left right) (SAdd lhs rhs)
| RRSub : forall left right lhs rhs,
    relabR env left lhs ->
    relabR env right rhs ->
    relabR env (RSub left right) (SSub lhs rhs)
| RRMul : forall left right lhs rhs,
    relabR env left lhs ->
    relabR env right rhs ->
    relabR env (RMul left right) (SMul lhs rhs)
| RRDiv : forall left right lhs rhs,
    relabR env left lhs ->
    relabR env right rhs ->
    relabR env (RDiv left right) (SDiv lhs rhs)
| RRMod : forall left right lhs rhs,
    relabR env left lhs ->
    relabR env right rhs ->
    relabR env (RMod left right) (SMod lhs rhs)
| RRNeg : forall value out,
    relabR env value out -> relabR env (RNeg value) (SNeg out)
| RRAbs : forall value out,
    relabR env value out -> relabR env (RAbs value) (SAbs out)
| RREq : forall raw left right typ lhs rhs,
    tyR env raw typ ->
    relabR env left lhs ->
    relabR env right rhs ->
    relabR env (REq raw left right) (SEq typ lhs rhs)
| RRCmp : forall relation left right lhs rhs out,
    relabR env left lhs ->
    relabR env right rhs ->
    rcmp relation lhs rhs = Some out ->
    relabR env (RCmp relation left right) out
| RRCat : forall left right lhs rhs,
    relabR env left lhs ->
    relabR env right rhs ->
    relabR env (RCat left right) (SCat lhs rhs)
| RRTake : forall pos value out,
    relabR env value out -> relabR env (RTake pos value) (STake pos out)
| RRDrop : forall pos value out,
    relabR env value out -> relabR env (RDrop pos value) (SDrop pos out)
| RRVcat : forall left right lhs rhs,
    relabR env left lhs ->
    relabR env right rhs ->
    relabR env (RVcat left right) (SVcat lhs rhs)
| RRAt : forall pos value out,
    relabR env value out -> relabR env (RAt pos value) (SAt pos out)
| RRUncons : forall value out,
    relabR env value out -> relabR env (RUncons value) (SUncons out)
| RRFold : forall count vector seed raw_item raw_state body values init item state out,
    relabR env vector values ->
    relabR env seed init ->
    rbR env raw_item item ->
    rbR env raw_state state ->
    relabR env body out ->
    relabR env (RFold count vector seed raw_item raw_state body)
      (SFold count values init item state out)
| RRStep : forall cap value left right,
    relabR env cap left ->
    relabR env value right ->
    relabR env (RStep cap value) (SStep left right)
| RRClose : forall value out,
    relabR env value out -> relabR env (RClose value) (SClose out)
| RRWeave : forall raw_count raw_out source raw_item body count out value
    item term source_name result,
    ieval env raw_count = Some count ->
    tyR env raw_out out ->
    relabR env source value ->
    rbR env raw_item item ->
    relabR env body term ->
    rpick [] [item] [value; term] = Some source_name ->
    Weave.wterm source_name count out value item term = Some result ->
    relabR env (RWeave raw_count raw_out source raw_item body) result
| RRBraid : forall raw_count raw_out raw_left raw_right raw_first raw_second body
    count out lhs rhs first second term left_name right_name result,
    ieval env raw_count = Some count ->
    tyR env raw_out out ->
    relabR env raw_left lhs ->
    relabR env raw_right rhs ->
    rbR env raw_first first ->
    rbR env raw_second second ->
    relabR env body term ->
    rpick [] [first; second] [lhs; rhs; term] = Some left_name ->
    rpick [left_name] [first; second] [lhs; rhs; term] = Some right_name ->
    Braid.bterm left_name right_name count out lhs rhs first second term =
      Some result ->
    relabR env
      (RBraid raw_count raw_out raw_left raw_right raw_first raw_second body)
      result
| RRLoom : forall raw_count raw_out raw_item body count out item term result,
    ieval env raw_count = Some count ->
    tyR env raw_out out ->
    rbR env raw_item item ->
    relabR env body term ->
    Loom.lterm count out item term = Some result ->
    relabR env (RLoom raw_count raw_out raw_item body) result
| RROrbit : forall raw_count seed raw_item body count value item term result,
    ieval env raw_count = Some count ->
    relabR env seed value ->
    rbR env raw_item item ->
    relabR env body term ->
    Orbit.oterm count value item term = Some result ->
    relabR env (ROrbit raw_count seed raw_item body) result
| RROrbitTo : forall raw_count turns seed raw_item body count rounds value
    item term turn_name left_name right_name delta_name result,
    ieval env raw_count = Some count ->
    relabR env turns rounds ->
    relabR env seed value ->
    rbR env raw_item item ->
    relabR env body term ->
    rpick [] [item] [rounds; value; term] = Some turn_name ->
    rpick [turn_name] [item] [rounds; value; term] = Some left_name ->
    rpick [turn_name; left_name] [item] [rounds; value; term] =
      Some right_name ->
    rpick [turn_name; left_name; right_name] [item]
      [rounds; value; term] = Some delta_name ->
    Orbit.oterm_to left_name right_name delta_name turn_name count rounds
      value item term = Some result ->
    relabR env (ROrbitTo raw_count turns seed raw_item body) result
| RRWake : forall raw_count seed raw_item body count value item term keep result,
    ieval env raw_count = Some count ->
    relabR env seed value ->
    rbR env raw_item item ->
    relabR env body term ->
    rpick [] [item] [value; term] = Some keep ->
    Wake.kterm keep count value item term = Some result ->
    relabR env (RWake raw_count seed raw_item body) result
| RRRift : forall raw_cut raw_rest raw_elem source cut rest elem value result,
    ieval env raw_cut = Some cut ->
    ieval env raw_rest = Some rest ->
    tyR env raw_elem elem ->
    relabR env source value ->
    Rift.rift_make cut rest elem value = Some result ->
    relabR env (RRift raw_cut raw_rest raw_elem source) result
| RRExact : forall raw typ body out,
    rexact env raw typ = true ->
    relabR env body out ->
    relabR env (RExact raw typ body) out.

Theorem rb_elab_sound : forall env raw out,
  rb_elab env raw = Some out ->
  rbname raw = sname out /\ rbmul raw = smul out /\
  ityR env (rbtype raw) (sty out).
Proof.
  intros env [name mode typ] out accepted.
  unfold rb_elab in accepted. simpl in accepted.
  destruct (yelab env typ) as [value |] eqn:done; try discriminate.
  inversion accepted; subst. simpl.
  repeat split; try reflexivity.
  eapply yelab_sound. exact done.
Qed.

Lemma yelab_soundR : forall env raw out,
  yelab env raw = Some out -> tyR env raw out.
Proof.
  intros env raw out accepted.
  unfold tyR.
  eapply yelab_sound.
  exact accepted.
Qed.

Lemma yelab_completeR : forall env raw out,
  tyR env raw out -> yelab env raw = Some out.
Proof.
  intros env raw out [shape typed].
  eapply yelab_complete; eauto.
Qed.

Lemma rb_elab_soundR : forall env raw out,
  rb_elab env raw = Some out -> rbR env raw out.
Proof.
  intros env [name mode raw] out accepted.
  unfold rb_elab in accepted. simpl in accepted.
  destruct (yelab env raw) as [typ |] eqn:typed; try discriminate.
  inversion accepted; subst.
  constructor.
  eapply yelab_soundR.
  exact typed.
Qed.

Lemma rb_elab_completeR : forall env raw out,
  rbR env raw out -> rb_elab env raw = Some out.
Proof.
  intros env raw out related.
  inversion related; subst.
  unfold rb_elab. simpl.
  rewrite (yelab_completeR env raw0 out0 H).
  reflexivity.
Qed.

Local Opaque rcmp Orbit.oterm_to.

Theorem relab_sound : forall env raw out,
  relab env raw = Some out -> relabR env raw out.
Proof.
  intros env raw.
  induction raw; intros out accepted; simpl in accepted.
  all: lazymatch goal with
  | |- relabR ?env (RCmp ?relation ?left ?right) _ =>
      destruct (relab env left) as [lhs |] eqn:left_ok; try discriminate;
      destruct (relab env right) as [rhs |] eqn:right_ok; try discriminate;
      destruct (rcmp relation lhs rhs) as [result |] eqn:result_ok;
        try discriminate;
      inversion accepted; subst;
      eapply RRCmp;
      [eauto 2
      |eauto 2
      |exact result_ok]
  | |- _ => idtac
  end.
  all: lazymatch goal with
  | |- relabR ?env (ROrbitTo ?raw_count ?turns ?seed ?raw_item ?body) _ =>
      destruct (ieval env raw_count) as [count |] eqn:count_ok;
        try discriminate;
      destruct (relab env turns) as [rounds |] eqn:turns_ok;
        try discriminate;
      destruct (relab env seed) as [value |] eqn:seed_ok;
        try discriminate;
      destruct (rb_elab env raw_item) as [item |] eqn:item_ok;
        try discriminate;
      destruct (relab env body) as [term |] eqn:body_ok;
        try discriminate;
      destruct (rpick [] [item] [rounds; value; term]) as [turn_name |]
        eqn:turn_ok; try discriminate;
      destruct (rpick [turn_name] [item] [rounds; value; term])
        as [left_name |] eqn:left_ok; try discriminate;
      destruct (rpick [turn_name; left_name] [item] [rounds; value; term])
        as [right_name |] eqn:right_ok; try discriminate;
      destruct (rpick [turn_name; left_name; right_name] [item]
        [rounds; value; term]) as [delta_name |] eqn:delta_ok;
        try discriminate;
      destruct (Orbit.oterm_to left_name right_name delta_name turn_name count
        rounds value item term) as [result |] eqn:result_ok;
        try discriminate;
      inversion accepted; subst;
      eapply RROrbitTo;
      [exact count_ok
      |eauto 2
      |eauto 2
      |eapply rb_elab_soundR; exact item_ok
      |eauto 2
      |exact turn_ok
      |exact left_ok
      |exact right_ok
      |exact delta_ok
      |exact result_ok]
  | |- _ => idtac
  end.
  all:
    repeat match type of accepted with
    | context [yelab ?ienv ?item] =>
        destruct (yelab ienv item) eqn:?; try discriminate
    | context [rb_elab ?ienv ?item] =>
        destruct (rb_elab ienv item) eqn:?; try discriminate
    | context [relab ?ienv ?item] =>
        destruct (relab ienv item) eqn:?; try discriminate
    | context [ieval ?ienv ?item] =>
        destruct (ieval ienv item) eqn:?; try discriminate
    | context [rpick ?used ?binds ?terms] =>
        destruct (rpick used binds terms) eqn:?; try discriminate
    | context [Weave.wterm ?name ?count ?typ ?source ?item ?body] =>
        destruct (Weave.wterm name count typ source item body) eqn:?;
          try discriminate
    | context [Braid.bterm ?left_name ?right_name ?count ?typ ?left ?right
        ?first ?second ?body] =>
        destruct (Braid.bterm left_name right_name count typ left right
          first second body) eqn:?; try discriminate
    | context [Loom.lterm ?count ?typ ?item ?body] =>
        destruct (Loom.lterm count typ item body) eqn:?; try discriminate
    | context [Orbit.oterm ?count ?seed ?item ?body] =>
        destruct (Orbit.oterm count seed item body) eqn:?; try discriminate
    | context [Wake.kterm ?keep ?count ?seed ?item ?body] =>
        destruct (Wake.kterm keep count seed item body) eqn:?; try discriminate
    | context [Rift.rift_make ?cut ?rest ?elem ?source] =>
        destruct (Rift.rift_make cut rest elem source) eqn:?; try discriminate
    | context [rexact ?ienv ?item ?typ] =>
        destruct (rexact ienv item typ) eqn:?; try discriminate
    end;
    inversion accepted; subst;
    match goal with
    | |- relabR _ RUnit _ => apply RRUnit
    | |- relabR _ (RBool _) _ => apply RRBool
    | |- relabR _ (RInt _) _ => apply RRInt
    | |- relabR _ (RBytes _) _ => apply RRBytes
    | |- relabR _ (RVnil _) _ => eapply RRVnil
    | |- relabR _ (RVcons _ _) _ => eapply RRVcons
    | |- relabR _ (RVar _) _ => apply RRVar
    | |- relabR _ (RLet _ _ _) _ => eapply RRLet
    | |- relabR _ (RIf _ _ _) _ => eapply RRIf
    | |- relabR _ (RPair _ _) _ => eapply RRPair
    | |- relabR _ (RUnpair _ _ _ _) _ => eapply RRUnpair
    | |- relabR _ (RFst _) _ => eapply RRFst
    | |- relabR _ (RSnd _) _ => eapply RRSnd
    | |- relabR _ (RInl _ _) _ => eapply RRInl
    | |- relabR _ (RInr _ _) _ => eapply RRInr
    | |- relabR _ (RCase _ _ _ _ _) _ => eapply RRCase
    | |- relabR _ (RAct _ _) _ => eapply RRAct
    | |- relabR _ (RAdd _ _) _ => eapply RRAdd
    | |- relabR _ (RSub _ _) _ => eapply RRSub
    | |- relabR _ (RMul _ _) _ => eapply RRMul
    | |- relabR _ (RDiv _ _) _ => eapply RRDiv
    | |- relabR _ (RMod _ _) _ => eapply RRMod
    | |- relabR _ (RNeg _) _ => eapply RRNeg
    | |- relabR _ (RAbs _) _ => eapply RRAbs
    | |- relabR _ (REq _ _ _) _ => eapply RREq
    | |- relabR _ (RCat _ _) _ => eapply RRCat
    | |- relabR _ (RTake _ _) _ => eapply RRTake
    | |- relabR _ (RDrop _ _) _ => eapply RRDrop
    | |- relabR _ (RVcat _ _) _ => eapply RRVcat
    | |- relabR _ (RAt _ _) _ => eapply RRAt
    | |- relabR _ (RUncons _) _ => eapply RRUncons
    | |- relabR _ (RFold _ _ _ _ _ _) _ => eapply RRFold
    | |- relabR _ (RStep _ _) _ => eapply RRStep
    | |- relabR _ (RClose _) _ => eapply RRClose
    | |- relabR _ (RWeave _ _ _ _ _) _ => eapply RRWeave
    | |- relabR _ (RBraid _ _ _ _ _ _ _) _ => eapply RRBraid
    | |- relabR _ (RLoom _ _ _ _) _ => eapply RRLoom
    | |- relabR _ (ROrbit _ _ _ _) _ => eapply RROrbit
    | |- relabR _ (RWake _ _ _ _) _ => eapply RRWake
    | |- relabR _ (RRift _ _ _ _) _ => eapply RRRift
    | |- relabR _ (RExact _ _ _) _ => eapply RRExact
    end;
    eauto using yelab_soundR, rb_elab_soundR.
Qed.

Theorem relab_complete : forall env raw out,
  relabR env raw out -> relab env raw = Some out.
Proof.
  intros env raw out related.
  induction related; simpl;
    repeat match goal with
    | H : relab _ _ = Some _ |- _ => rewrite H
    | H : rbR ?ienv ?item ?out |- _ =>
        rewrite (rb_elab_completeR ienv item out H)
    | H : tyR ?ienv ?item ?out |- _ =>
        rewrite (yelab_completeR ienv item out H)
    | H : ieval _ _ = Some _ |- _ => rewrite H
    | H : rpick _ _ _ = Some _ |- _ => rewrite H
    | H : Weave.wterm _ _ _ _ _ _ = Some _ |- _ => rewrite H
    | H : Braid.bterm _ _ _ _ _ _ _ _ _ = Some _ |- _ => rewrite H
    | H : Loom.lterm _ _ _ _ = Some _ |- _ => rewrite H
    | H : Orbit.oterm _ _ _ _ = Some _ |- _ => rewrite H
    | H : Orbit.oterm_to _ _ _ _ _ _ _ _ _ = Some _ |- _ => rewrite H
    | H : rcmp _ _ _ = Some _ |- _ => rewrite H
    | H : Wake.kterm _ _ _ _ _ = Some _ |- _ => rewrite H
    | H : Rift.rift_make _ _ _ _ = Some _ |- _ => rewrite H
    | H : rexact _ _ _ = true |- _ => rewrite H
    end;
    reflexivity.
Qed.

Corollary relab_exact : forall env raw out,
  relab env raw = Some out <-> relabR env raw out.
Proof.
  intros env raw out.
  split.
  - apply relab_sound.
  - apply relab_complete.
Qed.

Theorem relab_unique : forall env raw left right,
  relab env raw = Some left ->
  relab env raw = Some right ->
  left = right.
Proof.
  intros env raw left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Theorem relab_eq_exact : forall env raw left right typ lhs rhs,
  yelab env raw = Some typ ->
  relab env left = Some lhs ->
  relab env right = Some rhs ->
  relab env (REq raw left right) = Some (SEq typ lhs rhs).
Proof.
  intros env raw left right typ lhs rhs type_ok left_ok right_ok.
  simpl. rewrite type_ok, left_ok, right_ok. reflexivity.
Qed.

Theorem relab_vec_empty : forall env raw typ,
  yelab env raw = Some typ ->
  relab env (RVnil raw) = Some (SVnil typ).
Proof.
  intros env raw typ type_ok.
  simpl. rewrite type_ok. reflexivity.
Qed.

Theorem relab_vec_cons : forall env value rest out outs,
  relab env value = Some out ->
  relab env rest = Some outs ->
  relab env (RVcons value rest) = Some (SVcons out outs).
Proof.
  intros env value rest out outs value_ok rest_ok.
  simpl. rewrite value_ok, rest_ok. reflexivity.
Qed.