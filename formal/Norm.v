(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.ZArith.

Require Import Uni.
Require Import Surf.
Require Import Idx.
Require Import Low.
Require Import Quant.
Require Import Data.
Require Import Raw.

Import ListNotations.

Fixpoint sdrop (name : nat) (items : list sbind) : list sbind :=
  match items with
  | [] => []
  | item :: rest =>
      if Nat.eqb name (sname item) then sdrop name rest
      else item :: sdrop name rest
  end.

Definition spush (items : list sbind) (item : sbind) : list sbind :=
  sdrop (sname item) items ++ [item].

Definition vlen (items : list sbind) (term : stm) : option nat :=
  match pview items term with
  | Some (TVec count _, _, _, _) => Some count
  | _ => None
  end.

Theorem vlen_sound : forall items term count,
  vlen items term = Some count ->
  exists elem row cost next binds core gamma,
    pview items term = Some (TVec count elem, row, cost, next) /\
    prog items term = Some (binds, core) /\
    opens [] binds = Some gamma /\
    check gamma core (TVec count elem) row cost next.
Proof.
  intros items term count accepted.
  unfold vlen in accepted.
  destruct (pview items term) as [[[[typ row] cost] next] |] eqn:view;
    try discriminate.
  destruct typ; try discriminate.
  inversion accepted; subst.
  apply pview_sound in view.
  destruct view as [binds [core [gamma [lowered [opened checked]]]]].
  exists typ, row, cost, next, binds, core, gamma.
  repeat split; assumption.
Qed.

Definition qclear (state mark : nat) (source : stm) (item : sbind)
    (body : stm) : bool :=
  negb (Nat.eqb state mark) && clear state source item body
    && clear mark source item body.

Fixpoint qseek (fuel index : nat) (source : stm) (item : sbind)
    (body : stm) : option (nat * nat) :=
  match fuel with
  | O => None
  | S rest =>
      let state := did index in
      let mark := did (S index) in
      if qclear state mark source item body then Some (state, mark)
      else qseek rest (index + 2) source item body
  end.

Definition qpick (source : stm) (item : sbind) (body : stm)
    : option (nat * nat) :=
  qseek (Nat.div pmax 2) 0 source item body.

Definition qrtype (mode : qmode) : ity :=
  match mode with
  | QEvery | QSome => YBool
  | QCount | QSum => YInt
  end.

Definition qrmark (mode : qmode) : ity :=
  match mode with
  | QEvery | QSome | QCount => YBool
  | QSum => YInt
  end.

Definition qrseed (mode : qmode) : rtm :=
  match mode with
  | QEvery => RBool true
  | QSome => RBool false
  | QCount | QSum => RInt 0%Z
  end.

Definition qrbody (state mark : nat) (mode : qmode) (body : rtm) : rtm :=
  let marked := RLet (RBind mark MM (qrmark mode)) body in
  match mode with
  | QEvery => marked (RIf (RVar state) (RVar mark) (RBool false))
  | QSome => marked (RIf (RVar state) (RBool true) (RVar mark))
  | QCount => marked (RIf (RVar mark)
      (RAdd (RVar state) (RInt 1%Z)) (RVar state))
  | QSum => marked (RAdd (RVar state) (RVar mark))
  end.

Definition qrterm (state mark : nat) (mode : qmode) (count : nat)
    (source : rtm) (item : rbind) (body : rtm) : rtm :=
  RFold count source (qrseed mode) item (RBind state MM (qrtype mode))
    (qrbody state mark mode body).

Fixpoint norm (env : ienv) (scope : list sbind) (term : rtm) : option rtm :=
  match term with
  | RUnit => Some RUnit
  | RBool value => Some (RBool value)
  | RInt value => Some (RInt value)
  | RBytes value => Some (RBytes value)
  | RVnil typ => Some (RVnil typ)
  | RVcons value rest =>
      match norm env scope value, norm env scope rest with
      | Some out, Some tail => Some (RVcons out tail)
      | _, _ => None
      end
  | RVar name => Some (RVar name)
  | RLet item value body =>
      match rb_elab env item, norm env scope value with
      | Some bind, Some out =>
          match norm env (spush scope bind) body with
          | Some rest => Some (RLet item out rest)
          | None => None
          end
      | _, _ => None
      end
  | RIf guard yes no =>
      match norm env scope guard, norm env scope yes, norm env scope no with
      | Some g, Some y, Some n => Some (RIf g y n)
      | _, _, _ => None
      end
  | RPair lhs0 rhs0 =>
      match norm env scope lhs0, norm env scope rhs0 with
      | Some lhs, Some rhs => Some (RPair lhs rhs)
      | _, _ => None
      end
  | RUnpair value lhs0 rhs0 body =>
      match norm env scope value, rb_elab env lhs0, rb_elab env rhs0 with
      | Some out, Some lbind, Some rbind =>
          match norm env (spush (spush scope lbind) rbind) body with
          | Some rest => Some (RUnpair out lhs0 rhs0 rest)
          | None => None
          end
      | _, _, _ => None
      end
  | RFst value =>
      match norm env scope value with
      | Some out => Some (RFst out)
      | None => None
      end
  | RSnd value =>
      match norm env scope value with
      | Some out => Some (RSnd out)
      | None => None
      end
  | RInl value typ =>
      match norm env scope value with
      | Some out => Some (RInl out typ)
      | None => None
      end
  | RInr typ value =>
      match norm env scope value with
      | Some out => Some (RInr typ out)
      | None => None
      end
  | RCase value lhs0 yes rhs0 no =>
      match norm env scope value, rb_elab env lhs0, rb_elab env rhs0 with
      | Some out, Some lbind, Some rbind =>
          match norm env (spush scope lbind) yes,
              norm env (spush scope rbind) no with
          | Some lhs, Some rhs => Some (RCase out lhs0 lhs rhs0 rhs)
          | _, _ => None
          end
      | _, _, _ => None
      end
  | RAct atom body =>
      match norm env scope body with
      | Some out => Some (RAct atom out)
      | None => None
      end
  | RAdd lhs0 rhs0 =>
      match norm env scope lhs0, norm env scope rhs0 with
      | Some lhs, Some rhs => Some (RAdd lhs rhs)
      | _, _ => None
      end
  | RSub lhs0 rhs0 =>
      match norm env scope lhs0, norm env scope rhs0 with
      | Some lhs, Some rhs => Some (RSub lhs rhs)
      | _, _ => None
      end
  | RMul lhs0 rhs0 =>
      match norm env scope lhs0, norm env scope rhs0 with
      | Some lhs, Some rhs => Some (RMul lhs rhs)
      | _, _ => None
      end
  | RDiv lhs0 rhs0 =>
      match norm env scope lhs0, norm env scope rhs0 with
      | Some lhs, Some rhs => Some (RDiv lhs rhs)
      | _, _ => None
      end
  | RMod lhs0 rhs0 =>
      match norm env scope lhs0, norm env scope rhs0 with
      | Some lhs, Some rhs => Some (RMod lhs rhs)
      | _, _ => None
      end
  | RNeg value =>
      match norm env scope value with
      | Some out => Some (RNeg out)
      | None => None
      end
  | RAbs value =>
      match norm env scope value with
      | Some out => Some (RAbs out)
      | None => None
      end
  | REq typ lhs0 rhs0 =>
      match norm env scope lhs0, norm env scope rhs0 with
      | Some lhs, Some rhs => Some (REq typ lhs rhs)
      | _, _ => None
      end
  | RCmp relation lhs0 rhs0 =>
      match norm env scope lhs0, norm env scope rhs0 with
      | Some lhs, Some rhs => Some (RCmp relation lhs rhs)
      | _, _ => None
      end
  | RCat lhs0 rhs0 =>
      match norm env scope lhs0, norm env scope rhs0 with
      | Some lhs, Some rhs => Some (RCat lhs rhs)
      | _, _ => None
      end
  | RTake pos value =>
      match norm env scope value with
      | Some out => Some (RTake pos out)
      | None => None
      end
  | RDrop pos value =>
      match norm env scope value with
      | Some out => Some (RDrop pos out)
      | None => None
      end
  | RVcat lhs0 rhs0 =>
      match norm env scope lhs0, norm env scope rhs0 with
      | Some lhs, Some rhs => Some (RVcat lhs rhs)
      | _, _ => None
      end
  | RAt pos value =>
      match norm env scope value with
      | Some out => Some (RAt pos out)
      | None => None
      end
  | RUncons value =>
      match norm env scope value with
      | Some out => Some (RUncons out)
      | None => None
      end
  | RFold count vector seed item state body =>
      match norm env scope vector, norm env scope seed,
          rb_elab env item, rb_elab env state with
      | Some values, Some init, Some ibind, Some sbind =>
          match norm env (spush (spush scope ibind) sbind) body with
          | Some out => Some (RFold count values init item state out)
          | None => None
          end
      | _, _, _, _ => None
      end
  | RFoldI vector seed item state body =>
      match norm env scope vector, norm env scope seed,
          rb_elab env item, rb_elab env state with
      | Some values, Some init, Some ibind, Some sbind =>
          match relab env values,
              norm env (spush (spush scope ibind) sbind) body with
          | Some source, Some out =>
              match vlen scope source with
              | Some count => Some (RFold count values init item state out)
              | None => None
              end
          | _, _ => None
          end
      | _, _, _, _ => None
      end
  | RQuant mode source item body =>
      match norm env scope source, rb_elab env item with
      | Some value, Some bind =>
          match norm env (spush scope bind) body with
          | Some out =>
              match relab env value, relab env out with
              | Some input, Some pred =>
                  match vlen scope input, qpick input bind pred with
                  | Some count, Some (state, mark) =>
                      Some (qrterm state mark mode count value item out)
                  | _, _ => None
                  end
              | _, _ => None
              end
          | None => None
          end
      | _, _ => None
      end
  | RStep cap value =>
      match norm env scope cap, norm env scope value with
      | Some lhs, Some rhs => Some (RStep lhs rhs)
      | _, _ => None
      end
  | RClose value =>
      match norm env scope value with
      | Some out => Some (RClose out)
      | None => None
      end
  | RWeave count out source item body =>
      match norm env scope source, rb_elab env item with
      | Some value, Some bind =>
          match norm env (spush scope bind) body with
          | Some term => Some (RWeave count out value item term)
          | None => None
          end
      | _, _ => None
      end
  | RBraid count out lhs0 rhs0 first second body =>
      match norm env scope lhs0, norm env scope rhs0,
          rb_elab env first, rb_elab env second with
      | Some lhs, Some rhs, Some fbind, Some sbind =>
          match norm env (spush (spush scope fbind) sbind) body with
          | Some term => Some (RBraid count out lhs rhs first second term)
          | None => None
          end
      | _, _, _, _ => None
      end
  | RLoom count out item body =>
      match rb_elab env item with
      | Some bind =>
          match norm env (spush scope bind) body with
          | Some term => Some (RLoom count out item term)
          | None => None
          end
      | None => None
      end
  | ROrbit count seed item body =>
      match norm env scope seed, rb_elab env item with
      | Some value, Some bind =>
          match norm env (spush scope bind) body with
          | Some term => Some (ROrbit count value item term)
          | None => None
          end
      | _, _ => None
      end
  | ROrbitTo count turns seed item body =>
      match norm env scope turns, norm env scope seed, rb_elab env item with
      | Some rounds, Some value, Some bind =>
          match norm env (spush scope bind) body with
          | Some term => Some (ROrbitTo count rounds value item term)
          | None => None
          end
      | _, _, _ => None
      end
  | RWake count seed item body =>
      match norm env scope seed, rb_elab env item with
      | Some value, Some bind =>
          match norm env (spush scope bind) body with
          | Some term => Some (RWake count value item term)
          | None => None
          end
      | _, _ => None
      end
  | RRift cut rest elem source =>
      match norm env scope source with
      | Some value => Some (RRift cut rest elem value)
      | None => None
      end
  | RExact raw typ body =>
      if rexact env raw typ then norm env scope body else None
  | RReject => Some RReject
  end.

Definition nelab (env : ienv) (scope : list sbind) (term : rtm)
    : option stm :=
  match norm env scope term with
  | Some out => relab env out
  | None => None
  end.

Theorem qseek_clear : forall fuel index source item body state mark,
  qseek fuel index source item body = Some (state, mark) ->
  qclear state mark source item body = true.
Proof.
  induction fuel as [|fuel IH]; intros index source item body state mark found;
    simpl in found; try discriminate.
  destruct (qclear (did index) (did (S index)) source item body) eqn:clear.
  - inversion found; subst. exact clear.
  - eapply IH. exact found.
Qed.

Theorem qpick_clear : forall source item body state mark,
  qpick source item body = Some (state, mark) ->
  qclear state mark source item body = true.
Proof.
  intros source item body state mark found.
  unfold qpick in found.
  eapply qseek_clear. exact found.
Qed.

Lemma qclear_parts : forall state mark source item body,
  qclear state mark source item body = true ->
  state <> mark /\
  clear state source item body = true /\
  clear mark source item body = true.
Proof.
  intros state mark source item body accepted.
  unfold qclear in accepted.
  apply andb_true_iff in accepted as [rest mark_ok].
  apply andb_true_iff in rest as [fresh state_ok].
  apply negb_true_iff in fresh.
  apply Nat.eqb_neq in fresh.
  repeat split; assumption.
Qed.

Theorem qrterm_elab : forall env state mark mode count source item body
    input bind pred,
  relab env source = Some input ->
  rb_elab env item = Some bind ->
  relab env body = Some pred ->
  relab env (qrterm state mark mode count source item body) =
    Some (SFold count input (qseed mode) bind
      (SBind state MM (qtype mode)) (qbody mode state mark pred)).
Proof.
  intros env state mark mode count source item body input bind pred
    source_ok item_ok body_ok.
  destruct mode; simpl;
    rewrite source_ok, item_ok, body_ok; reflexivity.
Qed.

Theorem qpick_term : forall state mark mode count source item body,
  qpick source item body = Some (state, mark) ->
  qterm state mark mode count source item body =
    Some (SFold count source (qseed mode) item
      (SBind state MM (qtype mode)) (qbody mode state mark body)).
Proof.
  intros state mark mode count source item body picked.
  apply qpick_clear in picked.
  apply qclear_parts in picked as [apart [state_ok mark_ok]].
  apply qterm_exact; assumption.
Qed.

Theorem norm_fold : forall env scope vector seed item state body
    values init ibind sbind source out count,
  norm env scope vector = Some values ->
  norm env scope seed = Some init ->
  rb_elab env item = Some ibind ->
  rb_elab env state = Some sbind ->
  relab env values = Some source ->
  norm env (spush (spush scope ibind) sbind) body = Some out ->
  vlen scope source = Some count ->
  norm env scope (RFoldI vector seed item state body) =
    Some (RFold count values init item state out).
Proof.
  intros env scope vector seed item state body values init ibind sbind
    source out count values_ok init_ok item_ok state_ok source_ok body_ok len_ok.
  simpl.
  rewrite values_ok, init_ok, item_ok, state_ok, source_ok, body_ok, len_ok.
  reflexivity.
Qed.

Theorem norm_quant : forall env scope mode source item body value bind out
    input pred count state mark,
  norm env scope source = Some value ->
  rb_elab env item = Some bind ->
  norm env (spush scope bind) body = Some out ->
  relab env value = Some input ->
  relab env out = Some pred ->
  vlen scope input = Some count ->
  qpick input bind pred = Some (state, mark) ->
  norm env scope (RQuant mode source item body) =
    Some (qrterm state mark mode count value item out).
Proof.
  intros env scope mode source item body value bind out input pred count
    state mark source_ok item_ok body_ok input_ok pred_ok len_ok picked.
  simpl.
  rewrite source_ok, item_ok, body_ok, input_ok, pred_ok, len_ok, picked.
  reflexivity.
Qed.

Theorem norm_quant_elab : forall env state mark mode count source item body
    input bind pred,
  relab env source = Some input ->
  rb_elab env item = Some bind ->
  relab env body = Some pred ->
  qpick input bind pred = Some (state, mark) ->
  qterm state mark mode count input bind pred =
    relab env (qrterm state mark mode count source item body).
Proof.
  intros env state mark mode count source item body input bind pred
    source_ok item_ok body_ok picked.
  rewrite (qpick_term state mark mode count input bind pred picked).
  symmetry.
  apply qrterm_elab; assumption.
Qed.