(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.ZArith.

Require Import Uni.
Require Import Dec.
Require Import DecComp.
Require Import DecSound.
Require Import Lim.
Require Import Surf.

Import ListNotations.

Definition put (id : nat) (item : sbind) : bind :=
  Bind id (smul item) (sty item).

Definition pmax : nat := 64 * 64.

Fixpoint ins (env : senv) (next : nat) (items : list sbind)
    : option (senv * nat * list bind) :=
  match items with
  | [] => Some (env, next, [])
  | item :: rest =>
      match findn (sname item) env with
      | Some _ => None
      | None =>
          match ins ((sname item, next) :: env) (S next) rest with
          | Some (last_env, last, out) =>
              Some (last_env, last, put next item :: out)
          | None => None
          end
      end
  end.

Fixpoint low (env : senv) (next : nat) (term : stm) : option (tm * nat) :=
  match term with
  | SK value typ => Some (K value typ, next)
  | SBytes bytes => Some (Bytes bytes, next)
  | SVnil typ => Some (Vnil typ, next)
  | SVar name =>
      match findn name env with
      | Some id => Some (Var id, next)
      | None => None
      end
  | SLet item value body =>
      match low env next value with
      | Some (out, after) =>
          match low ((sname item, after) :: env) (S after) body with
          | Some (rest, last) => Some (Let (put after item) out rest, last)
          | None => None
          end
      | None => None
      end
  | SIf guard yes no =>
      match low env next guard with
      | Some (gout, after_guard) =>
          match low env after_guard yes with
          | Some (yout, after_yes) =>
              match low env after_yes no with
              | Some (nout, last) => Some (If gout yout nout, last)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | SPair first second =>
      match low env next first with
      | Some (lout, after) =>
          match low env after second with
          | Some (rout, last) => Some (Pair lout rout, last)
          | None => None
          end
      | None => None
      end
  | SUnpair pair_term first second body =>
      if Nat.eqb (sname first) (sname second) then None
      else
        match low env next pair_term with
        | Some (pout, after_pair) =>
            let left_id := after_pair in
            let right_id := S left_id in
            match low ((sname second, right_id) :: (sname first, left_id) :: env)
              (S right_id) body with
            | Some (bout, last) =>
                Some (Unpair pout (put left_id first) (put right_id second) bout, last)
            | None => None
            end
        | None => None
        end
  | SFst value =>
      match low env next value with
      | Some (out, last) => Some (Fst out, last)
      | None => None
      end
  | SSnd value =>
      match low env next value with
      | Some (out, last) => Some (Snd out, last)
      | None => None
      end
  | SInl value other =>
      match low env next value with
      | Some (out, last) => Some (Inl out other, last)
      | None => None
      end
  | SInr other value =>
      match low env next value with
      | Some (out, last) => Some (Inr other out, last)
      | None => None
      end
  | SCase value yes_bind yes no_bind no =>
      match low env next value with
      | Some (vout, after_value) =>
          let left_id := after_value in
          match low ((sname yes_bind, left_id) :: env) (S left_id) yes with
          | Some (yout, after_yes) =>
              let right_id := after_yes in
              match low ((sname no_bind, right_id) :: env) (S right_id) no with
              | Some (nout, last) =>
                  Some (Case vout (put left_id yes_bind) yout
                    (put right_id no_bind) nout, last)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | SAct action body =>
      match low env next body with
      | Some (out, last) => Some (Act action out, last)
      | None => None
      end
  | SAdd first second =>
      match low env next first with
      | Some (lout, after) =>
          match low env after second with
          | Some (rout, last) => Some (Add lout rout, last)
          | None => None
          end
      | None => None
      end
  | SSub first second =>
      match low env next first with
      | Some (lout, after) =>
          match low env after second with
          | Some (rout, last) => Some (Sub lout rout, last)
          | None => None
          end
      | None => None
      end
  | SMul first second =>
      match low env next first with
      | Some (lout, after) =>
          match low env after second with
          | Some (rout, last) => Some (Mul lout rout, last)
          | None => None
          end
      | None => None
      end
  | SDiv first second =>
      match low env next first with
      | Some (lout, after) =>
          match low env after second with
          | Some (rout, last) => Some (Div lout rout, last)
          | None => None
          end
      | None => None
      end
  | SMod first second =>
      match low env next first with
      | Some (lout, after) =>
          match low env after second with
          | Some (rout, last) => Some (Mod lout rout, last)
          | None => None
          end
      | None => None
      end
  | SNeg value =>
      match low env next value with
      | Some (out, last) => Some (Neg out, last)
      | None => None
      end
  | SAbs value =>
      match low env next value with
      | Some (out, last) => Some (Abs out, last)
      | None => None
      end
  | SEq typ first second =>
      match low env next first with
      | Some (lout, after) =>
          match low env after second with
          | Some (rout, last) => Some (Eq typ lout rout, last)
          | None => None
          end
      | None => None
      end
  | SCat first second =>
      match low env next first with
      | Some (lout, after) =>
          match low env after second with
          | Some (rout, last) => Some (Cat lout rout, last)
          | None => None
          end
      | None => None
      end
  | STake len value =>
      match low env next value with
      | Some (out, last) => Some (Take len out, last)
      | None => None
      end
  | SDrop len value =>
      match low env next value with
      | Some (out, last) => Some (Drop len out, last)
      | None => None
      end
  | SVcons first rest =>
      match low env next first with
      | Some (fout, after) =>
          match low env after rest with
          | Some (rout, last) => Some (Vcons fout rout, last)
          | None => None
          end
      | None => None
      end
  | SVcat first second =>
      match low env next first with
      | Some (lout, after) =>
          match low env after second with
          | Some (rout, last) => Some (Vcat lout rout, last)
          | None => None
          end
      | None => None
      end
  | SAt index value =>
      match low env next value with
      | Some (out, last) => Some (At index out, last)
      | None => None
      end
  | SUncons value =>
      match low env next value with
      | Some (out, last) => Some (Uncons out, last)
      | None => None
      end
  | SFold count vector seed item state body =>
      if Nat.eqb (sname item) (sname state) then None
      else
        match low env next vector with
        | Some (vout, after_vector) =>
            match low env after_vector seed with
            | Some (sout, after_seed) =>
                let item_id := after_seed in
                let state_id := S item_id in
                match low
                  ((sname state, state_id) :: (sname item, item_id) :: env)
                  (S state_id) body with
                | Some (bout, last) =>
                    Some (Fold count vout sout (put item_id item)
                      (put state_id state) bout, last)
                | None => None
                end
            | None => None
            end
        | None => None
        end
  | SStep cap value =>
      match low env next cap with
      | Some (cout, after) =>
          match low env after value with
          | Some (vout, last) => Some (Step cout vout, last)
          | None => None
          end
      | None => None
      end
  | SClose cap =>
      match low env next cap with
      | Some (out, last) => Some (Close out, last)
      | None => None
      end
  end.

Definition scheck (gamma : ctx) (term : stm) :=
  match low [] 0 term with
  | Some (core, _) => checkb gamma core
  | None => None
  end.

Definition prog (items : list sbind) (body : stm)
    : option (list bind * tm) :=
  if Nat.leb (length items) pmax then
    match ins [] 0 items with
    | Some (env, next, binds) =>
        match low env next body with
        | Some (core, _) =>
            if forallb bind_b binds && tm_b core
            then Some (binds, core)
            else None
        | None => None
        end
    | None => None
    end
  else None.

Fixpoint opens (gamma : ctx) (binds : list bind) : option ctx :=
  match binds with
  | [] => Some gamma
  | binder :: rest =>
      match openb binder gamma with
      | Some next => opens next rest
      | None => None
      end
  end.

Fixpoint doneb (gamma : ctx) : bool :=
  match gamma with
  | [] => true
  | Cell _ M1 _ true :: _ => false
  | _ :: rest => doneb rest
  end.

Definition pview (items : list sbind) (body : stm) : option chk :=
  match prog items body with
  | Some (binds, core) =>
      match opens [] binds with
      | Some gamma => checkb gamma core
      | None => None
      end
  | None => None
  end.

Definition pcheck (items : list sbind) (body : stm) : option chk :=
  match prog items body with
  | Some (binds, core) =>
      match opens [] binds with
      | Some gamma =>
          match checkb gamma core with
          | Some (typ, row, cost, next) =>
              if doneb next then Some (typ, row, cost, next) else None
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Theorem pview_sound : forall items body typ row cost next,
  pview items body = Some (typ, row, cost, next) ->
  exists binds core gamma,
    prog items body = Some (binds, core) /\
    opens [] binds = Some gamma /\
    check gamma core typ row cost next.
Proof.
  intros items body typ row cost next accepted.
  unfold pview in accepted.
  destruct (prog items body) as [[binds core] |] eqn:lowered;
    try discriminate.
  destruct (opens [] binds) as [gamma |] eqn:opened;
    try discriminate.
  exists binds, core, gamma.
  repeat split; try assumption.
  eapply checkb_sound. exact accepted.
Qed.

Theorem pview_complete : forall items body binds core gamma typ row cost next,
  prog items body = Some (binds, core) ->
  opens [] binds = Some gamma ->
  check gamma core typ row cost next ->
  pview items body = Some (typ, row, cost, next).
Proof.
  intros items body binds core gamma typ row cost next lowered opened checked.
  unfold pview.
  rewrite lowered, opened.
  apply checkb_complete.
  exact checked.
Qed.

Lemma ins_ids : forall items env next last_env last binds,
  ins env next items = Some (last_env, last, binds) ->
  map bid binds = List.seq next (length items) /\
  last = next + length items.
Proof.
  induction items as [| item rest IH];
    intros env next last_env last binds lowered; simpl in lowered.
  - inversion lowered; subst.
    split.
    + reflexivity.
    + apply plus_n_O.
  - destruct (findn (sname item) env) as [id |] eqn:found;
      try discriminate.
    destruct (ins ((sname item, next) :: env) (S next) rest)
      as [[[rest_env rest_next] rest_binds] |] eqn:lowered_rest;
      try discriminate.
    inversion lowered; subst.
    specialize (IH _ _ _ _ _ lowered_rest) as [ids_ok next_ok].
    split.
    + simpl.
      rewrite ids_ok.
      reflexivity.
    + rewrite next_ok.
      rewrite plus_Sn_m.
      rewrite plus_n_Sm.
      reflexivity.
Qed.

Theorem prog_ids : forall items body binds core,
  prog items body = Some (binds, core) ->
  map bid binds = List.seq 0 (length items) /\
  length items <= pmax.
Proof.
  intros items body binds core lowered.
  unfold prog in lowered.
  destruct (Nat.leb (length items) pmax) eqn:count_ok;
    try discriminate.
  destruct (ins [] 0 items) as [[[env next] out] |] eqn:inputs_ok;
    try discriminate.
  destruct (low env next body) as [[term last] |] eqn:body_ok;
    try discriminate.
  destruct (forallb bind_b out && tm_b term) eqn:profile_ok;
    try discriminate.
  inversion lowered; subst.
  split.
  - apply (proj1 (ins_ids items [] 0 env next binds inputs_ok)).
  - apply Nat.leb_le.
    exact count_ok.
Qed.

Theorem prog_profile : forall items body binds core,
  prog items body = Some (binds, core) ->
  forallb bind_b binds = true /\ tm_b core = true.
Proof.
  intros items body binds core lowered.
  unfold prog in lowered.
  destruct (Nat.leb (length items) pmax); try discriminate.
  destruct (ins [] 0 items) as [[[env next] out] |]; try discriminate.
  destruct (low env next body) as [[term last] |]; try discriminate.
  destruct (forallb bind_b out) eqn:binds_ok; simpl in lowered;
    try discriminate.
  destruct (tm_b term) eqn:term_ok; simpl in lowered; try discriminate.
  inversion lowered; subst.
  split; assumption.
Qed.

Theorem pcheck_sound : forall items body typ row cost next,
  pcheck items body = Some (typ, row, cost, next) ->
  exists binds core gamma,
    prog items body = Some (binds, core) /\
    opens [] binds = Some gamma /\
    check gamma core typ row cost next /\
    doneb next = true.
Proof.
  intros items body typ row cost next accepted.
  unfold pcheck in accepted.
  destruct (prog items body) as [[binds core] |] eqn:lowered;
    try discriminate.
  destruct (opens [] binds) as [gamma |] eqn:opened;
    try discriminate.
  destruct (checkb gamma core) as [[[[out_typ out_row] out_cost] out_next] |]
    eqn:checked; try discriminate.
  destruct (doneb out_next) eqn:done; try discriminate.
  inversion accepted; subst.
  exists binds, core, gamma.
  repeat split; try assumption.
  apply checkb_sound.
  exact checked.
Qed.

Theorem pcheck_complete : forall items body binds core gamma typ row cost next,
  prog items body = Some (binds, core) ->
  opens [] binds = Some gamma ->
  check gamma core typ row cost next ->
  doneb next = true ->
  pcheck items body = Some (typ, row, cost, next).
Proof.
  intros items body binds core gamma typ row cost next
    lowered opened checked done.
  unfold pcheck.
  rewrite lowered, opened.
  rewrite (checkb_complete gamma core typ row cost next checked).
  rewrite done.
  reflexivity.
Qed.

Lemma findn_head : forall name id env,
  findn name ((name, id) :: env) = Some id.
Proof.
  intros name id env.
  simpl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma findn_next : forall name key id env,
  name <> key ->
  findn name ((key, id) :: env) = findn name env.
Proof.
  intros name key id env distinct.
  simpl.
  apply Nat.eqb_neq in distinct.
  rewrite distinct.
  reflexivity.
Qed.

Lemma put_mul : forall id item,
  bmul (put id item) = smul item.
Proof.
  reflexivity.
Qed.

Lemma put_ty : forall id item,
  bty (put id item) = sty item.
Proof.
  reflexivity.
Qed.

Theorem alpha_low : forall left right lterm rterm,
  alpha left right lterm rterm ->
  forall next, low left next lterm = low right next rterm.
Proof.
  intros left right lterm rterm related.
  induction related; intros next; simpl;
    try rewrite IHrelated;
    try rewrite IHrelated1;
    try rewrite IHrelated2;
    try rewrite IHrelated3;
    try reflexivity.
  - rewrite H, H0.
    reflexivity.
  - destruct (low right next rvalue) as [[out after] |] eqn:value; simpl.
    + match goal with
      | ih : forall id next,
          low ((lname, id) :: left) next lbody =
          low ((rname, id) :: right) next rbody |- _ =>
          rewrite (ih after (S after))
      end.
      reflexivity.
    + reflexivity.
  - destruct (low right next rg) as [[gout after_guard] |] eqn:guard; simpl.
    + rewrite (IHrelated2 after_guard).
      destruct (low right after_guard ry) as [[yout after_yes] |] eqn:yes; simpl.
      * rewrite (IHrelated3 after_yes).
        reflexivity.
      * reflexivity.
    + reflexivity.
  - destruct (low right next ra) as [[lout after] |] eqn:first; simpl.
    + rewrite (IHrelated2 after).
      reflexivity.
    + reflexivity.
  - apply Nat.eqb_neq in H.
    apply Nat.eqb_neq in H0.
    rewrite H, H0.
    destruct (low right next rp) as [[pout after] |] eqn:pair; simpl.
    + match goal with
      | ih : forall id1 id2 next,
          low ((ln2, id2) :: (ln1, id1) :: left) next lb =
          low ((rn2, id2) :: (rn1, id1) :: right) next rb |- _ =>
          rewrite (ih after (S after) (S (S after)))
      end.
      reflexivity.
    + reflexivity.
  - destruct (low right next rv) as [[vout after] |] eqn:value; simpl.
    + match goal with
      | ih : forall id next,
          low ((ln, id) :: left) next ly =
          low ((rn, id) :: right) next ry |- _ =>
          rewrite (ih after (S after))
      end.
      destruct (low ((rn, after) :: right) (S after) ry)
        as [[yout after_yes] |] eqn:yes; simpl.
      * match goal with
        | ih : forall id next,
            low ((ln2, id) :: left) next lno =
            low ((rn2, id) :: right) next rno |- _ =>
            rewrite (ih after_yes (S after_yes))
        end.
        reflexivity.
      * reflexivity.
    + reflexivity.
  - destruct (low right next ra) as [[lout after] |] eqn:first; simpl.
    + rewrite (IHrelated2 after).
      reflexivity.
    + reflexivity.
  - destruct (low right next ra) as [[lout after] |] eqn:first; simpl.
    + rewrite (IHrelated2 after).
      reflexivity.
    + reflexivity.
  - destruct (low right next ra) as [[lout after] |] eqn:first; simpl.
    + rewrite (IHrelated2 after).
      reflexivity.
    + reflexivity.
  - destruct (low right next ra) as [[lout after] |] eqn:first; simpl.
    + rewrite (IHrelated2 after).
      reflexivity.
    + reflexivity.
  - destruct (low right next ra) as [[lout after] |] eqn:first; simpl.
    + rewrite (IHrelated2 after).
      reflexivity.
    + reflexivity.
  - destruct (low right next ra) as [[lout after] |] eqn:first; simpl.
    + rewrite (IHrelated2 after).
      reflexivity.
    + reflexivity.
  - destruct (low right next ra) as [[lout after] |] eqn:first; simpl.
    + rewrite (IHrelated2 after).
      reflexivity.
    + reflexivity.
  - destruct (low right next ra) as [[lout after] |] eqn:first; simpl.
    + rewrite (IHrelated2 after).
      reflexivity.
    + reflexivity.
  - destruct (low right next ra) as [[lout after] |] eqn:first; simpl.
    + rewrite (IHrelated2 after).
      reflexivity.
    + reflexivity.
  - apply Nat.eqb_neq in H.
    apply Nat.eqb_neq in H0.
    rewrite H, H0.
    destruct (low right next rv) as [[vout after_vector] |] eqn:vector; simpl.
    + rewrite (IHrelated2 after_vector).
      destruct (low right after_vector rs) as [[sout after_seed] |] eqn:seed; simpl.
      * match goal with
        | ih : forall id1 id2 next,
            low ((ln2, id2) :: (ln1, id1) :: left) next lb =
            low ((rn2, id2) :: (rn1, id1) :: right) next rb |- _ =>
            rewrite (ih after_seed (S after_seed) (S (S after_seed)))
        end.
        reflexivity.
      * reflexivity.
    + reflexivity.
  - destruct (low right next ra) as [[cout after] |] eqn:first; simpl.
    + rewrite (IHrelated2 after).
      reflexivity.
    + reflexivity.
Qed.

Corollary alpha_check : forall left right,
  alpha [] [] left right ->
  forall gamma, scheck gamma left = scheck gamma right.
Proof.
  intros left right related gamma.
  unfold scheck.
  rewrite (alpha_low [] [] left right related 0).
  reflexivity.
Qed.

Example alpha_let_sample :
  alpha [] []
    (SLet (SBind 7 M1 TInt) (SK (VInt (Z.of_nat 5)) TInt) (SVar 7))
    (SLet (SBind 19 M1 TInt) (SK (VInt (Z.of_nat 5)) TInt) (SVar 19)).
Proof.
  apply ALet.
  - apply AK.
  - intros id.
    apply AVar with (id := id).
    + apply findn_head.
    + apply findn_head.
Qed.