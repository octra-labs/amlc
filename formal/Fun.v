(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Uni.
Require Import Dec.
Require Import DecComp.
Require Import DecSound.
Require Import Lim.
Require Import Surf.
Require Import Low.

Import ListNotations.

Record arr : Type := Arr {
  amul : mul;
  acaps : list sbind;
  aarg : sbind;
  aout : ty;
  aeff : list atom;
  alim : option res
}.

Record fn : Type := Fn {
  fname : nat;
  farr : arr;
  fbody : stm
}.

Inductive ftm : Type :=
| FRet : stm -> ftm
| FLet : sbind -> stm -> ftm -> ftm
| FIf : stm -> ftm -> ftm -> ftm
| FCall : sbind -> nat -> list stm -> stm -> ftm -> ftm.

Definition mul_eqb (left right : mul) : bool :=
  if mul_dec left right then true else false.

Definition atom_eq_dec : forall left right : atom, {left = right} + {left <> right}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition atom_eqb (left right : atom) : bool :=
  if atom_eq_dec left right then true else false.

Fixpoint has_atom (action : atom) (row : list atom) : bool :=
  match row with
  | [] => false
  | item :: rest => atom_eqb action item || has_atom action rest
  end.

Definition row_subb (actual declared : list atom) : bool :=
  forallb (fun action => has_atom action declared) actual.

Definition res_b (value : res) : bool :=
  fit (rsteps value) && fit (rdepth value) && fit (rwork value).

Definition rleb (actual declared : res) : bool :=
  Nat.leb (rsteps actual) (rsteps declared)
    && Nat.leb (rdepth actual) (rdepth declared)
    && Nat.leb (rwork actual) (rwork declared).

Definition underb (actual : res) (declared : option res) : bool :=
  match declared with
  | None => true
  | Some limit => res_b limit && rleb actual limit
  end.

Fixpoint capm (caps : list sbind) : option mul :=
  match caps with
  | [] => Some MM
  | item :: rest =>
      match smul item, capm rest with
      | M0, _ => None
      | M1, Some _ => Some M1
      | MM, Some mode => Some mode
      | _, None => None
      end
  end.

Definition fcheckb (item : fn) : bool :=
  match capm (acaps (farr item)),
      pcheck (acaps (farr item) ++ [aarg (farr item)]) (fbody item) with
  | Some mode, Some (typ, row, cost, _) =>
      mul_eqb mode (amul (farr item)) && ty_eqb typ (aout (farr item))
        && forallb atom_b (aeff (farr item))
        && row_subb row (aeff (farr item))
        && underb cost (alim (farr item))
  | _, _ => false
  end.

Fixpoint findf (name : nat) (fns : list fn) : option fn :=
  match fns with
  | [] => None
  | item :: rest =>
      if Nat.eqb name (fname item) then Some item else findf name rest
  end.

Fixpoint defs_b (seen : list nat) (fns : list fn) : bool :=
  match fns with
  | [] => true
  | item :: rest =>
      negb (existsb (Nat.eqb (fname item)) seen)
        && fcheckb item && defs_b (fname item :: seen) rest
  end.

Fixpoint actuals (outer inner : senv) (next : nat)
    (formals : list sbind) (values : list stm)
    : option (senv * nat * list (bind * tm)) :=
  match formals, values with
  | [], [] => Some (inner, next, [])
  | formal :: formal_rest, value :: value_rest =>
      match low outer next value with
      | Some (core, after) =>
          match actuals outer ((sname formal, after) :: inner) (S after)
              formal_rest value_rest with
          | Some (last_env, last, rest) =>
              Some (last_env, last, (put after formal, core) :: rest)
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.

Fixpoint wrap (values : list (bind * tm)) (body : tm) : tm :=
  match values with
  | [] => body
  | (binder, value) :: rest => Let binder value (wrap rest body)
  end.

Definition call_low (outer : senv) (next : nat) (item : fn)
    (caps : list stm) (arg : stm) : option (tm * nat) :=
  let spec := farr item in
  match actuals outer [] next (acaps spec ++ [aarg spec]) (caps ++ [arg]) with
  | Some (inner, after, values) =>
      match low inner after (fbody item) with
      | Some (body, last) => Some (wrap values body, last)
      | None => None
      end
  | None => None
  end.

Fixpoint flow (fns : list fn) (env : senv) (next : nat) (term : ftm)
    : option (tm * nat) :=
  match term with
  | FRet body => low env next body
  | FLet result value rest =>
      match low env next value with
      | Some (out, after_value) =>
          match flow fns ((sname result, after_value) :: env)
              (S after_value) rest with
          | Some (body, last) =>
              Some (Let (put after_value result) out body, last)
          | None => None
          end
      | None => None
      end
  | FIf guard yes no =>
      match low env next guard with
      | Some (gout, after_guard) =>
          match flow fns env after_guard yes with
          | Some (yout, after_yes) =>
              match flow fns env after_yes no with
              | Some (nout, last) => Some (If gout yout nout, last)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | FCall result name caps arg rest =>
      match findf name fns with
      | Some item =>
          if Nat.eqb (length caps) (length (acaps (farr item)))
            && ty_eqb (sty result) (aout (farr item)) then
            match call_low env next item caps arg with
            | Some (value, after_value) =>
                match flow fns ((sname result, after_value) :: env)
                    (S after_value) rest with
                | Some (body, last) =>
                    Some (Let (put after_value result) value body, last)
                | None => None
                end
            | None => None
            end
          else None
      | None => None
      end
  end.

Theorem flow_let : forall fns env next result value rest out after body last,
  low env next value = Some (out, after) ->
  flow fns ((sname result, after) :: env) (S after) rest = Some (body, last) ->
  flow fns env next (FLet result value rest) =
    Some (Let (put after result) out body, last).
Proof.
  intros fns env next result value rest out after body last value_ok body_ok.
  simpl.
  rewrite value_ok, body_ok.
  reflexivity.
Qed.

Definition fprog (items : list sbind) (fns : list fn) (body : ftm)
    : option (list bind * tm) :=
  if Nat.leb (length items) pmax && Nat.leb (length fns) pmax
      && defs_b [] fns then
    match ins [] 0 items with
    | Some (env, next, binds) =>
        match flow fns env next body with
        | Some (core, _) =>
            if forallb bind_b binds && tm_b core
            then Some (binds, core)
            else None
        | None => None
        end
    | None => None
    end
  else None.

Definition fpcheck (items : list sbind) (fns : list fn) (body : ftm)
    : option chk :=
  match fprog items fns body with
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

Lemma mul_eqb_eq : forall left right,
  mul_eqb left right = true <-> left = right.
Proof.
  intros left right.
  unfold mul_eqb.
  destruct (mul_dec left right) as [same | distinct].
  - split.
    + intros.
      exact same.
    + intros.
      reflexivity.
  - split.
    + discriminate.
    + intros same.
      contradiction.
Qed.

Lemma atom_eqb_eq : forall left right,
  atom_eqb left right = true <-> left = right.
Proof.
  intros left right.
  unfold atom_eqb.
  destruct (atom_eq_dec left right) as [same | distinct].
  - split.
    + intros.
      exact same.
    + intros.
      reflexivity.
  - split.
    + discriminate.
    + intros same.
      contradiction.
Qed.

Lemma has_atom_sound : forall action row,
  has_atom action row = true -> In action row.
Proof.
  intros action row.
  induction row as [|item rest IH]; intros accepted; try discriminate.
  simpl in accepted.
  apply orb_true_iff in accepted as [same | found].
  - left.
    apply atom_eqb_eq in same.
    symmetry.
    exact same.
  - right.
    apply IH.
    exact found.
Qed.

Lemma has_atom_complete : forall action row,
  In action row -> has_atom action row = true.
Proof.
  intros action row.
  induction row as [|item rest IH]; intros found; try contradiction.
  simpl.
  destruct found as [same | found].
  - apply orb_true_iff.
    left.
    apply atom_eqb_eq.
    symmetry.
    exact same.
  - apply orb_true_iff.
    right.
    apply IH.
    exact found.
Qed.

Theorem row_subb_spec : forall actual declared,
  row_subb actual declared = true <-> within actual declared.
Proof.
  intros actual declared.
  split.
  - intros accepted.
    unfold row_subb in accepted.
    unfold within.
    apply Forall_forall.
    intros action found.
    apply has_atom_sound.
    apply forallb_forall with (x := action) in accepted.
    + exact accepted.
    + exact found.
  - intros accepted.
    unfold row_subb.
    apply forallb_forall.
    intros action found.
    apply has_atom_complete.
    unfold within in accepted.
    apply Forall_forall with (x := action) in accepted.
    + exact accepted.
    + exact found.
Qed.

Theorem rleb_spec : forall actual declared,
  rleb actual declared = true <-> rle actual declared.
Proof.
  intros [actual_steps actual_depth actual_work]
    [limit_steps limit_depth limit_work].
  unfold rleb, rle.
  simpl.
  repeat rewrite andb_true_iff.
  repeat rewrite Nat.leb_le.
  split.
  - intros [[steps depth] work] axis.
    destruct axis; assumption.
  - intros order.
    repeat split.
    + exact (order AxStep).
    + exact (order AxDepth).
    + exact (order AxWork).
Qed.

Theorem fcheck_marks : forall item typ row cost next,
  fcheckb item = true ->
  pcheck (acaps (farr item) ++ [aarg (farr item)]) (fbody item) =
    Some (typ, row, cost, next) ->
  forallb atom_b (aeff (farr item)) = true /\
  within row (aeff (farr item)).
Proof.
  intros item typ row cost next accepted checked.
  unfold fcheckb in accepted.
  destruct (capm (acaps (farr item))); try discriminate.
  rewrite checked in accepted.
  apply andb_true_iff in accepted as [accepted _].
  apply andb_true_iff in accepted as [head subset].
  apply andb_true_iff in head as [_ valid].
  split.
  - exact valid.
  - apply row_subb_spec.
    exact subset.
Qed.

Theorem fcheck_under : forall item typ row cost next limit,
  fcheckb item = true ->
  pcheck (acaps (farr item) ++ [aarg (farr item)]) (fbody item) =
    Some (typ, row, cost, next) ->
  alim (farr item) = Some limit ->
  res_b limit = true /\ rle cost limit.
Proof.
  intros item typ row cost next limit accepted checked declared.
  unfold fcheckb in accepted.
  destruct (capm (acaps (farr item))); try discriminate.
  rewrite checked in accepted.
  apply andb_true_iff in accepted as [_ measured].
  unfold underb in measured.
  rewrite declared in measured.
  apply andb_true_iff in measured as [valid ordered].
  split.
  - exact valid.
  - apply rleb_spec.
    exact ordered.
Qed.

Lemma capm_many : forall caps,
  capm caps = Some MM -> Forall (fun item => smul item = MM) caps.
Proof.
  induction caps as [|item rest IH]; intros accepted.
  - constructor.
  - simpl in accepted.
    destruct (smul item) eqn:item_mode.
    + discriminate.
    + destruct (capm rest); discriminate.
    + constructor.
      * exact item_mode.
      * apply IH.
        destruct (capm rest) eqn:rest_mode; try discriminate.
        inversion accepted; subst.
        reflexivity.
Qed.

Lemma capm_one : forall caps mode item,
  capm caps = Some mode ->
  In item caps ->
  smul item = M1 ->
  mode = M1.
Proof.
  induction caps as [|head rest IH]; intros mode item accepted found linear.
  - contradiction.
  - simpl in accepted.
    destruct (smul head) eqn:head_mode; try discriminate.
    + destruct (capm rest); try discriminate.
      inversion accepted.
      reflexivity.
    + destruct (capm rest) eqn:rest_mode; try discriminate.
      injection accepted as eq_mode.
      subst mode.
      destruct found as [same | found].
      * subst.
        rewrite head_mode in linear.
        discriminate.
      * apply (IH m item eq_refl found linear).
Qed.

Theorem repeated_captures : forall item,
  fcheckb item = true ->
  amul (farr item) = MM ->
  Forall (fun cap => smul cap = MM) (acaps (farr item)).
Proof.
  intros item accepted repeated.
  unfold fcheckb in accepted.
  destruct (capm (acaps (farr item))) as [mode |] eqn:mode_ok;
    try discriminate.
  destruct (pcheck (acaps (farr item) ++ [aarg (farr item)]) (fbody item))
    as [[[[typ row] cost] next] |]; try discriminate.
  apply andb_true_iff in accepted as [accepted _].
  apply andb_true_iff in accepted as [head _].
  apply andb_true_iff in head as [head _].
  apply andb_true_iff in head as [same _].
  apply mul_eqb_eq in same.
  rewrite repeated in same.
  subst mode.
  apply capm_many.
  exact mode_ok.
Qed.

Theorem linear_capture : forall item cap,
  fcheckb item = true ->
  In cap (acaps (farr item)) ->
  smul cap = M1 ->
  amul (farr item) = M1.
Proof.
  intros item cap accepted found linear.
  unfold fcheckb in accepted.
  destruct (capm (acaps (farr item))) as [mode |] eqn:mode_ok;
    try discriminate.
  destruct (pcheck (acaps (farr item) ++ [aarg (farr item)]) (fbody item))
    as [[[[typ row] cost] next] |]; try discriminate.
  apply andb_true_iff in accepted as [accepted _].
  apply andb_true_iff in accepted as [head _].
  apply andb_true_iff in head as [head _].
  apply andb_true_iff in head as [same _].
  apply mul_eqb_eq in same.
  rewrite <- same.
  apply (capm_one (acaps (farr item)) mode cap mode_ok found linear).
Qed.

Theorem fpcheck_sound : forall items fns body typ row cost next,
  fpcheck items fns body = Some (typ, row, cost, next) ->
  exists binds core gamma,
    fprog items fns body = Some (binds, core) /\
    opens [] binds = Some gamma /\
    check gamma core typ row cost next /\
    doneb next = true.
Proof.
  intros items fns body typ row cost next accepted.
  unfold fpcheck in accepted.
  destruct (fprog items fns body) as [[binds core] |] eqn:lowered;
    try discriminate.
  destruct (opens [] binds) as [gamma |] eqn:opened; try discriminate.
  destruct (checkb gamma core) as [[[[out_typ out_row] out_cost] out_next] |]
    eqn:checked; try discriminate.
  destruct (doneb out_next) eqn:done; try discriminate.
  inversion accepted; subst.
  exists binds, core, gamma.
  repeat split; try assumption.
  apply checkb_sound.
  exact checked.
Qed.

Theorem fpcheck_complete : forall items fns body binds core gamma typ row cost next,
  fprog items fns body = Some (binds, core) ->
  opens [] binds = Some gamma ->
  check gamma core typ row cost next ->
  doneb next = true ->
  fpcheck items fns body = Some (typ, row, cost, next).
Proof.
  intros items fns body binds core gamma typ row cost next
    lowered opened checked done.
  unfold fpcheck.
  rewrite lowered, opened.
  rewrite (checkb_complete gamma core typ row cost next checked).
  rewrite done.
  reflexivity.
Qed.