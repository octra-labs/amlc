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
Require Import Data.

Import ListNotations.

Record rfield : Type := RField {
  rfname : nat;
  rftyp : ty
}.

Record rtype : Type := RType {
  rtag : list bool;
  rname : nat;
  rfields : list rfield
}.

Record ritem : Type := RItem {
  riname : nat;
  rivalue : stm
}.

Record rpick : Type := RPick {
  rpname : nat;
  rpbind : sbind
}.

Fixpoint prodt (items : list rfield) : option ty :=
  match items with
  | [] => None
  | [item] => Some (rftyp item)
  | item :: rest =>
      match prodt rest with
      | Some rhs => Some (TPair (rftyp item) rhs)
      | None => None
      end
  end.

Definition rdata (item : rtype) : option dtype :=
  match prodt (rfields item) with
  | Some prod => Some (DType (rtag item) (rname item) [Ctor (rname item) prod])
  | None => None
  end.

Definition rtype_t (item : rtype) : option ty :=
  match rdata item with
  | Some data => dtype_t data
  | None => None
  end.

Fixpoint has_rname (name : nat) (items : list rfield) : bool :=
  match items with
  | [] => false
  | item :: rest => Nat.eqb name (rfname item) || has_rname name rest
  end.

Fixpoint rnames_b (items : list rfield) : bool :=
  match items with
  | [] => true
  | item :: rest => negb (has_rname (rfname item) rest) && rnames_b rest
  end.

Definition rdecl_b (item : rtype) : bool :=
  match rfields item, rdata item with
  | [], _ => false
  | fields, Some data =>
      Nat.leb (length fields) pmax && rnames_b fields && decl_b data
  | _, None => false
  end.

Fixpoint items_b (fields : list rfield) (items : list ritem) : bool :=
  match fields, items with
  | [], [] => true
  | field :: rest, item :: tail =>
      Nat.eqb (rfname field) (riname item) && items_b rest tail
  | _, _ => false
  end.

Fixpoint pack (items : list ritem) : option stm :=
  match items with
  | [] => None
  | [item] => Some (rivalue item)
  | item :: rest =>
      match pack rest with
      | Some rhs => Some (SPair (rivalue item) rhs)
      | None => None
      end
  end.

Definition rmake (item : rtype) (items : list ritem) : option stm :=
  if rdecl_b item then
    if items_b (rfields item) items then
      match rdata item, pack items with
      | Some data, Some value => make data (rname item) value
      | _, _ => None
      end
    else None
  else None.

Fixpoint rbody (seed : nat) (fields : list rfield) (items : list rpick)
    (value body : stm) : option stm :=
  match fields, items with
  | [_], [item] => Some (SLet (rpbind item) value body)
  | _ :: rest, item :: tail =>
      match prodt rest with
      | Some rhs =>
          match rbody (S seed) rest tail (SVar (did seed)) body with
          | Some out => Some (SUnpair value (rpbind item)
              (SBind (did seed) (paym rhs) rhs) out)
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.

Definition pick_b (field : rfield) (item : rpick) : bool :=
  Nat.eqb (rfname field) (rpname item)
    && ty_eqb (rftyp field) (sty (rpbind item))
    && meqb (paym (rftyp field)) (smul (rpbind item)).

Fixpoint picks_b (fields : list rfield) (items : list rpick) : bool :=
  match fields, items with
  | [], [] => true
  | field :: rest, item :: tail =>
      pick_b field item && picks_b rest tail
  | _, _ => false
  end.

Fixpoint has_bname (name : nat) (items : list rpick) : bool :=
  match items with
  | [] => false
  | item :: rest => Nat.eqb name (sname (rpbind item)) || has_bname name rest
  end.

Fixpoint bnames_b (items : list rpick) : bool :=
  match items with
  | [] => true
  | item :: rest =>
      negb (has_bname (sname (rpbind item)) rest) && bnames_b rest
  end.

Definition rsplit (item : rtype) (value : stm) (items : list rpick)
    (body : stm) : option stm :=
  if rdecl_b item then
    if picks_b (rfields item) items && bnames_b items then
      match prodt (rfields item), rdata item with
      | Some prod, Some data =>
          let payload := SBind (did 2) (paym prod) prod in
          match rbody 3 (rfields item) items (SVar (did 2)) body with
          | Some out => dcase data value [Arm (rname item) payload out]
          | None => None
          end
      | _, _ => None
      end
    else None
  else None.

Fixpoint rbranch (env : senv) (next : nat) (fields : list rfield)
    (items : list rpick) (value : tm) (body : stm) : option (tm * nat) :=
  match fields, items with
  | [_], [item] =>
      match low ((sname (rpbind item), next) :: env) (S next) body with
      | Some (out, last) => Some (Let (put next (rpbind item)) value out, last)
      | None => None
      end
  | _ :: rest, item :: tail =>
      match prodt rest with
      | Some rhs =>
          let left_id := next in
          let right_id := S left_id in
          match rbranch ((sname (rpbind item), left_id) :: env)
              (S right_id) rest tail (Var right_id) body with
          | Some (out, last) =>
              Some (Unpair value (put left_id (rpbind item))
                (Bind right_id (paym rhs) rhs) out, last)
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.

Definition rprog (inputs : list sbind) (item : rtype) (value : stm)
    (picks : list rpick) (body : stm) : option (list bind * tm) :=
  if Nat.leb (length inputs) pmax then
    if rdecl_b item then
      if picks_b (rfields item) picks && bnames_b picks then
        match ins [] 0 inputs with
        | Some (env, next, binds) =>
            match low env next value with
            | Some (core, after) =>
                match prodt (rfields item) with
                | Some prod =>
                    let tag_id := after in
                    let sum_id := S tag_id in
                    let payload_id := S sum_id in
                    match rbranch env (S payload_id) (rfields item) picks
                        (Var payload_id) body with
                    | Some (out, _) =>
                        let unpack := Let (Bind payload_id (paym prod) prod)
                          (Var sum_id) out in
                        let term := Unpair core
                          (Bind tag_id MM (tagt (rtag item)))
                          (Bind sum_id M1 prod) unpack in
                        if forallb bind_b binds && tm_b term
                        then Some (binds, term)
                        else None
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
      else None
    else None
  else None.

Definition rpcheck (inputs : list sbind) (item : rtype) (value : stm)
    (picks : list rpick) (body : stm) : option chk :=
  match rprog inputs item value picks body with
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

Lemma has_rname_absent : forall name items,
  has_rname name items = false -> ~ In name (map rfname items).
Proof.
  intros name items.
  induction items as [|item rest IH]; intros absent found.
  - contradiction.
  - simpl in absent.
    apply orb_false_iff in absent as [head tail].
    simpl in found.
    destruct found as [same | found].
    + subst.
      rewrite Nat.eqb_refl in head.
      discriminate.
    + apply (IH tail found).
Qed.

Lemma rnames_ok : forall items,
  rnames_b items = true -> NoDup (map rfname items).
Proof.
  induction items as [|item rest IH]; intros accepted.
  - constructor.
  - simpl in accepted.
    apply andb_true_iff in accepted as [head tail].
    constructor.
    + apply has_rname_absent.
      apply negb_true_iff in head.
      exact head.
    + apply IH.
      exact tail.
Qed.

Lemma rdecl_unique_b : forall item,
  rdecl_b item = true -> rnames_b (rfields item) = true.
Proof.
  intros item accepted.
  unfold rdecl_b in accepted.
  destruct (rfields item) as [|field rest] eqn:fields; try discriminate.
  destruct (rdata item) as [data |] eqn:made; try discriminate.
  apply andb_true_iff in accepted as [head _].
  apply andb_true_iff in head as [_ names].
  exact names.
Qed.

Theorem rdecl_names : forall item,
  rdecl_b item = true -> NoDup (map rfname (rfields item)).
Proof.
  intros item accepted.
  apply rnames_ok.
  apply rdecl_unique_b.
  exact accepted.
Qed.

Lemma data_type_b : forall item,
  decl_b item = true -> dtype_b item = true.
Proof.
  intros item accepted.
  unfold decl_b in accepted.
  destruct (dctors item) as [|ctor rest] eqn:ctors; try discriminate.
  apply andb_true_iff in accepted as [_ typed].
  exact typed.
Qed.

Theorem rdecl_type : forall item,
  rdecl_b item = true ->
  exists typ, rtype_t item = Some typ /\ ty_b typ = true.
Proof.
  intros item accepted.
  unfold rdecl_b in accepted.
  destruct (rfields item) as [|field rest] eqn:fields; try discriminate.
  destruct (rdata item) as [data |] eqn:made; try discriminate.
  apply andb_true_iff in accepted as [_ data_ok].
  unfold rtype_t.
  rewrite made.
  pose proof (data_type_b data data_ok) as valid.
  unfold dtype_b in valid.
  destruct (dtype_t data) as [typ |] eqn:formed; try discriminate.
  exists typ.
  split; try reflexivity.
  destruct (ty_b typ) eqn:typed; try discriminate.
  reflexivity.
Qed.

Lemma item_name : forall field item,
  Nat.eqb (rfname field) (riname item) = true -> riname item = rfname field.
Proof.
  intros field item same.
  apply Nat.eqb_eq in same.
  symmetry.
  exact same.
Qed.

Theorem items_names : forall fields items,
  items_b fields items = true -> map riname items = map rfname fields.
Proof.
  induction fields as [|field rest IH]; intros items accepted;
    destruct items as [|item tail]; simpl in accepted; try discriminate.
  - reflexivity.
  - apply andb_true_iff in accepted as [head next].
    simpl.
    rewrite (item_name field item head).
    rewrite (IH tail next).
    reflexivity.
Qed.

Lemma pick_name : forall field item,
  pick_b field item = true -> rpname item = rfname field.
Proof.
  intros field item accepted.
  unfold pick_b in accepted.
  apply andb_true_iff in accepted as [head _].
  apply andb_true_iff in head as [same _].
  apply Nat.eqb_eq in same.
  symmetry.
  exact same.
Qed.

Lemma pick_mode : forall field item,
  pick_b field item = true -> smul (rpbind item) = paym (rftyp field).
Proof.
  intros field item accepted.
  unfold pick_b in accepted.
  apply andb_true_iff in accepted as [_ mode].
  destruct (paym (rftyp field)), (smul (rpbind item));
    simpl in mode; try discriminate; reflexivity.
Qed.

Theorem picks_names : forall fields items,
  picks_b fields items = true -> map rpname items = map rfname fields.
Proof.
  induction fields as [|field rest IH]; intros items accepted;
    destruct items as [|item tail]; simpl in accepted; try discriminate.
  - reflexivity.
  - apply andb_true_iff in accepted as [head next].
    simpl.
    rewrite (pick_name field item head).
    rewrite (IH tail next).
    reflexivity.
Qed.

Theorem picks_modes : forall fields items,
  picks_b fields items = true ->
  map (fun item => smul (rpbind item)) items =
  map (fun field => paym (rftyp field)) fields.
Proof.
  induction fields as [|field rest IH]; intros items accepted;
    destruct items as [|item tail]; simpl in accepted; try discriminate.
  - reflexivity.
  - apply andb_true_iff in accepted as [head next].
    simpl.
    rewrite (pick_mode field item head).
    rewrite (IH tail next).
    reflexivity.
Qed.

Lemma has_bname_absent : forall name items,
  has_bname name items = false ->
  ~ In name (map (fun item => sname (rpbind item)) items).
Proof.
  intros name items.
  induction items as [|item rest IH]; intros absent found.
  - contradiction.
  - simpl in absent.
    apply orb_false_iff in absent as [head tail].
    simpl in found.
    destruct found as [same | found].
    + subst.
      rewrite Nat.eqb_refl in head.
      discriminate.
    + apply (IH tail found).
Qed.

Lemma bnames_ok : forall items,
  bnames_b items = true ->
  NoDup (map (fun item => sname (rpbind item)) items).
Proof.
  induction items as [|item rest IH]; intros accepted.
  - constructor.
  - simpl in accepted.
    apply andb_true_iff in accepted as [head tail].
    constructor.
    + apply has_bname_absent.
      apply negb_true_iff in head.
      exact head.
    + apply IH.
      exact tail.
Qed.

Lemma rsplit_accepts : forall item value picks body out,
  rsplit item value picks body = Some out ->
  picks_b (rfields item) picks = true /\ bnames_b picks = true.
Proof.
  intros item value picks body out accepted.
  unfold rsplit in accepted.
  destruct (rdecl_b item); try discriminate.
  destruct (picks_b (rfields item) picks && bnames_b picks)
    eqn:picks_ok; try discriminate.
  apply andb_true_iff in picks_ok.
  exact picks_ok.
Qed.

Theorem rsplit_fields : forall item value picks body out,
  rsplit item value picks body = Some out ->
  map rpname picks = map rfname (rfields item) /\
  map (fun pick => smul (rpbind pick)) picks =
    map (fun field => paym (rftyp field)) (rfields item) /\
  NoDup (map (fun pick => sname (rpbind pick)) picks).
Proof.
  intros item value picks body out accepted.
  pose proof (rsplit_accepts item value picks body out accepted)
    as [fields_ok binds_ok].
  repeat split.
  - apply picks_names.
    exact fields_ok.
  - apply picks_modes.
    exact fields_ok.
  - apply bnames_ok.
    exact binds_ok.
Qed.

Lemma rprog_accepts : forall inputs item value picks body binds core,
  rprog inputs item value picks body = Some (binds, core) ->
  rdecl_b item = true /\
  picks_b (rfields item) picks = true /\
  bnames_b picks = true.
Proof.
  intros inputs item value picks body binds core accepted.
  unfold rprog in accepted.
  destruct (Nat.leb (length inputs) pmax); try discriminate.
  destruct (rdecl_b item) eqn:decl_ok; try discriminate.
  destruct (picks_b (rfields item) picks && bnames_b picks)
    eqn:picks_ok; try discriminate.
  apply andb_true_iff in picks_ok as [fields_ok binds_ok].
  repeat split; assumption.
Qed.

Theorem rprog_fields : forall inputs item value picks body binds core,
  rprog inputs item value picks body = Some (binds, core) ->
  map rpname picks = map rfname (rfields item) /\
  map (fun pick => smul (rpbind pick)) picks =
    map (fun field => paym (rftyp field)) (rfields item).
Proof.
  intros inputs item value picks body binds core accepted.
  pose proof (rprog_accepts inputs item value picks body binds core accepted)
    as [_ [fields_ok _]].
  split.
  - apply picks_names.
    exact fields_ok.
  - apply picks_modes.
    exact fields_ok.
Qed.

Theorem rprog_binds : forall inputs item value picks body binds core,
  rprog inputs item value picks body = Some (binds, core) ->
  NoDup (map (fun pick => sname (rpbind pick)) picks).
Proof.
  intros inputs item value picks body binds core accepted.
  pose proof (rprog_accepts inputs item value picks body binds core accepted)
    as [_ [_ binds_ok]].
  apply bnames_ok.
  exact binds_ok.
Qed.

Theorem rpcheck_sound : forall inputs item value picks body typ row cost next,
  rpcheck inputs item value picks body = Some (typ, row, cost, next) ->
  exists binds core gamma,
    rprog inputs item value picks body = Some (binds, core) /\
    opens [] binds = Some gamma /\
    check gamma core typ row cost next /\
    doneb next = true.
Proof.
  intros inputs item value picks body typ row cost next accepted.
  unfold rpcheck in accepted.
  destruct (rprog inputs item value picks body) as [[binds core] |]
    eqn:lowered; try discriminate.
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

Theorem rpcheck_complete : forall inputs item value picks body binds core gamma
    typ row cost next,
  rprog inputs item value picks body = Some (binds, core) ->
  opens [] binds = Some gamma ->
  check gamma core typ row cost next ->
  doneb next = true ->
  rpcheck inputs item value picks body = Some (typ, row, cost, next).
Proof.
  intros inputs item value picks body binds core gamma typ row cost next
    lowered opened checked done.
  unfold rpcheck.
  rewrite lowered, opened.
  rewrite (checkb_complete gamma core typ row cost next checked).
  rewrite done.
  reflexivity.
Qed.