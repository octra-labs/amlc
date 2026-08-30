(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Uni.
Require Import Dec.
Require Import Lim.
Require Import Bin.
Require Import Ser.
Require Import Low.
Require Import Rule.
Require Import Pbin.

Import ListNotations.

Definition atom_tag (value : atom) : nat :=
  match value with
  | ARead _ => 0
  | AWrite _ => 1
  | AEmit _ => 2
  | AFail _ => 3
  | AClose _ => 4
  end.

Definition atom_nat (value : atom) : nat :=
  match value with
  | ARead id | AWrite id | AEmit id | AFail id | AClose id => id
  end.

Definition atom_dec (left right : atom) : {left = right} + {left <> right}.
Proof.
  decide equality.
  all: apply Nat.eq_dec.
Defined.

Definition atom_eqb (left right : atom) : bool :=
  if atom_dec left right then true else false.

Definition atom_ltb (left right : atom) : bool :=
  Nat.ltb (atom_tag left) (atom_tag right)
    || (Nat.eqb (atom_tag left) (atom_tag right)
      && Nat.ltb (atom_nat left) (atom_nat right)).

Fixpoint row_add (value : atom) (row : list atom) : list atom :=
  match row with
  | [] => [value]
  | first :: rest =>
      if atom_eqb value first then row
      else if atom_ltb value first then value :: row
      else first :: row_add value rest
  end.

Fixpoint row_norm (row : list atom) : list atom :=
  match row with
  | [] => []
  | first :: rest => row_add first (row_norm rest)
  end.

Lemma atom_eqb_eq : forall left right,
  atom_eqb left right = true -> left = right.
Proof.
  intros left right same.
  unfold atom_eqb in same.
  destruct (atom_dec left right); try discriminate.
  assumption.
Qed.

Lemma atom_eqb_refl : forall value,
  atom_eqb value value = true.
Proof.
  intros value.
  unfold atom_eqb.
  destruct (atom_dec value value); try contradiction.
  reflexivity.
Qed.

Lemma row_add_in : forall needle value row,
  In needle (row_add value row) <-> needle = value \/ In needle row.
Proof.
  intros needle value row.
  induction row as [|first rest IH]; simpl.
  - intuition congruence.
  - destruct (atom_eqb value first) eqn:same.
    + apply atom_eqb_eq in same. subst. simpl. intuition congruence.
    + destruct (atom_ltb value first); simpl.
      * intuition congruence.
      * rewrite IH. intuition congruence.
Qed.

Theorem row_norm_in : forall needle row,
  In needle (row_norm row) <-> In needle row.
Proof.
  intros needle row.
  induction row as [|first rest IH]; simpl.
  - tauto.
  - rewrite row_add_in, IH. intuition congruence.
Qed.

Definition nat_list_dec (left right : list nat) : {left = right} + {left <> right} :=
  list_eq_dec Nat.eq_dec left right.

Definition nat_list_eqb (left right : list nat) : bool :=
  if nat_list_dec left right then true else false.

Definition row_dec (left right : list atom) : {left = right} + {left <> right} :=
  list_eq_dec atom_dec left right.

Definition row_eqb (left right : list atom) : bool :=
  if row_dec left right then true else false.

Definition res_dec (left right : res) : {left = right} + {left <> right}.
Proof.
  decide equality.
  all: apply Nat.eq_dec.
Defined.

Definition res_eqb (left right : res) : bool :=
  if res_dec left right then true else false.

Lemma nat_list_eqb_eq : forall left right,
  nat_list_eqb left right = true -> left = right.
Proof.
  intros left right same.
  unfold nat_list_eqb in same.
  destruct (nat_list_dec left right); try discriminate.
  assumption.
Qed.

Lemma nat_list_eqb_refl : forall value,
  nat_list_eqb value value = true.
Proof.
  intros value.
  unfold nat_list_eqb.
  destruct (nat_list_dec value value); try contradiction.
  reflexivity.
Qed.

Lemma ty_eqb_eq : forall left right,
  ty_eqb left right = true -> left = right.
Proof.
  intros left right same.
  unfold ty_eqb in same.
  destruct (ty_dec left right); try discriminate.
  assumption.
Qed.

Lemma ty_eqb_refl : forall value,
  ty_eqb value value = true.
Proof.
  intros value.
  unfold ty_eqb.
  destruct (ty_dec value value); try contradiction.
  reflexivity.
Qed.

Lemma row_eqb_eq : forall left right,
  row_eqb left right = true -> left = right.
Proof.
  intros left right same.
  unfold row_eqb in same.
  destruct (row_dec left right); try discriminate.
  assumption.
Qed.

Lemma row_eqb_refl : forall value,
  row_eqb value value = true.
Proof.
  intros value.
  unfold row_eqb.
  destruct (row_dec value value); try contradiction.
  reflexivity.
Qed.

Lemma res_eqb_eq : forall left right,
  res_eqb left right = true -> left = right.
Proof.
  intros left right same.
  unfold res_eqb in same.
  destruct (res_dec left right); try discriminate.
  assumption.
Qed.

Lemma res_eqb_refl : forall value,
  res_eqb value value = true.
Proof.
  intros value.
  unfold res_eqb.
  destruct (res_dec value value); try contradiction.
  reflexivity.
Qed.

Record cert : Type := Cert {
  cprog : program;
  crule : list nat;
  ctyp : ty;
  crow : list atom;
  cres : res
}.

Definition rule_code (values : list nat) : code := list_code CNum values.

Definition rule_get (input : code) : option (list nat) :=
  match list_get num_get input with
  | Some values => if Nat.eqb (length values) 12 then Some values else None
  | None => None
  end.

Lemma rule_get_code : forall values,
  length values = 12 -> rule_get (rule_code values) = Some values.
Proof.
  intros values size.
  unfold rule_get, rule_code.
  rewrite list_get_code.
  - rewrite size, Nat.eqb_refl. reflexivity.
  - intros value _. apply num_get_code.
Qed.

Definition cert_code (value : cert) : code :=
  CTag 0 (CCons (prog_code (cprog value))
    (CCons (rule_code (crule value))
      (CCons (ty_code (ctyp value))
        (CCons (list_code atom_code (crow value))
          (CCons (res_code (cres value)) CNil))))).

Definition cert_b (value : cert) : bool :=
  prog_b (cprog value)
    && Nat.eqb (length (crule value)) 12
    && Nat.leb (length (put_code (cert_code value))) (rstr local).

Definition cert_get (input : code) : option cert :=
  match input with
  | CTag 0 (CCons prog (CCons rule (CCons typ
      (CCons row (CCons cost CNil))))) =>
      match prog_get prog, rule_get rule, ty_get typ,
          list_get atom_get row, res_get cost with
      | Some prog, Some rule, Some typ, Some row, Some cost =>
          let value := Cert prog rule typ row cost in
          if cert_b value then Some value else None
      | _, _, _, _, _ => None
      end
  | _ => None
  end.

Lemma cert_get_code : forall value,
  cert_b value = true -> cert_get (cert_code value) = Some value.
Proof.
  intros [prog rule typ row cost] valid.
  change (prog_b prog
    && Nat.eqb (length rule) 12
    && Nat.leb (length (put_code
      (cert_code (Cert prog rule typ row cost)))) (rstr local) = true) in valid.
  repeat rewrite andb_true_iff in valid.
  destruct valid as [[prog_ok rule_ok] size_ok].
  apply Nat.eqb_eq in rule_ok.
  assert (cert_ok : cert_b (Cert prog rule typ row cost) = true).
  {
    change (prog_b prog
      && Nat.eqb (length rule) 12
      && Nat.leb (length (put_code
        (cert_code (Cert prog rule typ row cost)))) (rstr local) = true).
    rewrite prog_ok, rule_ok, Nat.eqb_refl, size_ok. reflexivity.
  }
  cbn [cert_get cert_code cprog crule ctyp crow cres].
  rewrite prog_get_code, rule_get_code, ty_get_code, list_get_code, res_get_code.
  - rewrite cert_ok. reflexivity.
  - intros action _. apply atom_get_code.
  - exact rule_ok.
  - exact prog_ok.
Qed.

Lemma cert_get_b : forall input value,
  cert_get input = Some value -> cert_b value = true.
Proof.
  intros input value accepted.
  unfold cert_get in accepted.
  destruct input; try discriminate.
  destruct n; try discriminate.
  destruct input; try discriminate.
  destruct input2; try discriminate.
  destruct input2_2; try discriminate.
  destruct input2_2_2; try discriminate.
  destruct input2_2_2_2; try discriminate.
  destruct input2_2_2_2_2; try discriminate.
  destruct (prog_get input1); try discriminate.
  destruct (rule_get input2_1); try discriminate.
  destruct (ty_get input2_2_1); try discriminate.
  destruct (list_get atom_get input2_2_2_1); try discriminate.
  destruct (res_get input2_2_2_2_1); try discriminate.
  destruct (cert_b (Cert p l t l0 r)) eqn:valid; try discriminate.
  inversion accepted. subst. exact valid.
Qed.

Definition enc_cert (value : cert) : option bits :=
  if cert_b value then Some (enc cert_code value) else None.

Definition dec_cert : bits -> option cert := dec cert_code cert_get.

Theorem cert_decode_encode : forall value input,
  enc_cert value = Some input -> dec_cert input = Some value.
Proof.
  intros value input encoded.
  unfold enc_cert in encoded.
  destruct (cert_b value) eqn:valid; try discriminate.
  inversion encoded; subst input.
  unfold dec_cert.
  apply dec_enc.
  apply cert_get_code.
  exact valid.
Qed.

Theorem cert_encode_decode : forall input value,
  dec_cert input = Some value -> enc_cert value = Some input.
Proof.
  intros input value decoded.
  assert (valid : cert_b value = true).
  {
    unfold dec_cert, dec in decoded.
    destruct (get_code input) as [shape |] eqn:shape_ok; try discriminate.
    destruct (cert_get shape) as [found |] eqn:value_ok; try discriminate.
    destruct (code_eqb (cert_code found) shape) eqn:exact; try discriminate.
    inversion decoded; subst.
    eapply cert_get_b. exact value_ok.
  }
  pose proof (enc_dec cert cert_code cert_get input value decoded) as exact.
  unfold enc_cert.
  rewrite valid, exact.
  reflexivity.
Qed.

Lemma dec_cert_b : forall input value,
  dec_cert input = Some value -> cert_b value = true.
Proof.
  intros input value decoded.
  unfold dec_cert, dec in decoded.
  destruct (get_code input) as [shape |] eqn:shape_ok; try discriminate.
  destruct (cert_get shape) as [found |] eqn:value_ok; try discriminate.
  destruct (code_eqb (cert_code found) shape) eqn:exact; try discriminate.
  inversion decoded; subst.
  eapply cert_get_b. exact value_ok.
Qed.

Lemma cert_b_prog : forall value,
  cert_b value = true -> prog_b (cprog value) = true.
Proof.
  intros value valid.
  unfold cert_b in valid.
  repeat rewrite andb_true_iff in valid.
  tauto.
Qed.

Lemma rid_vals_length : forall id, length (rid_vals id) = 12.
Proof.
  intros [version limits].
  reflexivity.
Qed.

Definition issue (rules : list rule) (epoch : nat) (value : program)
    : option bits :=
  if prog_b value then
    let '(binds, term) := value in
    match opens [] binds with
    | Some gamma =>
        match rcheck rules epoch gamma term with
        | Some (id, (typ, row, cost, next)) =>
            if doneb next then
              enc_cert (Cert value (rid_vals id) typ (row_norm row) cost)
            else None
        | None => None
        end
    | None => None
    end
  else None.

Definition verifyb (rules : list rule) (epoch : nat) (input : bits) : bool :=
  match dec_cert input with
  | Some value =>
      let '(binds, term) := cprog value in
      match opens [] binds with
      | Some gamma =>
          match rcheck rules epoch gamma term with
          | Some (id, (typ, row, cost, next)) =>
              doneb next
                && nat_list_eqb (crule value) (rid_vals id)
                && ty_eqb (ctyp value) typ
                && row_eqb (crow value) (row_norm row)
                && res_eqb (cres value) cost
          | None => false
          end
      | None => false
      end
  | None => false
  end.

Theorem issue_verify : forall rules epoch value input,
  issue rules epoch value = Some input -> verifyb rules epoch input = true.
Proof.
  intros rules epoch [binds term] input issued.
  change ((if prog_b (binds, term) then
    match opens [] binds with
    | Some gamma =>
        match rcheck rules epoch gamma term with
        | Some (id, (typ, row, cost, next)) =>
            if doneb next then
              enc_cert
                (Cert (binds, term) (rid_vals id) typ (row_norm row) cost)
            else None
        | None => None
        end
    | None => None
    end
  else None) = Some input) in issued.
  destruct (prog_b (binds, term)) eqn:prog_ok; try discriminate.
  destruct (opens [] binds) as [gamma |] eqn:opened; try discriminate.
  destruct (rcheck rules epoch gamma term)
    as [[id [[[typ row] cost] next]] |] eqn:checked; try discriminate.
  destruct (doneb next) eqn:done; try discriminate.
  pose proof (cert_decode_encode _ _ issued) as decoded.
  unfold verifyb.
  rewrite decoded. cbn [cprog crule ctyp crow cres].
  rewrite opened, checked, done.
  rewrite nat_list_eqb_refl, ty_eqb_refl, row_eqb_refl, res_eqb_refl.
  reflexivity.
Qed.

Theorem issue_decode : forall rules epoch value input,
  issue rules epoch value = Some input ->
  exists id typ row cost,
    dec_cert input =
      Some (Cert value (rid_vals id) typ (row_norm row) cost).
Proof.
  intros rules epoch [binds term] input issued.
  change ((if prog_b (binds, term) then
    match opens [] binds with
    | Some gamma =>
        match rcheck rules epoch gamma term with
        | Some (id, (typ, row, cost, next)) =>
            if doneb next then
              enc_cert
                (Cert (binds, term) (rid_vals id) typ (row_norm row) cost)
            else None
        | None => None
        end
    | None => None
    end
  else None) = Some input) in issued.
  destruct (prog_b (binds, term)) eqn:prog_ok; try discriminate.
  destruct (opens [] binds) as [gamma |] eqn:opened; try discriminate.
  destruct (rcheck rules epoch gamma term)
    as [[id [[[typ row] cost] next]] |] eqn:checked; try discriminate.
  destruct (doneb next) eqn:done; try discriminate.
  exists id, typ, row, cost.
  eapply cert_decode_encode.
  exact issued.
Qed.

Theorem verify_sound : forall rules epoch input,
  verifyb rules epoch input = true ->
  exists value gamma id raw next active_rule,
    dec_cert input = Some value
      /\ opens [] (fst (cprog value)) = Some gamma
      /\ rcheck rules epoch gamma (snd (cprog value)) =
        Some (id, (ctyp value, raw, cres value, next))
      /\ crule value = rid_vals id
      /\ crow value = row_norm raw
      /\ doneb next = true
      /\ check gamma (snd (cprog value)) (ctyp value) raw (cres value) next
      /\ rsel epoch rules = Some active_rule
      /\ rrid active_rule = id
      /\ active epoch active_rule = true.
Proof.
  intros rules epoch input verified.
  unfold verifyb in verified.
  destruct (dec_cert input) as [value |] eqn:decoded; try discriminate.
  destruct (cprog value) as [binds term] eqn:prog.
  destruct (opens [] binds) as [gamma |] eqn:opened; try discriminate.
  destruct (rcheck rules epoch gamma term)
    as [[id [[[typ row] cost] next]] |] eqn:checked; try discriminate.
  repeat rewrite andb_true_iff in verified.
  destruct verified as [[[[done rule_ok] typ_ok] row_ok] res_ok].
  apply nat_list_eqb_eq in rule_ok.
  apply ty_eqb_eq in typ_ok.
  apply row_eqb_eq in row_ok.
  apply res_eqb_eq in res_ok.
  subst typ cost.
  pose proof (rcheck_sound rules epoch gamma term id (ctyp value) row
    (cres value) next checked) as sound.
  destruct (rcheck_active rules epoch gamma term id
    (ctyp value, row, cres value, next) checked)
    as [selected [selected_at [selected_id selected_active]]].
  exists value, gamma, id, row, next, selected.
  rewrite prog in *. simpl in *.
  repeat split; assumption.
Qed.

Theorem verify_issue : forall rules epoch input value,
  verifyb rules epoch input = true ->
  dec_cert input = Some value ->
  issue rules epoch (cprog value) = Some input.
Proof.
  intros rules epoch input [[binds term] cert_rule cert_typ cert_row cert_res]
    verified decoded.
  unfold verifyb in verified.
  rewrite decoded in verified.
  cbn [cprog crule ctyp crow cres] in verified.
  destruct (opens [] binds) as [gamma |] eqn:opened; try discriminate.
  destruct (rcheck rules epoch gamma term)
    as [[id [[[typ row] cost] next]] |] eqn:checked; try discriminate.
  repeat rewrite andb_true_iff in verified.
  destruct verified as [[[[done rule_ok] typ_ok] row_ok] res_ok].
  apply nat_list_eqb_eq in rule_ok.
  apply ty_eqb_eq in typ_ok.
  apply row_eqb_eq in row_ok.
  apply res_eqb_eq in res_ok.
  subst cert_rule cert_typ cert_row cert_res.
  pose proof (cert_encode_decode input
    (Cert (binds, term) (rid_vals id) typ (row_norm row) cost) decoded)
    as encoded.
  pose proof (dec_cert_b input
    (Cert (binds, term) (rid_vals id) typ (row_norm row) cost) decoded)
    as valid.
  pose proof (cert_b_prog _ valid) as prog_ok.
  cbn [cprog] in prog_ok.
  change ((if prog_b (binds, term) then
    match opens [] binds with
    | Some gamma =>
        match rcheck rules epoch gamma term with
        | Some (found, (found_ty, found_row, found_cost, found_next)) =>
            if doneb found_next then
              enc_cert (Cert (binds, term) (rid_vals found) found_ty
                (row_norm found_row) found_cost)
            else None
        | None => None
        end
    | None => None
    end
  else None) = Some input).
  rewrite prog_ok, opened, checked, done.
  exact encoded.
Qed.

Theorem verify_unique : forall rules epoch left right first second,
  verifyb rules epoch left = true ->
  verifyb rules epoch right = true ->
  dec_cert left = Some first ->
  dec_cert right = Some second ->
  cprog first = cprog second ->
  left = right.
Proof.
  intros rules epoch left right first second left_ok right_ok
    left_dec right_dec same_prog.
  pose proof (verify_issue rules epoch left first left_ok left_dec) as left_issue.
  pose proof (verify_issue rules epoch right second right_ok right_dec) as right_issue.
  rewrite same_prog in left_issue.
  rewrite right_issue in left_issue.
  inversion left_issue.
  reflexivity.
Qed.