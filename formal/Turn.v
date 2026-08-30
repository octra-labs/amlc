(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.

Require Import Uni.
Require Import Dec.
Require Import Lim.
Require Import Low.
Require Import Host.
Require Import Sess.
Require Import Sbin.
Require Import Bin.
Require Import Ser.
Require Import Pbin.
Require Import Root.

Import ListNotations.

Fixpoint value_inputs (inputs : list bits) : option (list value) :=
  match inputs with
  | [] => Some []
  | first :: rest =>
      match dec_value first, value_inputs rest with
      | Some value, Some values => Some (value :: values)
      | _, _ => None
      end
  end.

Fixpoint token_inputs (inputs : list bits) : option (list stok) :=
  match inputs with
  | [] => Some []
  | first :: rest =>
      match dec_tok first, token_inputs rest with
      | Some token, Some tokens => Some (token :: tokens)
      | _, _ => None
      end
  end.

Fixpoint live_keys (entries : list sentry) : list Host.key :=
  match entries with
  | [] => []
  | entry :: rest =>
      if elive entry then (ekind entry, eid entry) :: live_keys rest
      else live_keys rest
  end.

Fixpoint keys_eqb (left right : list Host.key) : bool :=
  match left, right with
  | [], [] => true
  | first :: more, second :: rest =>
      Host.key_eqb first second && keys_eqb more rest
  | _, _ => false
  end.

Definition token_keys (tokens : list stok) : list Host.key :=
  Host.key_sort (map (fun token => (tkind token, tid token)) tokens).

Fixpoint token_pop (key : Host.key) (tokens : list stok)
    : option (stok * list stok) :=
  match tokens with
  | [] => None
  | token :: rest =>
      if Host.key_eqb key (tkind token, tid token) then Some (token, rest)
      else
        match token_pop key rest with
        | Some (found, more) => Some (found, token :: more)
        | None => None
        end
  end.

Fixpoint entry_set (key : Host.key) (rev : nat) (live : bool)
    (entries : list sentry) : option (list sentry) :=
  match entries with
  | [] => None
  | entry :: rest =>
      if Host.key_eqb key (ekind entry, eid entry) then
        Some (Entry (ekind entry) (eid entry) rev live :: rest)
      else
        match entry_set key rev live rest with
        | Some more => Some (entry :: more)
        | None => None
        end
  end.

Definition take_entry (domain : scope) (entries : list sentry)
    (token : stok) (keep : bool) : option (list sentry * option stok) :=
  if scope_eqb domain (tscope token) then
    match entry_get entries (tkind token) (tid token) with
    | Some (rev, true) =>
        if Nat.eqb rev (trev token) then
          let key := (tkind token, tid token) in
          if keep then
            if fit (S rev) then
              match entry_set key (S rev) true entries with
              | Some next => Some (next, Some (Tok domain (tkind token)
                  (tid token) (S rev)))
              | None => None
              end
            else None
          else
            match entry_set key rev false entries with
            | Some next => Some (next, None)
            | None => None
            end
        else None
    | _ => None
    end
  else None.

Fixpoint advance (domain : scope) (entries : list sentry)
    (tokens : list stok) (output keys : list Host.key) {struct keys}
    : option (list sentry * list stok) :=
  match keys with
  | [] =>
      match tokens with
      | [] => Some (entries, [])
      | _ => None
      end
  | key :: rest =>
      match token_pop key tokens with
      | Some (token, more) =>
          match take_entry domain entries token (Host.key_mem key output) with
          | Some (next, fresh) =>
              match advance domain next more output rest with
              | Some (final, made) =>
                  Some (final,
                    match fresh with Some item => item :: made | None => made end)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  end.

Definition root_scope (domain : scope) (root : list nat) : scope :=
  Scope (schain domain) (sprog domain) root.

Definition root_view (view : sview) (root : list nat) : sview :=
  View (root_scope (vscope view) root) (ventries view).

Definition root_token (root : list nat) (token : stok) : stok :=
  Tok (root_scope (tscope token) root) (tkind token) (tid token) (trev token).

Definition prior_view (view : sview) (prior : list nat) : sview :=
  View (root_scope (vscope view) prior) (ventries view).

Definition ready (binds : list bind) (term : tm) (values : list value)
    : option (env * res) :=
  match opens [] binds, Host.load [] binds values with
  | Some gamma, Some sigma =>
      match checkb gamma term with
      | Some (_, _, cost, next) =>
          if doneb next then Some (sigma, cost) else None
      | None => None
      end
  | _, _ => None
  end.

Definition verify (program : bits) (prior : list nat) (state : bits)
    (digest : list nat) : bool :=
  match dec_view state with
  | Some view =>
      if prior_b digest &&
        bytes_eqb (sprog (vscope view)) (Root.image program) &&
        bytes_eqb (sroot (vscope view)) digest then
        match Root.root program prior (enc_view (prior_view view prior)) with
        | Some found => bytes_eqb found digest
        | None => false
        end
      else false
  | None => false
  end.

Record result : Type := Result {
  reval : run;
  rstate : bits;
  rtokens : list bits;
  rroot : list nat
}.

Definition turn (program : bits) (prior : list nat) (state : bits)
    (inputs tokens : list bits) : option result :=
  match Root.link program prior state, value_inputs inputs,
    token_inputs tokens with
  | Some ((binds, term), view), Some values, Some supplied =>
      if keys_eqb (token_keys supplied) (live_keys (ventries view)) then
        match ready binds term values, Host.caps values with
        | Some (sigma, cost), Some input_keys =>
            match run_fuel (rsteps cost) sigma term with
            | Done out _ =>
                match Host.cap (rv out) with
                | Some output_keys =>
                    if Host.key_sub output_keys input_keys then
                      match advance (vscope view) (ventries view) supplied
                        output_keys (Host.key_sort input_keys) with
                      | Some (entries, fresh) =>
                          let next := View (vscope view) entries in
                          if view_b next then
                            let open_bits := enc_view next in
                            match Root.root program prior open_bits with
                            | Some digest =>
                                let sealed := root_view next digest in
                                let sealed_tokens := map (root_token digest) fresh in
                                if view_b sealed && forallb tok_b sealed_tokens then
                                  let state_bits := enc_view sealed in
                                  let token_bits := map enc_tok sealed_tokens in
                                  let value := Result out state_bits token_bits digest in
                                  if verify program prior state_bits digest then
                                    Some value
                                  else None
                                else None
                            | None => None
                            end
                          else None
                      | None => None
                      end
                    else None
                | None => None
                end
            | Rejected _ | OutOfFuel | Stuck => None
            end
        | _, _ => None
        end
      else None
  | _, _, _ => None
  end.

Theorem turn_det : forall program prior state inputs tokens left right,
  turn program prior state inputs tokens = Some left ->
  turn program prior state inputs tokens = Some right ->
  left = right.
Proof.
  intros program prior state inputs tokens left right first second.
  rewrite first in second.
  inversion second.
  reflexivity.
Qed.

Theorem verify_state : forall program prior state digest,
  verify program prior state digest = true ->
  exists view,
    dec_view state = Some view /\
    sprog (vscope view) = Root.image program /\
    sroot (vscope view) = digest /\
    Root.root program prior (enc_view (prior_view view prior)) = Some digest.
Proof.
  intros program prior state digest accepted.
  unfold verify in accepted.
  destruct (dec_view state) as [view |] eqn:decoded; try discriminate.
  destruct (prior_b digest &&
    bytes_eqb (sprog (vscope view)) (Root.image program) &&
    bytes_eqb (sroot (vscope view)) digest) eqn:scope_ok; try discriminate.
  destruct (Root.root program prior (enc_view (prior_view view prior)))
    as [found |] eqn:root_ok; try discriminate.
  apply andb_true_iff in scope_ok.
  destruct scope_ok as [pair_ok root_scope_ok].
  apply andb_true_iff in pair_ok.
  destruct pair_ok as [_ prog_scope_ok].
  apply bytes_eqb_eq in prog_scope_ok, root_scope_ok.
  apply bytes_eqb_eq in accepted.
  subst found.
  exists view.
  repeat split; assumption.
Qed.

Theorem turn_verify : forall program prior state inputs tokens value,
  turn program prior state inputs tokens = Some value ->
  verify program prior (rstate value) (rroot value) = true.
Proof.
  intros program prior state inputs tokens value accepted.
  unfold turn in accepted.
  repeat match goal with
  | H : context [match ?item with _ => _ end] |- _ =>
      destruct item eqn:?; try discriminate
  | H : context [if ?flag then _ else _] |- _ =>
      destruct flag eqn:?; try discriminate
  end.
  inversion accepted; subst.
  assumption.
Qed.

Theorem turn_eval : forall program prior state inputs tokens value,
  turn program prior state inputs tokens = Some value ->
  exists binds term view values supplied sigma cost final,
    Root.link program prior state = Some ((binds, term), view) /\
    value_inputs inputs = Some values /\
    token_inputs tokens = Some supplied /\
    ready binds term values = Some (sigma, cost) /\
    run_fuel (rsteps cost) sigma term = Done (reval value) final.
Proof.
  intros program prior state inputs tokens value accepted.
  unfold turn in accepted.
  destruct (Root.link program prior state) as [[[binds term] view] |]
    eqn:linked; try discriminate.
  destruct (value_inputs inputs) as [values |] eqn:values_ok; try discriminate.
  destruct (token_inputs tokens) as [supplied |] eqn:tokens_ok; try discriminate.
  destruct (keys_eqb (token_keys supplied) (live_keys (ventries view)))
    eqn:live_ok; try discriminate.
  destruct (ready binds term values) as [[sigma cost] |] eqn:ready_ok;
    try discriminate.
  destruct (Host.caps values) as [input_keys |] eqn:input_ok; try discriminate.
  destruct (run_fuel (rsteps cost) sigma term) as [out final | reason | |] eqn:ran;
    try discriminate.
  repeat match goal with
  | H : context [match ?item with _ => _ end] |- _ =>
      destruct item eqn:?; try discriminate
  | H : context [if ?flag then _ else _] |- _ =>
      destruct flag eqn:?; try discriminate
  end.
  inversion accepted; subst.
  exists binds, term, view, values, supplied, sigma, cost, final.
  repeat split; assumption.
Qed.

Corollary turn_state : forall program prior state inputs tokens value,
  turn program prior state inputs tokens = Some value ->
  exists view,
    dec_view (rstate value) = Some view /\
    sprog (vscope view) = Root.image program /\
    sroot (vscope view) = rroot value /\
    Root.root program prior (enc_view (prior_view view prior)) =
      Some (rroot value).
Proof.
  intros program prior state inputs tokens value accepted.
  apply verify_state.
  apply turn_verify with (state := state) (inputs := inputs) (tokens := tokens).
  exact accepted.
Qed.