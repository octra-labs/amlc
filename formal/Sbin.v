(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.

Require Import Sess.
Require Import Lim.
Require Import Bin.
Require Import Ser.

Import ListNotations.

Definition raw_code (value : list nat) : code := list_code CNum value.
Definition raw_get (input : code) : option (list nat) := list_get num_get input.

Definition scope_code (value : scope) : code :=
  CTag 0 (CCons (raw_code (schain value))
    (CCons (raw_code (sprog value))
      (CCons (raw_code (sroot value)) CNil))).

Definition scope_get (input : code) : option scope :=
  match input with
  | CTag 0 (CCons chain (CCons prog (CCons root CNil))) =>
      match raw_get chain, raw_get prog, raw_get root with
      | Some chain', Some prog', Some root' =>
          let value := Scope chain' prog' root' in
          if scope_b value then Some value else None
      | _, _, _ => None
      end
  | _ => None
  end.

Lemma raw_get_code : forall value, raw_get (raw_code value) = Some value.
Proof.
  intros value.
  apply list_get_code.
  intros item _.
  apply num_get_code.
Qed.

Lemma scope_get_code : forall value,
  scope_b value = true ->
  scope_get (scope_code value) = Some value.
Proof.
  intros [chain prog root] valid.
  simpl.
  rewrite !raw_get_code.
  cbn [scope_b schain sprog sroot] in valid.
  rewrite valid.
  reflexivity.
Qed.

Definition tok_code (value : stok) : code :=
  CTag 1 (CCons (scope_code (tscope value))
    (CCons (CNum (tkind value))
      (CCons (CNum (tid value)) (CCons (CNum (trev value)) CNil)))).

Definition tok_get (input : code) : option stok :=
  match input with
  | CTag 1 (CCons domain
      (CCons (CNum kind) (CCons (CNum id) (CCons (CNum rev) CNil)))) =>
      match scope_get domain with
      | Some scope' =>
          if fit kind && fit id && fit rev then Some (Tok scope' kind id rev)
          else None
      | None => None
      end
  | _ => None
  end.

Definition tok_b (value : stok) : bool :=
  scope_b (tscope value) && fit (tkind value) && fit (tid value) &&
  fit (trev value).

Lemma tok_get_code : forall value,
  tok_b value = true ->
  tok_get (tok_code value) = Some value.
Proof.
  intros [[chain prog root] kind id rev] valid.
  unfold tok_b in valid.
  cbn [tscope tkind tid trev scope_b schain sprog sroot] in valid.
  repeat rewrite andb_true_iff in valid.
  destruct valid as [[[scope_ok kind_ok] id_ok] rev_ok].
  simpl.
  rewrite !raw_get_code.
  rewrite scope_ok, kind_ok, id_ok, rev_ok.
  reflexivity.
Qed.

Definition sentry_code (value : sentry) : code :=
  CTag 2 (CCons (CNum (ekind value))
    (CCons (CNum (eid value))
      (CCons (CNum (erev value))
        (CCons (CNum (if elive value then 1 else 0)) CNil)))).

Definition sentry_get (input : code) : option sentry :=
  match input with
  | CTag 2 (CCons (CNum kind)
      (CCons (CNum id) (CCons (CNum rev) (CCons (CNum live) CNil)))) =>
      if fit kind && fit id && fit rev then
        match live with
        | 0 => Some (Entry kind id rev false)
        | 1 => Some (Entry kind id rev true)
        | _ => None
        end
      else None
  | _ => None
  end.

Lemma sentry_get_code : forall value,
  entry_b value = true ->
  sentry_get (sentry_code value) = Some value.
Proof.
  intros [kind id rev live] valid.
  cbn [entry_b ekind eid erev] in valid.
  apply andb_true_iff in valid.
  destruct valid as [pair_ok rev_ok].
  apply andb_true_iff in pair_ok.
  destruct pair_ok as [kind_ok id_ok].
  destruct live.
  - change (fit kind = true) in kind_ok.
    change (fit id = true) in id_ok.
    change (fit rev = true) in rev_ok.
    change
      ((if fit kind && fit id && fit rev then
         Some (Entry kind id rev true)
       else None) = Some (Entry kind id rev true)).
    rewrite kind_ok, id_ok, rev_ok.
    reflexivity.
  - change (fit kind = true) in kind_ok.
    change (fit id = true) in id_ok.
    change (fit rev = true) in rev_ok.
    change
      ((if fit kind && fit id && fit rev then
         Some (Entry kind id rev false)
       else None) = Some (Entry kind id rev false)).
    rewrite kind_ok, id_ok, rev_ok.
    reflexivity.
Qed.

Definition sview_code (value : sview) : code :=
  CTag 3 (CCons (scope_code (vscope value))
    (CCons (list_code sentry_code (ventries value)) CNil)).

Definition sview_get (input : code) : option sview :=
  match input with
  | CTag 3 (CCons domain (CCons entries CNil)) =>
      match scope_get domain, list_get sentry_get entries with
      | Some domain', Some entries' =>
          let value := View domain' entries' in
          if view_b value then Some value else None
      | _, _ => None
      end
  | _ => None
  end.

Lemma sview_get_code : forall value,
  view_b value = true ->
  sview_get (sview_code value) = Some value.
Proof.
  intros [domain entries] valid.
  unfold view_b in valid.
  cbn [vscope ventries] in valid.
  apply andb_true_iff in valid.
  destruct valid as [domain_ok entries_ok].
  unfold entries_b in entries_ok.
  repeat rewrite andb_true_iff in entries_ok.
  destruct entries_ok as [[length_ok items_ok] order_ok].
  unfold sview_code, sview_get.
  cbn [vscope ventries].
  rewrite scope_get_code by exact domain_ok.
  rewrite list_get_code.
  - assert (whole : view_b (View domain entries) = true).
    {
      unfold view_b.
      cbn [vscope ventries].
      rewrite domain_ok.
      unfold entries_b.
      rewrite length_ok, items_ok, order_ok.
      reflexivity.
    }
    change
      ((if view_b (View domain entries) then Some (View domain entries)
        else None) = Some (View domain entries)).
    rewrite whole.
    reflexivity.
  - intros entry present.
    apply sentry_get_code.
    rewrite forallb_forall in items_ok.
    apply items_ok.
    exact present.
Qed.

Definition enc_scope := enc scope_code.
Definition dec_scope := dec scope_code scope_get.
Definition enc_tok := enc tok_code.
Definition dec_tok := dec tok_code tok_get.
Definition enc_view := enc sview_code.
Definition dec_view := dec sview_code sview_get.

Theorem scope_decode_encode : forall value,
  scope_b value = true ->
  dec_scope (enc_scope value) = Some value.
Proof.
  intros value valid.
  apply dec_enc.
  apply scope_get_code.
  exact valid.
Qed.

Theorem scope_encode_decode : forall input value,
  dec_scope input = Some value -> enc_scope value = input.
Proof.
  apply enc_dec.
Qed.

Theorem tok_decode_encode : forall value,
  tok_b value = true ->
  dec_tok (enc_tok value) = Some value.
Proof.
  intros value valid.
  apply dec_enc.
  apply tok_get_code.
  exact valid.
Qed.

Theorem tok_encode_decode : forall input value,
  dec_tok input = Some value -> enc_tok value = input.
Proof.
  apply enc_dec.
Qed.

Theorem view_decode_encode : forall value,
  view_b value = true ->
  dec_view (enc_view value) = Some value.
Proof.
  intros value valid.
  apply dec_enc.
  apply sview_get_code.
  exact valid.
Qed.

Theorem view_encode_decode : forall input value,
  dec_view input = Some value -> enc_view value = input.
Proof.
  apply enc_dec.
Qed.