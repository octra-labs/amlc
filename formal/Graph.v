(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.

Require Import Lim.

Import ListNotations.

Definition fprime : Z := Z.sub (Z.pow 2 127) 1.

Inductive sign : Type := Pos | Neg.

Inductive rule : Type :=
| Base
| Prod (left right : nat).

Record layer : Type := Layer {
  ltag : nat;
  lrule : rule
}.

Record edge : Type := Edge {
  elayer : nat;
  eindex : nat;
  esign : sign;
  eweight : list Z;
  esigma : list bool
}.

Record cfg : Type := Cfg {
  gbasis : nat;
  gslots : nat;
  gsigma : nat;
  gedge_cap : Z
}.

Record graph : Type := Graph {
  glayers : list layer;
  gedges : list edge
}.

Record ginfo : Type := Ginfo {
  gout : graph;
  gmerged : bool;
  glayer_count : nat;
  gedge_count : nat;
  gremoved : nat
}.

Definition sign_b (left right : sign) : bool :=
  match left, right with
  | Pos, Pos | Neg, Neg => true
  | _, _ => false
  end.

Definition sign_rank (value : sign) : nat :=
  match value with Pos => 0 | Neg => 1 end.

Definition field_b (value : Z) : bool :=
  Z.leb 0 value && Z.ltb value fprime.

Definition cfg_b (value : cfg) : bool :=
  fit (gbasis value) && negb (Nat.eqb (gbasis value) 0)
    && fit (gslots value) && negb (Nat.eqb (gslots value) 0)
    && fit (gsigma value) && negb (Nat.eqb (gsigma value) 0)
    && Z.ltb 0 (gedge_cap value).

Definition layer_b (id : nat) (value : layer) : bool :=
  fit (ltag value) &&
  match lrule value with
  | Base => true
  | Prod pa pb => Nat.ltb pa id && Nat.ltb pb id
  end.

Fixpoint layers_b_at (id : nat) (values : list layer) : bool :=
  match values with
  | [] => true
  | value :: rest => layer_b id value && layers_b_at (S id) rest
  end.

Definition edge_b (config : cfg) (layer_count : nat) (value : edge) : bool :=
  Nat.ltb (elayer value) layer_count
    && Nat.ltb (eindex value) (gbasis config)
    && Nat.eqb (length (eweight value)) (gslots config)
    && Nat.eqb (length (esigma value)) (gsigma config)
    && forallb field_b (eweight value).

Fixpoint edges_b (config : cfg) (layer_count : nat)
    (values : list edge) : bool :=
  match values with
  | [] => true
  | value :: rest =>
      edge_b config layer_count value && edges_b config layer_count rest
  end.

Definition graph_b (config : cfg) (value : graph) : bool :=
  cfg_b config
    && layers_b_at 0 (glayers value)
    && edges_b config (length (glayers value)) (gedges value).

Definition fadd (left right : Z) : Z := Z.modulo (Z.add left right) fprime.

Fixpoint wadd (left right : list Z) : list Z :=
  match left, right with
  | [], [] => []
  | x :: xs, y :: ys => fadd x y :: wadd xs ys
  | _, _ => []
  end.

Fixpoint sxor (left right : list bool) : list bool :=
  match left, right with
  | [], [] => []
  | x :: xs, y :: ys => xorb x y :: sxor xs ys
  | _, _ => []
  end.

Fixpoint wnz (values : list Z) : bool :=
  match values with
  | [] => false
  | value :: rest => negb (Z.eqb value 0) || wnz rest
  end.

Fixpoint snz (values : list bool) : bool :=
  match values with
  | [] => false
  | value :: rest => value || snz rest
  end.

Definition edge_nz (value : edge) : bool :=
  wnz (eweight value) || snz (esigma value).

Record cell : Type := Cell {
  clayer : nat;
  cindex : nat;
  csign : sign;
  cweight : list Z;
  csigma : list bool
}.

Definition cell_of (value : edge) : cell :=
  Cell (elayer value) (eindex value) (esign value)
    (eweight value) (esigma value).

Definition edge_of (value : cell) : edge :=
  Edge (clayer value) (cindex value) (csign value)
    (cweight value) (csigma value).

Definition key_eqb (value : edge) (item : cell) : bool :=
  Nat.eqb (elayer value) (clayer item)
    && Nat.eqb (eindex value) (cindex item)
    && sign_b (esign value) (csign item).

Definition key_ltb (value : edge) (item : cell) : bool :=
  Nat.ltb (elayer value) (clayer item)
    || (Nat.eqb (elayer value) (clayer item)
      && (Nat.ltb (eindex value) (cindex item)
        || (Nat.eqb (eindex value) (cindex item)
          && Nat.ltb (sign_rank (esign value)) (sign_rank (csign item))))).

Fixpoint put (value : edge) (items : list cell) : list cell :=
  match items with
  | [] => [cell_of value]
  | item :: rest =>
      if key_eqb value item then
        Cell (clayer item) (cindex item) (csign item)
          (wadd (cweight item) (eweight value))
          (sxor (csigma item) (esigma value)) :: rest
      else if key_ltb value item then cell_of value :: item :: rest
      else item :: put value rest
  end.

Definition cells (values : list edge) : list cell :=
  fold_left (fun items value => put value items) values [].

Definition cell_nz (value : cell) : bool :=
  wnz (cweight value) || snz (csigma value).

Definition merge (values : list edge) : list edge :=
  map edge_of (filter cell_nz (cells values)).

Fixpoint set_true (pos : nat) (values : list bool) : list bool :=
  match pos, values with
  | _, [] => []
  | 0, _ :: rest => true :: rest
  | S next, value :: rest => value :: set_true next rest
  end.

Fixpoint mark_edges (values : list edge) (live : list bool) : list bool :=
  match values with
  | [] => live
  | value :: rest => mark_edges rest (set_true (elayer value) live)
  end.

Fixpoint mark_layers_at (id : nat) (values : list layer)
    (live : list bool) : list bool :=
  match values with
  | [] => live
  | value :: rest =>
      let next :=
        if nth id live false then
          match lrule value with
          | Base => live
          | Prod pa pb => set_true pb (set_true pa live)
          end
        else live in
      mark_layers_at (S id) rest next
  end.

Definition mark_layers (values : list layer) (live : list bool) : list bool :=
  mark_layers_at 0 values live.

Fixpoint close (fuel : nat) (values : list layer)
    (live : list bool) : list bool :=
  match fuel with
  | 0 => live
  | S rest => close rest values (mark_layers values live)
  end.

Fixpoint before (pos : nat) (values : list bool) : nat :=
  match pos, values with
  | 0, _ => 0
  | _, [] => 0
  | S next, value :: rest => (if value then 1 else 0) + before next rest
  end.

Definition rank (pos : nat) (values : list bool) : option nat :=
  if nth pos values false then Some (before pos values) else None.

Definition map_layer (live : list bool) (value : layer) : option layer :=
  match lrule value with
  | Base => Some value
  | Prod pa pb =>
      match rank pa live, rank pb live with
      | Some lnext, Some rnext => Some (Layer (ltag value) (Prod lnext rnext))
      | _, _ => None
      end
  end.

Fixpoint map_layers (all live : list bool) (values : list layer)
    : option (list layer) :=
  match live, values with
  | [], [] => Some []
  | keep :: lrest, value :: rest =>
      match map_layers all lrest rest with
      | None => None
      | Some tail =>
          if keep then
            match map_layer all value with
            | Some next => Some (next :: tail)
            | None => None
            end
          else Some tail
      end
  | _, _ => None
  end.

Definition map_edge (live : list bool) (value : edge) : option edge :=
  match rank (elayer value) live with
  | Some id => Some (Edge id (eindex value) (esign value)
      (eweight value) (esigma value))
  | None => None
  end.

Fixpoint map_edges (live : list bool) (values : list edge)
    : option (list edge) :=
  match values with
  | [] => Some []
  | value :: rest =>
      match map_edge live value, map_edges live rest with
      | Some next, Some tail => Some (next :: tail)
      | _, _ => None
      end
  end.

Definition compact (layers : list layer) (edges : list edge) : option graph :=
  let first := mark_edges edges (repeat false (length layers)) in
  let live := close (length layers) layers first in
  match map_layers live live layers, map_edges live edges with
  | Some lout, Some eout => Some (Graph lout eout)
  | _, _ => None
  end.

Definition need_merge (config : cfg) (values : list edge) : bool :=
  Z.ltb (gedge_cap config) (Z.of_nat (length values)).

Theorem need_merge_exact : forall config values,
  need_merge config values = true <->
  (gedge_cap config < Z.of_nat (length values))%Z.
Proof.
  intros config values. unfold need_merge. apply Z.ltb_lt.
Qed.

Definition norm (config : cfg) (value : graph) : option ginfo :=
  if graph_b config value then
    let joined := need_merge config (gedges value) in
    let edges := if joined then merge (gedges value) else gedges value in
    match compact (glayers value) edges with
    | Some out =>
        if graph_b config out then
          Some (Ginfo out joined (length (glayers out)) (length (gedges out))
            (length (glayers value) - length (glayers out)))
        else None
    | None => None
    end
  else None.

Inductive normR (config : cfg) (value : graph) : ginfo -> Prop :=
| NRun : forall (joined : bool) (edges : list edge) (out : graph),
    graph_b config value = true ->
    joined = need_merge config (gedges value) ->
    edges = (if joined then merge (gedges value) else gedges value) ->
    compact (glayers value) edges = Some out ->
    graph_b config out = true ->
    normR config value
      (Ginfo out joined (length (glayers out)) (length (gedges out))
        (length (glayers value) - length (glayers out))).

Theorem norm_sound : forall config value out,
  norm config value = Some out -> normR config value out.
Proof.
  intros config value out H. unfold norm in H.
  destruct (graph_b config value) eqn:Hv; try discriminate.
  remember (need_merge config (gedges value)) as joined eqn:Hj.
  remember (if joined then merge (gedges value) else gedges value) as edges
    eqn:He.
  destruct (compact (glayers value) edges) as [graph_out |] eqn:Hc;
    try discriminate.
  destruct (graph_b config graph_out) eqn:Ho; try discriminate.
  inversion H. subst. eapply NRun; eauto.
Qed.

Theorem norm_complete : forall config value out,
  normR config value out -> norm config value = Some out.
Proof.
  intros config value out H.
  induction H as [joined edges graph_out Hv Hj He Hc Ho].
  unfold norm. rewrite Hv, <- Hj, <- He, Hc, Ho. reflexivity.
Qed.

Theorem norm_unique : forall config value left right,
  normR config value left -> normR config value right -> left = right.
Proof.
  intros config value left right Hl Hr.
  pose proof (norm_complete _ _ _ Hl) as El.
  pose proof (norm_complete _ _ _ Hr) as Er.
  rewrite El in Er. inversion Er. reflexivity.
Qed.

Theorem norm_valid : forall config value info,
  norm config value = Some info -> graph_b config (gout info) = true.
Proof.
  intros config value info H.
  apply norm_sound in H.
  induction H as [joined edges graph_out Hv Hj He Hc Ho].
  exact Ho.
Qed.

Theorem norm_counts : forall config value info,
  norm config value = Some info ->
  glayer_count info = length (glayers (gout info)) /\
  gedge_count info = length (gedges (gout info)) /\
  gremoved info = length (glayers value) - length (glayers (gout info)).
Proof.
  intros config value info H.
  apply norm_sound in H.
  induction H as [joined edges graph_out Hv Hj He Hc Ho].
  repeat split; reflexivity.
Qed.

Lemma edge_of_nz : forall value,
  edge_nz (edge_of value) = cell_nz value.
Proof. intros value. reflexivity. Qed.

Lemma edge_map_nz : forall values,
  forallb edge_nz (map edge_of values) = forallb cell_nz values.
Proof.
  intros values. induction values as [|value rest IH].
  - reflexivity.
  - cbn [map forallb]. rewrite IH. reflexivity.
Qed.

Theorem merge_nonzero : forall values,
  forallb edge_nz (merge values) = true.
Proof.
  assert (Hfilter : forall items,
    forallb cell_nz (filter cell_nz items) = true).
  {
    intros items. induction items as [|item rest IH].
    - reflexivity.
    - cbn [filter]. destruct (cell_nz item) eqn:Hz.
      + cbn [forallb]. rewrite Hz. exact IH.
      + exact IH.
  }
  intros values. unfold merge.
  rewrite edge_map_nz.
  apply Hfilter.
Qed.