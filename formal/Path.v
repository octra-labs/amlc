(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Strings.String.

Require Import Uni.
Require Import Comp.
Require Import Src.
Require Import Emit.
Require Import Mach.
Require Import Lex.
Require Import Smap.
Require Import Live.
Require Import Feed.

Import ListNotations.

Inductive kind : Type :=
| KLoad
| KMove
| KPlus
| KTimes
| KQuotient
| KRemainder
| KNegate
| KAbsolute
| KSame
| KLess
| KGreater
| KJoin
| KMinus
| KSize
| KSlice
| KJump
| KJumpIf
| KMark
| KNoop
| KStop.

Fixpoint kinds (value : Mach.code) : list kind :=
  match value with
  | Mach.Done => []
  | Mach.Push _ rest => KLoad :: kinds rest
  | Mach.Void rest | Mach.Empty _ rest => kinds rest
  | Mach.Get _ form rest =>
      repeat KMove (Mach.shape_width form) ++ kinds rest
  | Mach.Plus rest => KPlus :: kinds rest
  | Mach.Minus rest => KMinus :: kinds rest
  | Mach.Times rest => KTimes :: kinds rest
  | Mach.Quot rest => KQuotient :: kinds rest
  | Mach.Rem rest => KRemainder :: kinds rest
  | Mach.Negate rest => KNegate :: kinds rest
  | Mach.Absolute rest => KAbsolute :: kinds rest
  | Mach.Same rest => KSame :: kinds rest
  | Mach.Order RLt rest => KLess :: kinds rest
  | Mach.Order RLe rest => KGreater :: KLoad :: KSame :: kinds rest
  | Mach.Order RGt rest => KGreater :: kinds rest
  | Mach.Order RGe rest => KLess :: KLoad :: KSame :: kinds rest
  | Mach.Join rest => KJoin :: kinds rest
  | Mach.Clip _ rest => KLoad :: KLoad :: KSlice :: kinds rest
  | Mach.Skip _ rest => KLoad :: KSize :: KMinus :: KSlice :: kinds rest
  | Mach.Duo rest | Mach.First rest | Mach.Second rest | Mach.Cons rest
  | Mach.Append rest | Mach.Pick _ rest | Mach.Unhead rest => kinds rest
  | Mach.Left rest | Mach.Right rest => KLoad :: kinds rest
  | Mach.Effect _ body rest => KNoop :: kinds body ++ kinds rest
  | Mach.Scope _ body rest => kinds body ++ kinds rest
  | Mach.Scope2 _ _ body rest => kinds body ++ kinds rest
  | Mach.Iter len _ _ body rest =>
      List.concat (repeat (kinds body) len) ++ kinds rest
  | Mach.Choice _ yes _ no form rest =>
      KJumpIf :: kinds no ++ repeat KMove (Mach.shape_width form)
      ++ [KJump; KMark] ++ kinds yes
      ++ repeat KMove (Mach.shape_width form) ++ [KMark] ++ kinds rest
  | Mach.Fork form yes no rest =>
      KJumpIf :: kinds no ++ repeat KMove (Mach.shape_width form)
      ++ [KJump; KMark] ++ kinds yes
      ++ repeat KMove (Mach.shape_width form) ++ [KMark] ++ kinds rest
  end.

Definition plan (value : Mach.code) : list kind :=
  kinds value ++ [KMove; KStop].

Record frame : Type := Frame {
  fpc : nat;
  fkind : kind;
  fspan : span;
  fslots : list Live.slot
}.

Fixpoint join (pc : nat) (ops : list kind) (spans : list span)
    (rows : list (list Live.slot)) : option (list frame) :=
  match ops, spans, rows with
  | [], [], [] => Some []
  | op :: op_rest, spot :: spot_rest, row :: row_rest =>
      match join (S pc) op_rest spot_rest row_rest with
      | Some rest => Some (Frame pc op spot row :: rest)
      | None => None
      end
  | _, _, _ => None
  end.

Record path : Type := Path {
  pcode : Mach.code;
  pframes : list frame;
  pshape : ty;
  prow : list atom;
  peff : list atom;
  puse : res;
  pres : res;
  pdepth : nat;
  pout : lit
}.

Inductive cause : Type :=
| PSource
| PFeed
| PMachine
| PSlots
| PMap
| PRun.

Inductive reply : Type :=
| POk : path -> reply
| PNo : cause -> reply.

Definition make (source : string) (spans : list span) : reply :=
  match Src.compile source with
  | None => PNo PSource
  | Some image =>
      match Mach.image_code image with
      | None => PNo PMachine
      | Some artifact =>
          match Live.analyze (Mach.acode artifact) with
          | None => PNo PSlots
          | Some rows =>
              if Live.live_b rows then
                if Smap.map_b spans then
                  match join 0 (plan (Mach.acode artifact)) spans rows with
                  | None => PNo PMap
                  | Some frames =>
                      match run_fuel (rsteps (Comp.icost image)) []
                          (Comp.iterm image) with
                      | Uni.Done out [] =>
                          POk (Path (Mach.acode artifact) frames
                            (Comp.ityp image) (Comp.irow image) (rp out)
                            (used out) (Comp.ires image)
                            (rdepth (Comp.ires image)) (Mach.aresult artifact))
                      | _ => PNo PRun
                      end
                  end
                else PNo PMap
              else PNo PSlots
          end
      end
  end.

Definition make_feed (source : string) (values : list value)
    (spans : list span) : reply :=
  match Src.compile source with
  | None => PNo PSource
  | Some image =>
      match Feed.load (Comp.iins image) values with
      | None => PNo PFeed
      | Some sigma =>
          match Mach.image_feed_code image values with
          | None => PNo PMachine
          | Some artifact =>
              match Live.analyze (Mach.acode artifact) with
              | None => PNo PSlots
              | Some rows =>
                  if Live.live_b rows then
                    if Smap.map_b spans then
                      match join 0 (plan (Mach.acode artifact)) spans rows with
                      | None => PNo PMap
                      | Some frames =>
                          match run_fuel (rsteps (Comp.icost image)) sigma
                              (Comp.iterm image) with
                          | Uni.Done out _ =>
                              POk (Path (Mach.acode artifact) frames
                                (Comp.ityp image) (Comp.irow image) (rp out)
                                (used out) (Comp.ires image)
                                (rdepth (Comp.ires image))
                                (Mach.aresult artifact))
                          | _ => PNo PRun
                          end
                      end
                    else PNo PMap
                  else PNo PSlots
              end
          end
      end
  end.

Definition replay (value : path) : option (list lit) :=
  Mach.replay (pcode value).

Theorem make_sound : forall source spans value,
  make source spans = POk value ->
  exists image artifact core rows,
    Src.compile source = Some image /\
    Mach.image_code image = Some artifact /\
    Live.analyze (Mach.acode artifact) = Some rows /\
    Live.live_b rows = true /\
    Smap.map_b spans = true /\
    join 0 (plan (Mach.acode artifact)) spans rows =
      Some (pframes value) /\
    run_fuel (rsteps (Comp.icost image)) [] (Comp.iterm image) =
      Uni.Done core [] /\
    pcode value = Mach.acode artifact /\
    pshape value = Comp.ityp image /\
    prow value = Comp.irow image /\
    peff value = rp core /\
    puse value = used core /\
    pres value = Comp.ires image /\
    pdepth value = rdepth (Comp.ires image) /\
    pout value = Mach.aresult artifact /\
    rep (Comp.ityp image) (rv core) (pout value) /\
    replay value = Some [pout value].
Proof.
  intros source spans value accepted.
  unfold make in accepted.
  destruct (Src.compile source) as [image |] eqn:compiled; try discriminate.
  destruct (Mach.image_code image) as [artifact |] eqn:coded;
    try discriminate.
  destruct (Live.analyze (Mach.acode artifact)) as [rows |] eqn:live;
    try discriminate.
  destruct (Live.live_b rows) eqn:rows_ok; try discriminate.
  destruct (Smap.map_b spans) eqn:map_ok; try discriminate.
  destruct (join 0 (plan (Mach.acode artifact)) spans rows)
    as [frames |] eqn:joined; try discriminate.
  destruct (run_fuel (rsteps (Comp.icost image)) [] (Comp.iterm image))
    as [core state | reason | |] eqn:ran; try discriminate.
  destruct state as [|entry state]; try discriminate.
  inversion accepted; subst value.
  pose proof (Mach.image_code_sound image artifact coded) as image_ok.
  destruct image_ok as [_ [_ [emitted [_ [replayed route]]]]].
  pose proof (Emit.emit_sound image (Mach.aresult artifact) emitted)
    as result_ok.
  destruct result_ok as [_ [_ [seen [seen_run [_ represented]]]]].
  rewrite ran in seen_run.
  inversion seen_run; subst seen.
  exists image, artifact, core, rows.
  repeat split; try assumption; try reflexivity.
Qed.

Corollary make_replay : forall source spans value,
  make source spans = POk value ->
  replay value = Some [pout value].
Proof.
  intros source spans value accepted.
  destruct (make_sound source spans value accepted)
    as [image [artifact [core [rows facts]]]].
  repeat match type of facts with
  | _ /\ _ => destruct facts as [_ facts]
  end.
  exact facts.
Qed.

Theorem make_unique : forall source spans left right,
  make source spans = POk left ->
  make source spans = POk right ->
  left = right.
Proof.
  intros source spans left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Theorem make_feed_sound : forall source values spans value,
  make_feed source values spans = POk value ->
  exists image sigma artifact core final rows,
    Src.compile source = Some image /\
    Feed.load (Comp.iins image) values = Some sigma /\
    Mach.image_feed_code image values = Some artifact /\
    Live.analyze (Mach.acode artifact) = Some rows /\
    Live.live_b rows = true /\
    Smap.map_b spans = true /\
    join 0 (plan (Mach.acode artifact)) spans rows =
      Some (pframes value) /\
    run_fuel (rsteps (Comp.icost image)) sigma (Comp.iterm image) =
      Uni.Done core final /\
    pcode value = Mach.acode artifact /\
    pshape value = Comp.ityp image /\
    prow value = Comp.irow image /\
    peff value = rp core /\
    puse value = used core /\
    pres value = Comp.ires image /\
    pdepth value = rdepth (Comp.ires image) /\
    pout value = Mach.aresult artifact /\
    rep (Comp.ityp image) (rv core) (pout value) /\
    replay value = Some [pout value].
Proof.
  intros source values spans value accepted.
  unfold make_feed in accepted.
  destruct (Src.compile source) as [image |] eqn:compiled; try discriminate.
  destruct (Feed.load (Comp.iins image) values) as [sigma |]
    eqn:loaded; try discriminate.
  destruct (Mach.image_feed_code image values) as [artifact |]
    eqn:coded; try discriminate.
  destruct (Live.analyze (Mach.acode artifact)) as [rows |]
    eqn:live; try discriminate.
  destruct (Live.live_b rows) eqn:rows_ok; try discriminate.
  destruct (Smap.map_b spans) eqn:map_ok; try discriminate.
  destruct (join 0 (plan (Mach.acode artifact)) spans rows)
    as [frames |] eqn:joined; try discriminate.
  destruct (run_fuel (rsteps (Comp.icost image)) sigma (Comp.iterm image))
    as [core state | reason | |] eqn:ran; try discriminate.
  inversion accepted; subst value.
  pose proof (Mach.image_feed_code_sound image values artifact coded)
    as image_ok.
  destruct image_ok as
    [no_effects [found_sigma [term [found_core [found_state
      [found_load [closed [found_run [no_plan
        [represented [formed [replayed route]]]]]]]]]]]].
  rewrite loaded in found_load.
  inversion found_load; subst found_sigma.
  rewrite ran in found_run.
  inversion found_run; subst found_core found_state.
  exists image, sigma, artifact, core, state, rows.
  repeat split; try assumption; try reflexivity.
Qed.

Corollary make_feed_replay : forall source values spans value,
  make_feed source values spans = POk value ->
  replay value = Some [pout value].
Proof.
  intros source values spans value accepted.
  destruct (make_feed_sound source values spans value accepted)
    as [image [sigma [artifact [core [final [rows facts]]]]]].
  repeat match type of facts with
  | _ /\ _ => destruct facts as [_ facts]
  end.
  exact facts.
Qed.

Theorem make_feed_unique : forall source values spans left right,
  make_feed source values spans = POk left ->
  make_feed source values spans = POk right ->
  left = right.
Proof.
  intros source values spans left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.