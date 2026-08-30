(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.

Require Import Uni.
Require Import Dec.
Require Import Bin.
Require Import Ser.
Require Import Rule.
Require Import Mach.

Import ListNotations.

Record slot : Type := Slot {
  sid : nat;
  smul : mul;
  slive : bool
}.

Definition map_max : nat := 4 * rtm_nodes local + 2.

Definition mode (value : slot) : nat :=
  match smul value, slive value with
  | M0, false => 0
  | M0, true => 1
  | M1, false => 2
  | M1, true => 3
  | MM, false => 4
  | MM, true => 5
  end.

Definition mode_get (value : nat) : option (mul * bool) :=
  match value with
  | 0 => Some (M0, false)
  | 1 => Some (M0, true)
  | 2 => Some (M1, false)
  | 3 => Some (M1, true)
  | 4 => Some (MM, false)
  | 5 => Some (MM, true)
  | _ => None
  end.

Lemma mode_get_mode : forall value,
  mode_get (mode value) = Some (smul value, slive value).
Proof.
  intros [id mul live].
  destruct mul, live; reflexivity.
Qed.

Definition slot_b (value : slot) : bool :=
  Nat.leb (sid value) (rnat local)
    && match smul value, slive value with
       | M1, _ | MM, true => true
       | _, _ => false
       end.

Fixpoint has (id : nat) (values : list slot) : bool :=
  match values with
  | [] => false
  | value :: rest => Nat.eqb id (sid value) || has id rest
  end.

Fixpoint unique_b (values : list slot) : bool :=
  match values with
  | [] => true
  | value :: rest => negb (has (sid value) rest) && unique_b rest
  end.

Definition row_b (values : list slot) : bool :=
  Nat.leb (length values) (rtm_nodes local)
    && forallb slot_b values
    && unique_b values.

Definition live_b (values : list (list slot)) : bool :=
  negb (Nat.eqb (length values) 0)
    && Nat.leb (length values) map_max
    && forallb row_b values.

Definition slot_code (value : slot) : Bin.code :=
  CTag 0 (CCons (CNum (sid value))
    (CCons (CNum (mode value)) CNil)).

Definition slot_get (input : Bin.code) : option slot :=
  match input with
  | CTag 0 (CCons (CNum id) (CCons (CNum kind) CNil)) =>
      match mode_get kind with
      | Some (mul, live) => Some (Slot id mul live)
      | None => None
      end
  | _ => None
  end.

Lemma slot_get_code : forall value,
  slot_get (slot_code value) = Some value.
Proof.
  intros [id mul live].
  unfold slot_get, slot_code.
  simpl.
  rewrite mode_get_mode.
  reflexivity.
Qed.

Definition row_code (values : list slot) : Bin.code :=
  CTag 1 (list_code slot_code values).

Definition row_get (input : Bin.code) : option (list slot) :=
  match input with
  | CTag 1 body => list_get slot_get body
  | _ => None
  end.

Lemma row_get_code : forall values,
  row_get (row_code values) = Some values.
Proof.
  intros values.
  unfold row_get, row_code.
  apply list_get_code.
  intros value _.
  apply slot_get_code.
Qed.

Definition live_code (values : list (list slot)) : Bin.code :=
  CTag 2 (list_code row_code values).

Definition live_get (input : Bin.code) : option (list (list slot)) :=
  match input with
  | CTag 2 body => list_get row_get body
  | _ => None
  end.

Lemma live_get_code : forall values,
  live_get (live_code values) = Some values.
Proof.
  intros values.
  unfold live_get, live_code.
  apply list_get_code.
  intros value _.
  apply row_get_code.
Qed.

Definition live_bits (values : list (list slot)) : bits :=
  Ser.enc live_code values.

Definition live_fit (values : list (list slot)) : bool :=
  live_b values && Nat.leb (length (live_bits values)) (rstr local).

Definition enc_live (values : list (list slot)) : option bits :=
  if live_fit values then Some (live_bits values) else None.

Definition dec_live (input : bits) : option (list (list slot)) :=
  if Nat.leb (length input) (rstr local) then
    match Ser.dec live_code live_get input with
    | Some values => if live_b values then Some values else None
    | None => None
    end
  else None.

Theorem live_decode_encode : forall values,
  live_fit values = true ->
  dec_live (live_bits values) = Some values.
Proof.
  intros values fit.
  unfold live_fit in fit.
  apply andb_true_iff in fit.
  destruct fit as [valid size].
  unfold dec_live.
  rewrite size.
  unfold live_bits.
  rewrite Ser.dec_enc.
  - rewrite valid.
    reflexivity.
  - apply live_get_code.
Qed.

Theorem live_encode_decode : forall input values,
  dec_live input = Some values ->
  enc_live values = Some input.
Proof.
  intros input values accepted.
  unfold dec_live in accepted.
  destruct (Nat.leb (length input) (rstr local)) eqn:size;
    try discriminate.
  destruct (Ser.dec live_code live_get input) as [found |] eqn:decoded;
    try discriminate.
  destruct (live_b found) eqn:valid; try discriminate.
  inversion accepted; subst found.
  pose proof
    (Ser.enc_dec (list (list slot)) live_code live_get input values decoded)
    as exact.
  unfold enc_live, live_fit.
  rewrite valid.
  unfold live_bits.
  rewrite exact, size.
  reflexivity.
Qed.

Record cell : Type := Cell {
  cbind : bind;
  clive : bool
}.

Definition mul_b (left right : mul) : bool :=
  match left, right with
  | M0, M0 | M1, M1 | MM, MM => true
  | _, _ => false
  end.

Definition cell_b (left right : cell) : bool :=
  Nat.eqb (bid (cbind left)) (bid (cbind right))
    && mul_b (bmul (cbind left)) (bmul (cbind right))
    && ty_eqb (bty (cbind left)) (bty (cbind right))
    && Bool.eqb (clive left) (clive right).

Fixpoint cells_b (left right : list cell) : bool :=
  match left, right with
  | [], [] => true
  | lhead :: ltail, rhead :: rtail =>
      cell_b lhead rhead && cells_b ltail rtail
  | _, _ => false
  end.

Fixpoint cell_has (id : nat) (values : list cell) : bool :=
  match values with
  | [] => false
  | value :: rest =>
      Nat.eqb id (bid (cbind value)) || cell_has id rest
  end.

Fixpoint cell_take (id : nat) (left values : list cell)
    : option (list cell) :=
  match values with
  | [] => None
  | value :: rest =>
      if Nat.eqb id (bid (cbind value)) then
        match bmul (cbind value), clive value with
        | M1, true =>
            Some (rev_append left (Cell (cbind value) false :: rest))
        | MM, _ => Some (rev_append left (value :: rest))
        | _, _ => None
        end
      else cell_take id (value :: left) rest
  end.

Definition cell_open (binder : bind) (values : list cell)
    : option (list cell) :=
  if cell_has (bid binder) values then None
  else
    match bmul binder with
    | M1 | MM => Some (Cell binder true :: values)
    | M0 => None
    end.

Definition cell_close (binder : bind) (values : list cell)
    : option (list cell) :=
  match values with
  | value :: rest =>
      if Nat.eqb (bid binder) (bid (cbind value)) then
        match bmul binder, bmul (cbind value), clive value with
        | M1, M1, false | MM, MM, _ => Some rest
        | _, _, _ => None
        end
      else None
  | [] => None
  end.

Definition cell_row (values : list cell) : list slot :=
  map (fun value =>
    Slot (bid (cbind value)) (bmul (cbind value)) (clive value)) values.

Definition scan_state := (nat * list cell * list (list slot))%type.

Fixpoint scan (value : Mach.code) (depth : nat) (env : list cell)
    : option scan_state :=
  match value with
  | Mach.Done => Some (depth, env, [])
  | Mach.Push _ rest =>
      match scan rest (S depth) env with
      | Some (next_depth, next_env, rows) =>
          Some (next_depth, next_env, cell_row env :: rows)
      | None => None
      end
  | Mach.Void rest | Mach.Empty _ rest => scan rest (S depth) env
  | Mach.Get id form rest =>
      match cell_take id [] env with
      | Some used =>
          match scan rest (S depth) used with
          | Some (next_depth, next_env, rows) =>
              Some (next_depth, next_env,
                repeat (cell_row used) (Mach.shape_width form) ++ rows)
          | None => None
          end
      | None => None
      end
  | Mach.Plus rest | Mach.Minus rest | Mach.Times rest
  | Mach.Quot rest | Mach.Rem rest
  | Mach.Same rest | Mach.Join rest =>
      match depth with
      | S (S tail) =>
          match scan rest (S tail) env with
          | Some (next_depth, next_env, rows) =>
              Some (next_depth, next_env, cell_row env :: rows)
          | None => None
          end
      | _ => None
      end
  | Mach.Negate rest | Mach.Absolute rest =>
      match depth with
      | S tail =>
          match scan rest (S tail) env with
          | Some (next_depth, next_env, rows) =>
              Some (next_depth, next_env, cell_row env :: rows)
          | None => None
          end
      | 0 => None
      end
  | Mach.Clip _ rest =>
      match depth with
      | S tail =>
          match scan rest (S tail) env with
          | Some (next_depth, next_env, rows) =>
              Some (next_depth, next_env,
                cell_row env :: cell_row env :: cell_row env :: rows)
          | None => None
          end
      | 0 => None
      end
  | Mach.Skip _ rest =>
      match depth with
      | S tail =>
          match scan rest (S tail) env with
          | Some (next_depth, next_env, rows) =>
              Some (next_depth, next_env,
                cell_row env :: cell_row env :: cell_row env
                :: cell_row env :: rows)
          | None => None
          end
      | 0 => None
      end
  | Mach.Duo rest | Mach.Cons rest | Mach.Append rest =>
      match depth with
      | S (S tail) => scan rest (S tail) env
      | _ => None
      end
  | Mach.First rest | Mach.Second rest | Mach.Pick _ rest
  | Mach.Unhead rest =>
      match depth with
      | S tail => scan rest (S tail) env
      | 0 => None
      end
  | Mach.Effect _ rest =>
      match scan rest depth env with
      | Some (next_depth, next_env, rows) =>
          Some (next_depth, next_env, cell_row env :: rows)
      | None => None
      end
  | Mach.Scope binder body rest =>
      match depth with
      | S tail =>
          match cell_open binder env with
          | Some opened =>
              match scan body tail opened with
              | Some (body_depth, body_env, body_rows) =>
                  if Nat.eqb body_depth (S tail) then
                    match cell_close binder body_env with
                    | Some closed =>
                        match scan rest body_depth closed with
                        | Some (next_depth, next_env, rest_rows) =>
                            Some (next_depth, next_env,
                              body_rows ++ rest_rows)
                        | None => None
                        end
                    | None => None
                    end
                  else None
              | None => None
              end
          | None => None
          end
      | 0 => None
      end
  | Mach.Scope2 lhs rhs body rest =>
      match depth with
      | S tail =>
          match cell_open lhs env with
          | Some first =>
              match cell_open rhs first with
              | Some opened =>
                  match scan body tail opened with
                  | Some (body_depth, body_env, body_rows) =>
                      if Nat.eqb body_depth (S tail) then
                        match cell_close rhs body_env with
                        | Some last =>
                            match cell_close lhs last with
                            | Some closed =>
                                match scan rest body_depth closed with
                                | Some (next_depth, next_env, rest_rows) =>
                                    Some (next_depth, next_env,
                                      body_rows ++ rest_rows)
                                | None => None
                                end
                            | None => None
                            end
                        | None => None
                        end
                      else None
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | 0 => None
      end
  | Mach.Fork form yes no rest =>
      match depth with
      | S tail =>
          match scan no tail env, scan yes tail env with
          | Some (no_depth, no_env, no_rows),
              Some (yes_depth, yes_env, yes_rows) =>
              if Nat.eqb no_depth (S tail)
                  && Nat.eqb yes_depth (S tail)
                  && cells_b no_env yes_env then
                match scan rest (S tail) no_env with
                | Some (next_depth, next_env, rest_rows) =>
                    Some (next_depth, next_env,
                      [cell_row env] ++ no_rows
                      ++ repeat (cell_row no_env) (Mach.shape_width form)
                      ++ [cell_row no_env; cell_row env]
                      ++ yes_rows
                      ++ repeat (cell_row yes_env) (Mach.shape_width form)
                      ++ [cell_row no_env]
                      ++ rest_rows)
                | None => None
                end
              else None
          | _, _ => None
          end
      | 0 => None
      end
  end.

Definition slot_same (left right : slot) : bool :=
  Nat.eqb (sid left) (sid right)
    && mul_b (smul left) (smul right)
    && Bool.eqb (slive left) (slive right).

Fixpoint row_same (left right : list slot) : bool :=
  match left, right with
  | [], [] => true
  | lhead :: ltail, rhead :: rtail =>
      slot_same lhead rhead && row_same ltail rtail
  | _, _ => false
  end.

Fixpoint rows_same (left right : list (list slot)) : bool :=
  match left, right with
  | [], [] => true
  | lhead :: ltail, rhead :: rtail =>
      row_same lhead rhead && rows_same ltail rtail
  | _, _ => false
  end.

Lemma mul_b_eq : forall left right,
  mul_b left right = true -> left = right.
Proof.
  intros left right same.
  destruct left, right; simpl in same; try discriminate; reflexivity.
Qed.

Lemma slot_same_eq : forall left right,
  slot_same left right = true -> left = right.
Proof.
  intros [lid lmul llive] [rid rmul rlive] same.
  unfold slot_same in same.
  simpl in same.
  apply andb_true_iff in same.
  destruct same as [head lives].
  apply andb_true_iff in head.
  destruct head as [ids muls].
  apply Nat.eqb_eq in ids.
  apply mul_b_eq in muls.
  destruct llive, rlive; simpl in lives; try discriminate;
    subst rid rmul;
    reflexivity.
Qed.

Lemma row_same_eq : forall left right,
  row_same left right = true -> left = right.
Proof.
  induction left as [|lhead ltail IH]; destruct right as [|rhead rtail];
    simpl; intros same; try discriminate; try reflexivity.
  apply andb_true_iff in same.
  destruct same as [head tail].
  apply slot_same_eq in head.
  apply IH in tail.
  now subst.
Qed.

Lemma rows_same_eq : forall left right,
  rows_same left right = true -> left = right.
Proof.
  induction left as [|lhead ltail IH]; destruct right as [|rhead rtail];
    simpl; intros same; try discriminate; try reflexivity.
  apply andb_true_iff in same.
  destruct same as [head tail].
  apply row_same_eq in head.
  apply IH in tail.
  now subst.
Qed.

Inductive live_event : Type :=
| LEmit : live_event
| LOpen : bind -> live_event
| LUse : nat -> live_event
| LClose : bind -> live_event
| LSplit : live_event
| LElse : live_event
| LJoin : live_event.

Record branch_state : Type := BranchState {
  brbase : list cell;
  brout : option (list cell)
}.

Record path_state : Type := PathState {
  penv : list cell;
  pbranches : list branch_state;
  prows : list (list slot)
}.

Definition event_step (event : live_event) (state : path_state)
    : option path_state :=
  match event with
  | LEmit =>
      Some (PathState (penv state) (pbranches state)
        (cell_row (penv state) :: prows state))
  | LOpen binder =>
      match cell_open binder (penv state) with
      | Some next => Some (PathState next (pbranches state) (prows state))
      | None => None
      end
  | LUse id =>
      match cell_take id [] (penv state) with
      | Some next => Some (PathState next (pbranches state) (prows state))
      | None => None
      end
  | LClose binder =>
      match cell_close binder (penv state) with
      | Some next => Some (PathState next (pbranches state) (prows state))
      | None => None
      end
  | LSplit =>
      Some (PathState (penv state)
        (BranchState (penv state) None :: pbranches state) (prows state))
  | LElse =>
      match pbranches state with
      | BranchState base None :: rest =>
          Some (PathState base
            (BranchState base (Some (penv state)) :: rest) (prows state))
      | _ => None
      end
  | LJoin =>
      match pbranches state with
      | BranchState _ (Some expected) :: rest =>
          if cells_b (penv state) expected then
            Some (PathState expected rest (prows state))
          else None
      | _ => None
      end
  end.

Fixpoint event_run (events : list live_event) (state : path_state)
    : option path_state :=
  match events with
  | [] => Some state
  | event :: rest =>
      match event_step event state with
      | Some next => event_run rest next
      | None => None
      end
  end.

Fixpoint event_path (value : Mach.code) : list live_event :=
  match value with
  | Mach.Done => []
  | Mach.Push _ rest => LEmit :: event_path rest
  | Mach.Void rest | Mach.Empty _ rest => event_path rest
  | Mach.Get id form rest =>
      LUse id :: repeat LEmit (Mach.shape_width form) ++ event_path rest
  | Mach.Plus rest | Mach.Minus rest | Mach.Times rest
  | Mach.Quot rest | Mach.Rem rest | Mach.Negate rest | Mach.Absolute rest
  | Mach.Same rest | Mach.Join rest =>
      LEmit :: event_path rest
  | Mach.Clip _ rest => LEmit :: LEmit :: LEmit :: event_path rest
  | Mach.Skip _ rest =>
      LEmit :: LEmit :: LEmit :: LEmit :: event_path rest
  | Mach.Duo rest | Mach.First rest | Mach.Second rest | Mach.Cons rest
  | Mach.Append rest | Mach.Pick _ rest | Mach.Unhead rest => event_path rest
  | Mach.Effect _ rest => LEmit :: event_path rest
  | Mach.Scope binder body rest =>
      LOpen binder :: event_path body ++ LClose binder :: event_path rest
  | Mach.Scope2 lhs rhs body rest =>
      LOpen lhs :: LOpen rhs :: event_path body
      ++ LClose rhs :: LClose lhs :: event_path rest
  | Mach.Fork form yes no rest =>
      LEmit :: LSplit :: event_path no
      ++ repeat LEmit (Mach.shape_width form)
      ++ [LEmit; LElse; LEmit]
      ++ event_path yes
      ++ repeat LEmit (Mach.shape_width form)
      ++ [LJoin; LEmit]
      ++ event_path rest
  end.

Definition certify (value : Mach.code) : option (list (list slot)) :=
  match event_run (event_path value ++ [LEmit; LEmit])
      (PathState [] [] []) with
  | Some (PathState [] [] rows) => Some (rev rows)
  | _ => None
  end.

Inductive live_step : path_state -> live_event -> path_state -> Prop :=
| LiveStep : forall before event after,
    event_step event before = Some after ->
    live_step before event after.

Inductive live_steps : path_state -> list live_event -> path_state -> Prop :=
| LiveStepsNil : forall state, live_steps state [] state
| LiveStepsCons : forall before event next rest after,
    live_step before event next ->
    live_steps next rest after ->
    live_steps before (event :: rest) after.

Theorem event_run_sound : forall events before after,
  event_run events before = Some after ->
  live_steps before events after.
Proof.
  induction events as [|event rest IH]; intros before after ran.
  - simpl in ran.
    inversion ran; subst after.
    apply LiveStepsNil.
  - simpl in ran.
    destruct (event_step event before) as [next |] eqn:step;
      try discriminate.
    apply LiveStepsCons with next.
    + apply LiveStep.
      exact step.
    + apply IH.
      exact ran.
Qed.

Theorem certify_steps : forall value rows,
  certify value = Some rows ->
  exists state,
    live_steps (PathState [] [] [])
      (event_path value ++ [LEmit; LEmit]) state /\
    penv state = [] /\
    pbranches state = [] /\
    rows = rev (prows state).
Proof.
  intros value rows accepted.
  unfold certify in accepted.
  destruct (event_run (event_path value ++ [LEmit; LEmit])
    (PathState [] [] [])) as [[env branches seen] |] eqn:ran;
    try discriminate.
  destruct env as [|entry env]; try discriminate.
  destruct branches as [|branch branches]; try discriminate.
  inversion accepted; subst rows.
  exists (PathState [] [] seen).
  repeat split; try reflexivity.
  apply event_run_sound.
  exact ran.
Qed.

Definition analyze (value : Mach.code) : option (list (list slot)) :=
  match scan value 0 [], certify value with
  | Some (1, [], rows), Some checked =>
      let complete := rows ++ [[]; []] in
      if rows_same complete checked then Some complete else None
  | _, _ => None
  end.

Theorem analyze_cert : forall value rows,
  analyze value = Some rows ->
  certify value = Some rows.
Proof.
  intros value rows accepted.
  unfold analyze in accepted.
  destruct (scan value 0 []) as [[[depth env] prefix] |] eqn:ran;
    try discriminate.
  destruct depth as [|depth]; try discriminate.
  destruct depth as [|depth]; try discriminate.
  destruct env as [|entry env]; try discriminate.
  destruct (certify value) as [checked |] eqn:cert; try discriminate.
  destruct (rows_same (prefix ++ [[]; []]) checked) eqn:same;
    try discriminate.
  inversion accepted; subst rows.
  apply rows_same_eq in same.
  subst checked.
  reflexivity.
Qed.

Theorem analyze_steps : forall value rows,
  analyze value = Some rows ->
  exists state,
    live_steps (PathState [] [] [])
      (event_path value ++ [LEmit; LEmit]) state /\
    penv state = [] /\
    pbranches state = [] /\
    rows = rev (prows state).
Proof.
  intros value rows accepted.
  apply certify_steps.
  apply analyze_cert.
  exact accepted.
Qed.

Theorem analyze_shape : forall value rows,
  analyze value = Some rows ->
  exists prefix, rows = prefix ++ [[]; []].
Proof.
  intros value rows accepted.
  unfold analyze in accepted.
  destruct (scan value 0 []) as [[[depth env] prefix] |] eqn:ran;
    try discriminate.
  destruct depth as [|depth]; try discriminate.
  destruct depth as [|depth]; try discriminate.
  destruct env as [|entry env]; try discriminate.
  destruct (certify value) as [checked |]; try discriminate.
  destruct (rows_same (prefix ++ [[]; []]) checked); try discriminate.
  inversion accepted; subst rows.
  now exists prefix.
Qed.

Theorem analyze_final : forall value rows,
  analyze value = Some rows ->
  last rows [] = [].
Proof.
  intros value rows accepted.
  apply analyze_shape in accepted.
  destruct accepted as [prefix shape].
  subst rows.
  induction prefix as [|head tail IH].
  - reflexivity.
  - destruct tail as [|next rest].
    + reflexivity.
    + simpl in *.
      exact IH.
Qed.