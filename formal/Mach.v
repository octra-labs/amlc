(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Strings.String.

Require Import Uni.
Require Import Comp.
Require Import Src.
Require Import Emit.
Require Import Trace.
Require Import Rval.
Require Import Feed.

Import ListNotations.

Inductive shape : Type :=
| ShUnit : shape
| ShAtom : shape
| ShPair : shape -> shape -> shape
| ShVec : nat -> shape -> shape.

Inductive code : Type :=
| Done : code
| Push : lit -> code -> code
| Void : code -> code
| Get : nat -> shape -> code -> code
| Plus : code -> code
| Minus : code -> code
| Times : code -> code
| Quot : code -> code
| Rem : code -> code
| Negate : code -> code
| Absolute : code -> code
| Same : code -> code
| Join : code -> code
| Clip : nat -> code -> code
| Skip : nat -> code -> code
| Duo : code -> code
| First : code -> code
| Second : code -> code
| Empty : shape -> code -> code
| Cons : code -> code
| Append : code -> code
| Pick : nat -> code -> code
| Unhead : code -> code
| Effect : atom -> code -> code
| Scope : bind -> code -> code -> code
| Scope2 : bind -> bind -> code -> code -> code
| Fork : shape -> code -> code -> code -> code.

Fixpoint shape_eqb (left right : shape) : bool :=
  match left, right with
  | ShUnit, ShUnit | ShAtom, ShAtom => true
  | ShPair ll lr, ShPair rl rr => shape_eqb ll rl && shape_eqb lr rr
  | ShVec ln le, ShVec rn re => Nat.eqb ln rn && shape_eqb le re
  | _, _ => false
  end.

Fixpoint shape_of (typ : ty) : option shape :=
  match typ with
  | TUnit => Some ShUnit
  | TBool | TInt | TBytes _ => Some ShAtom
  | TVec len elem =>
      match shape_of elem with
      | Some item => Some (ShVec len item)
      | None => None
      end
  | TPair lhs rhs =>
      match shape_of lhs, shape_of rhs with
      | Some lhs, Some rhs => Some (ShPair lhs rhs)
      | _, _ => None
      end
  | TCap _ | TEnc _ _ | TSum _ _ => None
  end.

Fixpoint shape_width (value : shape) : nat :=
  match value with
  | ShUnit => 0
  | ShAtom => 1
  | ShPair lhs rhs => shape_width lhs + shape_width rhs
  | ShVec len elem => len * shape_width elem
  end.

Fixpoint shapes_eqb (left right : list shape) : bool :=
  match left, right with
  | [], [] => true
  | lhs :: lrest, rhs :: rrest =>
      shape_eqb lhs rhs && shapes_eqb lrest rrest
  | _, _ => false
  end.

Definition keep_shape (tail after : list shape) : option shape :=
  match after with
  | value :: rest => if shapes_eqb rest tail then Some value else None
  | [] => None
  end.

Fixpoint shape_run (value : code) (stack : list shape)
    : option (list shape) :=
  match value with
  | Done => Some stack
  | Push _ rest => shape_run rest (ShAtom :: stack)
  | Void rest => shape_run rest (ShUnit :: stack)
  | Get _ form rest => shape_run rest (form :: stack)
  | Plus rest | Minus rest | Times rest | Quot rest | Rem rest
  | Same rest | Join rest =>
      match stack with
      | ShAtom :: ShAtom :: tail => shape_run rest (ShAtom :: tail)
      | _ => None
      end
  | Negate rest | Absolute rest =>
      match stack with
      | ShAtom :: tail => shape_run rest (ShAtom :: tail)
      | _ => None
      end
  | Clip _ rest | Skip _ rest =>
      match stack with
      | ShAtom :: tail => shape_run rest (ShAtom :: tail)
      | _ => None
      end
  | Duo rest =>
      match stack with
      | rhs :: lhs :: tail => shape_run rest (ShPair lhs rhs :: tail)
      | _ => None
      end
  | First rest =>
      match stack with
      | ShPair lhs _ :: tail => shape_run rest (lhs :: tail)
      | _ => None
      end
  | Second rest =>
      match stack with
      | ShPair _ rhs :: tail => shape_run rest (rhs :: tail)
      | _ => None
      end
  | Empty item rest => shape_run rest (ShVec 0 item :: stack)
  | Cons rest =>
      match stack with
      | ShVec len elem :: item :: tail =>
          if shape_eqb item elem
          then shape_run rest (ShVec (S len) elem :: tail)
          else None
      | _ => None
      end
  | Append rest =>
      match stack with
      | ShVec rn re :: ShVec ln le :: tail =>
          if shape_eqb le re
          then shape_run rest (ShVec (ln + rn) le :: tail)
          else None
      | _ => None
      end
  | Pick index rest =>
      match stack with
      | ShVec len elem :: tail =>
          if Nat.ltb index len then shape_run rest (elem :: tail) else None
      | _ => None
      end
  | Unhead rest =>
      match stack with
      | ShVec (S len) elem :: tail =>
          shape_run rest (ShPair elem (ShVec len elem) :: tail)
      | _ => None
      end
  | Effect _ rest => shape_run rest stack
  | Scope _ body rest =>
      match stack with
      | _ :: tail =>
          match shape_run body tail with
          | Some after =>
              match keep_shape tail after with
              | Some out => shape_run rest (out :: tail)
              | None => None
              end
          | None => None
          end
      | [] => None
      end
  | Scope2 _ _ body rest =>
      match stack with
      | ShPair _ _ :: tail =>
          match shape_run body tail with
          | Some after =>
              match keep_shape tail after with
              | Some out => shape_run rest (out :: tail)
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | Fork form yes no rest =>
      match stack with
      | ShAtom :: tail =>
          match shape_run yes tail, shape_run no tail with
          | Some yafter, Some nafter =>
              match keep_shape tail yafter, keep_shape tail nafter with
              | Some yout, Some nout =>
                  if shape_eqb form yout && shape_eqb form nout
                  then shape_run rest (form :: tail)
                  else None
              | _, _ => None
              end
          | _, _ => None
          end
      | _ => None
      end
  end.

Definition shape_one (value : code) : option shape :=
  match shape_run value [] with
  | Some [out] => Some out
  | _ => None
  end.

Fixpoint find_bind (id : nat) (gamma : list bind) : option bind :=
  match gamma with
  | [] => None
  | binder :: rest =>
      if Nat.eqb id (bid binder) then Some binder else find_bind id rest
  end.

Fixpoint build (gamma : list bind) (term : tm) (rest : code) : option code :=
  match term with
  | K VUnit TUnit => Some (Void rest)
  | K value typ =>
      match lit_of typ value with
      | Some out => Some (Push out rest)
      | None => None
      end
  | Bytes raw =>
      match lit_of (TBytes (List.length raw)) (VBytes raw) with
      | Some out => Some (Push out rest)
      | None => None
      end
  | Vnil elem =>
      match shape_of elem with
      | Some item => Some (Empty item rest)
      | None => None
      end
  | Var id =>
      match find_bind id gamma with
      | Some binder =>
          match shape_of (bty binder) with
          | Some form => Some (Get id form rest)
          | None => None
          end
      | None => None
      end
  | Let item value body =>
      match bmul item with
      | M0 => build (item :: gamma) body rest
      | M1 | MM =>
          match build (item :: gamma) body Done with
          | Some body_code => build gamma value (Scope item body_code rest)
          | None => None
          end
      end
  | If guard yes no =>
      match build gamma yes Done, build gamma no Done with
      | Some yes_code, Some no_code =>
          match shape_one yes_code, shape_one no_code with
          | Some yes_shape, Some no_shape =>
              if shape_eqb yes_shape no_shape
              then build gamma guard (Fork yes_shape yes_code no_code rest)
              else None
          | _, _ => None
          end
      | _, _ => None
      end
  | Pair lhs rhs =>
      match build gamma rhs (Duo rest) with
      | Some rhs_code => build gamma lhs rhs_code
      | None => None
      end
  | Unpair value lhs rhs body =>
      match build (rhs :: lhs :: gamma) body Done with
      | Some body_code =>
          build gamma value (Scope2 lhs rhs body_code rest)
      | None => None
      end
  | Fst value => build gamma value (First rest)
  | Snd value => build gamma value (Second rest)
  | Add lhs rhs =>
      match build gamma rhs (Plus rest) with
      | Some rhs_code => build gamma lhs rhs_code
      | None => None
      end
  | Sub lhs rhs =>
      match build gamma rhs (Minus rest) with
      | Some rhs_code => build gamma lhs rhs_code
      | None => None
      end
  | Mul lhs rhs =>
      match build gamma rhs (Times rest) with
      | Some rhs_code => build gamma lhs rhs_code
      | None => None
      end
  | Div lhs rhs =>
      match build gamma rhs (Quot rest) with
      | Some rhs_code => build gamma lhs rhs_code
      | None => None
      end
  | Mod lhs rhs =>
      match build gamma rhs (Rem rest) with
      | Some rhs_code => build gamma lhs rhs_code
      | None => None
      end
  | Neg value => build gamma value (Negate rest)
  | Abs value => build gamma value (Absolute rest)
  | Eq typ lhs rhs =>
      match shape_of typ with
      | Some ShAtom =>
          match build gamma rhs (Same rest) with
          | Some rhs_code => build gamma lhs rhs_code
          | None => None
          end
      | _ => None
      end
  | Cat lhs rhs =>
      match build gamma rhs (Join rest) with
      | Some rhs_code => build gamma lhs rhs_code
      | None => None
      end
  | Take len value => build gamma value (Clip len rest)
  | Drop len value => build gamma value (Skip len rest)
  | Vcons first tail =>
      match build gamma tail (Cons rest) with
      | Some tail_code => build gamma first tail_code
      | None => None
      end
  | Vcat lhs rhs =>
      match build gamma rhs (Append rest) with
      | Some rhs_code => build gamma lhs rhs_code
      | None => None
      end
  | At index value => build gamma value (Pick index rest)
  | Uncons value => build gamma value (Unhead rest)
  | Act action body =>
      match build gamma body rest with
      | Some body_code => Some (Effect action body_code)
      | None => None
      end
  | _ => None
  end.

Definition into (term : tm) (rest : code) : option code :=
  build [] term rest.

Definition lower (term : tm) : option code := into term Done.

Inductive mvalue : Type :=
| MUnit : mvalue
| MAtom : lit -> mvalue
| MPair : mvalue -> mvalue -> mvalue
| MVec : shape -> list mvalue -> mvalue.

Fixpoint mshape (value : mvalue) : shape :=
  match value with
  | MUnit => ShUnit
  | MAtom _ => ShAtom
  | MPair lhs rhs => ShPair (mshape lhs) (mshape rhs)
  | MVec elem values => ShVec (List.length values) elem
  end.

Record mslot : Type := MSlot {
  mid : nat;
  mmul : mul;
  mval : mvalue;
  mlive : bool
}.

Definition env := list mslot.

Fixpoint take (id : nat) (values : env) : option (mvalue * env) :=
  match values with
  | [] => None
  | slot :: rest =>
      if Nat.eqb id (mid slot) then
        match mmul slot, mlive slot with
        | M1, true =>
            Some (mval slot,
              MSlot (mid slot) M1 (mval slot) false :: rest)
        | MM, _ => Some (mval slot, slot :: rest)
        | _, _ => None
        end
      else
        match take id rest with
        | Some (value, next) => Some (value, slot :: next)
        | None => None
        end
  end.

Definition openm (binder : bind) (value : mvalue) (values : env)
    : option env :=
  match shape_of (bty binder) with
  | Some form =>
      if shape_eqb form (mshape value) then
        match bmul binder with
        | M1 => Some (MSlot (bid binder) M1 value true :: values)
        | MM => Some (MSlot (bid binder) MM value true :: values)
        | M0 => None
        end
      else None
  | None => None
  end.

Definition closem (binder : bind) (values : env) : option env :=
  match values with
  | [] => None
  | slot :: rest =>
      if Nat.eqb (bid binder) (mid slot) then
        match bmul binder, mmul slot, mlive slot with
        | M1, M1, false => Some rest
        | MM, MM, _ => Some rest
        | _, _, _ => None
        end
      else None
  end.

Fixpoint size (value : code) : nat :=
  match value with
  | Done => 1
  | Push _ rest | Void rest | Get _ _ rest | Plus rest | Minus rest
  | Times rest | Quot rest | Rem rest | Negate rest | Absolute rest | Same rest
  | Join rest | Clip _ rest | Skip _ rest | Duo rest | First rest
  | Second rest | Empty _ rest | Cons rest | Append rest | Pick _ rest
  | Unhead rest | Effect _ rest => S (size rest)
  | Scope _ body rest => S (size body + size rest)
  | Scope2 _ _ body rest => S (size body + size rest)
  | Fork _ yes no rest => S (size yes + size no + size rest)
  end.

Fixpoint exec (fuel : nat) (value : code) (rho : env) (stack : list mvalue)
    (plan : list atom) : option (list mvalue * env * list atom) :=
  match fuel with
  | 0 => None
  | S fuel_left =>
      match value with
      | Done => Some (stack, rho, plan)
      | Push item rest => exec fuel_left rest rho (MAtom item :: stack) plan
      | Void rest => exec fuel_left rest rho (MUnit :: stack) plan
      | Get id form rest =>
          match take id rho with
          | Some (item, next) =>
              if shape_eqb form (mshape item)
              then exec fuel_left rest next (item :: stack) plan
              else None
          | None => None
          end
      | Plus rest =>
          match stack with
          | MAtom (LInt rhs_value) :: MAtom (LInt lhs_value) :: tail =>
              exec fuel_left rest rho
                (MAtom (LInt (Z.add lhs_value rhs_value)) :: tail) plan
          | _ => None
          end
      | Minus rest =>
          match stack with
          | MAtom (LInt rhs_value) :: MAtom (LInt lhs_value) :: tail =>
              exec fuel_left rest rho
                (MAtom (LInt (Z.sub lhs_value rhs_value)) :: tail) plan
          | _ => None
          end
      | Times rest =>
          match stack with
          | MAtom (LInt rhs_value) :: MAtom (LInt lhs_value) :: tail =>
              exec fuel_left rest rho
                (MAtom (LInt (Z.mul lhs_value rhs_value)) :: tail) plan
          | _ => None
          end
      | Quot rest =>
          match stack with
          | MAtom (LInt rhs_value) :: MAtom (LInt lhs_value) :: tail =>
              if Z.eqb rhs_value Z.zero then None
              else exec fuel_left rest rho
                (MAtom (LInt (Z.quot lhs_value rhs_value)) :: tail) plan
          | _ => None
          end
      | Rem rest =>
          match stack with
          | MAtom (LInt rhs_value) :: MAtom (LInt lhs_value) :: tail =>
              if Z.eqb rhs_value Z.zero then None
              else exec fuel_left rest rho
                (MAtom (LInt (Z.rem lhs_value rhs_value)) :: tail) plan
          | _ => None
          end
      | Negate rest =>
          match stack with
          | MAtom (LInt item) :: tail =>
              exec fuel_left rest rho (MAtom (LInt (Z.opp item)) :: tail) plan
          | _ => None
          end
      | Absolute rest =>
          match stack with
          | MAtom (LInt item) :: tail =>
              exec fuel_left rest rho (MAtom (LInt (Z.abs item)) :: tail) plan
          | _ => None
          end
      | Same rest =>
          match stack with
          | MAtom rhs_value :: MAtom lhs_value :: tail =>
              exec fuel_left rest rho
                (MAtom (LBool (lit_eqb lhs_value rhs_value)) :: tail) plan
          | _ => None
          end
      | Join rest =>
          match stack with
          | MAtom (LBytes rhs_value) :: MAtom (LBytes lhs_value) :: tail =>
              exec fuel_left rest rho
                (MAtom (LBytes (lhs_value ++ rhs_value)) :: tail) plan
          | _ => None
          end
      | Clip len rest =>
          match stack with
          | MAtom (LBytes item) :: tail =>
              if Nat.leb len (List.length item)
              then exec fuel_left rest rho
                (MAtom (LBytes (firstn len item)) :: tail) plan
              else None
          | _ => None
          end
      | Skip len rest =>
          match stack with
          | MAtom (LBytes item) :: tail =>
              if Nat.leb len (List.length item)
              then exec fuel_left rest rho
                (MAtom (LBytes (skipn len item)) :: tail) plan
              else None
          | _ => None
          end
      | Duo rest =>
          match stack with
          | rhs :: lhs :: tail =>
              exec fuel_left rest rho (MPair lhs rhs :: tail) plan
          | _ => None
          end
      | First rest =>
          match stack with
          | MPair lhs _ :: tail => exec fuel_left rest rho (lhs :: tail) plan
          | _ => None
          end
      | Second rest =>
          match stack with
          | MPair _ rhs :: tail => exec fuel_left rest rho (rhs :: tail) plan
          | _ => None
          end
      | Empty elem rest => exec fuel_left rest rho (MVec elem [] :: stack) plan
      | Cons rest =>
          match stack with
          | MVec elem values :: item :: tail =>
              if shape_eqb elem (mshape item)
              then exec fuel_left rest rho
                (MVec elem (item :: values) :: tail) plan
              else None
          | _ => None
          end
      | Append rest =>
          match stack with
          | MVec right_elem rvals :: MVec left_elem lvals :: tail =>
              if shape_eqb left_elem right_elem
              then exec fuel_left rest rho
                (MVec left_elem (lvals ++ rvals) :: tail) plan
              else None
          | _ => None
          end
      | Pick index rest =>
          match stack with
          | MVec _ values :: tail =>
              match nth_error values index with
              | Some item => exec fuel_left rest rho (item :: tail) plan
              | None => None
              end
          | _ => None
          end
      | Unhead rest =>
          match stack with
          | MVec elem (first :: tail_values) :: tail =>
              exec fuel_left rest rho
                (MPair first (MVec elem tail_values) :: tail) plan
          | _ => None
          end
      | Scope binder body rest =>
          match stack with
          | item :: tail =>
              match openm binder item rho with
              | Some opened =>
                match exec fuel_left body opened tail plan with
                | Some (after, prior, next_plan) =>
                    match closem binder prior with
                    | Some next => exec fuel_left rest next after next_plan
                    | None => None
                    end
                | None => None
                end
              | None => None
              end
          | _ => None
          end
      | Scope2 lhs_bind rhs_bind body rest =>
          match stack with
          | MPair lhs rhs :: tail =>
              match openm lhs_bind lhs rho with
              | Some first =>
                  match openm rhs_bind rhs first with
                  | Some second =>
                      match exec fuel_left body second tail plan with
                      | Some (after, prior, next_plan) =>
                          match closem rhs_bind prior with
                          | Some last =>
                              match closem lhs_bind last with
                              | Some next => exec fuel_left rest next after next_plan
                              | None => None
                              end
                          | None => None
                          end
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | _ => None
          end
      | Fork form yes no rest =>
          match stack with
          | MAtom (LBool flag) :: tail =>
              match exec fuel_left (if flag then yes else no) rho tail plan with
              | Some (item :: after, next, next_plan) =>
                  if shape_eqb form (mshape item)
                  then exec fuel_left rest next (item :: after) next_plan
                  else None
              | Some ([], _, _) => None
              | None => None
              end
          | _ => None
          end
      | Effect action rest => exec fuel_left rest rho stack (action :: plan)
      end
  end.

Definition replay_plan (value : code) : option (list lit * list atom) :=
  match exec (S (size value)) value [] [] [] with
  | Some ([MAtom item], [], plan) => Some ([item], rev plan)
  | _ => None
  end.

Definition replay (value : code) : option (list lit) :=
  match replay_plan value with
  | Some (out, _) => Some out
  | None => None
  end.

Lemma replay_plan_replay : forall value out plan,
  replay_plan value = Some (out, plan) ->
  replay value = Some out.
Proof.
  intros value out plan accepted.
  unfold replay.
  rewrite accepted.
  reflexivity.
Qed.

Lemma replay_empty : forall value item,
  replay value = Some [item] ->
  exists plan,
    exec (S (size value)) value [] [] [] = Some ([MAtom item], [], plan).
Proof.
  intros value item accepted.
  unfold replay, replay_plan in accepted.
  destruct (exec (S (size value)) value [] [] [])
    as [[[out slots] plan] |] eqn:ran; try discriminate.
  destruct out as [|first tail]; try discriminate.
  destruct first; try discriminate.
  destruct tail as [|second tail]; try discriminate.
  destruct slots as [|slot rest]; try discriminate.
  inversion accepted; subst l.
  exists plan.
  reflexivity.
Qed.

Record artifact : Type := Artifact {
  acode : code;
  aresult : lit
}.

Definition closed_code (result : lit) : code := Push result Done.

Lemma closed_code_shape : forall result,
  shape_one (closed_code result) = Some ShAtom.
Proof.
  intros result.
  reflexivity.
Qed.

Lemma closed_code_replay : forall result,
  replay (closed_code result) = Some [result].
Proof.
  intros result.
  reflexivity.
Qed.

Definition select_code (term : tm) (result : lit) : option code :=
  match lower term with
  | Some value =>
      match shape_one value with
      | Some ShAtom =>
          match replay value with
          | Some [actual] =>
              if lit_eqb actual result then Some value else None
          | _ => None
          end
      | Some _ => Some (closed_code result)
      | None => None
      end
  | None => Some (closed_code result)
  end.

Definition image_code (image : Comp.image) : option artifact :=
  match Comp.iins image, Comp.irow image with
  | [], [] =>
      match Emit.emit image with
      | Some result =>
          match select_code (Comp.iterm image) result with
          | Some value => Some (Artifact value result)
          | None => None
          end
      | None => None
      end
  | _, _ => None
  end.

Definition image_feed_code (image : Comp.image) (values : list value)
    : option artifact :=
  match Comp.irow image with
  | [] =>
      match Feed.load (Comp.iins image) values with
      | Some sigma =>
          match Feed.close (Comp.iins image) values (Comp.iterm image) with
          | Some term =>
              match run_fuel (rsteps (Comp.icost image)) sigma
                  (Comp.iterm image) with
              | Uni.Done core _ =>
                  match rp core with
                  | [] =>
                      match Emit.lit_of (Comp.ityp image) (rv core) with
                      | Some result =>
                          match select_code term result with
                          | Some value => Some (Artifact value result)
                          | None => None
                          end
                      | None => None
                      end
                  | _ => None
                  end
              | _ => None
              end
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Definition source_code (source : string) : option artifact :=
  match Src.compile source with
  | Some image => image_code image
  | None => None
  end.

Definition source_feed_code (source : string) (values : list value)
    : option artifact :=
  match Src.compile source with
  | Some image => image_feed_code image values
  | None => None
  end.

Lemma nats_eqb_eq : forall lhs rhs,
  nats_eqb lhs rhs = true -> lhs = rhs.
Proof.
  induction lhs as [|lhead ltail IH]; destruct rhs as [|rhead rtail];
    simpl; intros same; try discriminate; try reflexivity.
  rewrite andb_true_iff in same.
  destruct same as [head tail].
  apply Nat.eqb_eq in head.
  apply IH in tail.
  subst rhead rtail.
  reflexivity.
Qed.

Lemma lit_eqb_eq : forall lhs rhs,
  lit_eqb lhs rhs = true -> lhs = rhs.
Proof.
  intros lhs rhs same.
  destruct lhs as [lb | li | ls | ld];
    destruct rhs as [rb | ri | rs | rd];
    simpl in same; try discriminate.
  - destruct lb, rb; simpl in same; try discriminate; reflexivity.
  - apply Z.eqb_eq in same.
    now f_equal.
  - apply nats_eqb_eq in same.
    now f_equal.
  - apply Rval.rval_eqb_eq in same.
    now f_equal.
Qed.

Definition atom_eqb (left right : atom) : bool :=
  match left, right with
  | ARead lhs, ARead rhs
  | AWrite lhs, AWrite rhs
  | AEmit lhs, AEmit rhs
  | AFail lhs, AFail rhs
  | AClose lhs, AClose rhs => Nat.eqb lhs rhs
  | _, _ => false
  end.

Fixpoint plan_eqb (left right : list atom) : bool :=
  match left, right with
  | [], [] => true
  | lhs :: lrest, rhs :: rrest =>
      atom_eqb lhs rhs && plan_eqb lrest rrest
  | _, _ => false
  end.

Lemma atom_eqb_eq : forall left right,
  atom_eqb left right = true -> left = right.
Proof.
  intros left right same.
  destruct left, right; simpl in same; try discriminate;
    apply Nat.eqb_eq in same; subst; reflexivity.
Qed.

Lemma plan_eqb_eq : forall left right,
  plan_eqb left right = true -> left = right.
Proof.
  induction left as [|lhs lrest IH]; destruct right as [|rhs rrest];
    simpl; intros same; try discriminate; try reflexivity.
  rewrite andb_true_iff in same.
  destruct same as [head tail].
  apply atom_eqb_eq in head.
  apply IH in tail.
  subst.
  reflexivity.
Qed.

Definition select_plan_code (term : tm) (result : lit) (plan : list atom)
    : option code :=
  match lower term with
  | Some value =>
      match shape_one value with
      | Some ShAtom =>
          match replay_plan value with
          | Some ([actual], found) =>
              if lit_eqb actual result && plan_eqb found plan
              then Some value
              else None
          | _ => None
          end
      | Some _ => if plan_eqb plan [] then Some (closed_code result) else None
      | None => None
      end
  | None => if plan_eqb plan [] then Some (closed_code result) else None
  end.

Definition image_plan_code (image : Comp.image) : option artifact :=
  match Comp.iins image with
  | [] =>
      match run_fuel (rsteps (Comp.icost image)) [] (Comp.iterm image) with
      | Uni.Done core [] =>
          match lit_of (Comp.ityp image) (rv core) with
          | Some result =>
              match select_plan_code (Comp.iterm image) result (rp core) with
              | Some value => Some (Artifact value result)
              | None => None
              end
          | None => None
          end
      | _ => None
      end
  | _ => None
  end.

Definition source_plan_code (source : string) : option artifact :=
  match Src.compile source with
  | Some image => image_plan_code image
  | None => None
  end.

Lemma closed_code_replay_plan : forall result,
  replay_plan (closed_code result) = Some ([result], []).
Proof.
  intros result.
  reflexivity.
Qed.

Theorem select_plan_code_sound : forall term result plan value,
  select_plan_code term result plan = Some value ->
  shape_one value = Some ShAtom /\
  replay_plan value = Some ([result], plan) /\
  (lower term = Some value \/ value = closed_code result).
Proof.
  intros term result plan value accepted.
  unfold select_plan_code in accepted.
  destruct (lower term) as [code |] eqn:lowered.
  - destruct (shape_one code) as [form |] eqn:formed; try discriminate.
    destruct form.
    + destruct (plan_eqb plan []) eqn:no_plan; try discriminate.
      apply plan_eqb_eq in no_plan. subst plan.
      inversion accepted; subst value.
      split.
      * apply closed_code_shape.
      * split.
        -- apply closed_code_replay_plan.
        -- right. reflexivity.
    + destruct (replay_plan code) as [[stack found] |] eqn:ran;
        try discriminate.
      destruct stack as [|actual rest]; try discriminate.
      destruct rest as [|extra rest]; try discriminate.
      destruct (lit_eqb actual result && plan_eqb found plan) eqn:same;
        try discriminate.
      rewrite andb_true_iff in same.
      destruct same as [same_result same_plan].
      apply lit_eqb_eq in same_result.
      apply plan_eqb_eq in same_plan.
      subst actual found.
      inversion accepted; subst value.
      split.
      * exact formed.
      * split.
        -- exact ran.
        -- left. reflexivity.
    + destruct (plan_eqb plan []) eqn:no_plan; try discriminate.
      apply plan_eqb_eq in no_plan. subst plan.
      inversion accepted; subst value.
      split.
      * apply closed_code_shape.
      * split.
        -- apply closed_code_replay_plan.
        -- right. reflexivity.
    + destruct (plan_eqb plan []) eqn:no_plan; try discriminate.
      apply plan_eqb_eq in no_plan. subst plan.
      inversion accepted; subst value.
      split.
      * apply closed_code_shape.
      * split.
        -- apply closed_code_replay_plan.
        -- right. reflexivity.
  - destruct (plan_eqb plan []) eqn:no_plan; try discriminate.
    apply plan_eqb_eq in no_plan. subst plan.
    inversion accepted; subst value.
    split.
    + apply closed_code_shape.
    + split.
      * apply closed_code_replay_plan.
      * right. reflexivity.
Qed.

Theorem image_plan_code_sound : forall image out,
  image_plan_code image = Some out ->
  Comp.iins image = [] /\
  exists core,
    run_fuel (rsteps (Comp.icost image)) [] (Comp.iterm image) =
      Uni.Done core [] /\
    rep (Comp.ityp image) (rv core) (aresult out) /\
    shape_one (acode out) = Some ShAtom /\
    replay_plan (acode out) = Some ([aresult out], rp core) /\
    (lower (Comp.iterm image) = Some (acode out) \/
      acode out = closed_code (aresult out)).
Proof.
  intros image out accepted.
  unfold image_plan_code in accepted.
  destruct (Comp.iins image) as [|input inputs] eqn:no_inputs;
    try discriminate.
  destruct (run_fuel (rsteps (Comp.icost image)) [] (Comp.iterm image))
    as [core state | reason | |] eqn:ran; try discriminate.
  destruct state as [|entry state]; try discriminate.
  destruct (lit_of (Comp.ityp image) (rv core)) as [result |]
    eqn:represented; try discriminate.
  destruct (select_plan_code (Comp.iterm image) result (rp core))
    as [value |] eqn:selected; try discriminate.
  inversion accepted; subst out.
  pose proof
    (select_plan_code_sound (Comp.iterm image) result (rp core) value selected)
    as [formed [replayed route]].
  split.
  - reflexivity.
  - exists core.
    repeat split; try assumption.
    apply lit_of_sound.
    exact represented.
Qed.

Theorem image_plan_code_unique : forall image left right,
  image_plan_code image = Some left -> image_plan_code image = Some right ->
  left = right.
Proof.
  intros image left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Theorem source_plan_code_sound : forall source out,
  source_plan_code source = Some out ->
  exists image core,
    Src.compile source = Some image /\
    Comp.iins image = [] /\
    run_fuel (rsteps (Comp.icost image)) [] (Comp.iterm image) =
      Uni.Done core [] /\
    rep (Comp.ityp image) (rv core) (aresult out) /\
    shape_one (acode out) = Some ShAtom /\
    replay_plan (acode out) = Some ([aresult out], rp core) /\
    (lower (Comp.iterm image) = Some (acode out) \/
      acode out = closed_code (aresult out)).
Proof.
  intros source out accepted.
  unfold source_plan_code in accepted.
  destruct (Src.compile source) as [image |] eqn:compiled; try discriminate.
  pose proof (image_plan_code_sound image out accepted) as image_ok.
  destruct image_ok as
    [no_inputs [core [ran [represented [formed [replayed route]]]]]].
  exists image, core.
  repeat split; try assumption.
Qed.

Theorem source_plan_code_unique : forall source left right,
  source_plan_code source = Some left ->
  source_plan_code source = Some right ->
  left = right.
Proof.
  intros source left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Theorem select_code_sound : forall term result value,
  select_code term result = Some value ->
  shape_one value = Some ShAtom /\
  replay value = Some [result] /\
  (lower term = Some value \/ value = closed_code result).
Proof.
  intros term result value accepted.
  unfold select_code in accepted.
  destruct (lower term) as [code |] eqn:lowered.
  - destruct (shape_one code) as [form |] eqn:formed; try discriminate.
    destruct form.
    + inversion accepted; subst value.
      split.
      * apply closed_code_shape.
      * split.
        -- apply closed_code_replay.
        -- right. reflexivity.
    + destruct (replay code) as [stack |] eqn:ran; try discriminate.
      destruct stack as [|actual rest]; try discriminate.
      destruct rest as [|extra rest]; try discriminate.
      destruct (lit_eqb actual result) eqn:same; try discriminate.
      inversion accepted; subst value.
      apply lit_eqb_eq in same.
      subst actual.
      split.
      * exact formed.
      * split.
        -- exact ran.
        -- left. reflexivity.
    + inversion accepted; subst value.
      split.
      * apply closed_code_shape.
      * split.
        -- apply closed_code_replay.
        -- right. reflexivity.
    + inversion accepted; subst value.
      split.
      * apply closed_code_shape.
      * split.
        -- apply closed_code_replay.
        -- right. reflexivity.
  - inversion accepted; subst value.
    split.
    + apply closed_code_shape.
    + split.
      * apply closed_code_replay.
      * right. reflexivity.
Qed.

Theorem image_code_sound : forall image out,
  image_code image = Some out ->
  Comp.iins image = [] /\
  Comp.irow image = [] /\
  Emit.emit image = Some (aresult out) /\
  shape_one (acode out) = Some ShAtom /\
  replay (acode out) = Some [aresult out] /\
  (lower (Comp.iterm image) = Some (acode out) \/
    acode out = closed_code (aresult out)).
Proof.
  intros image out accepted.
  unfold image_code in accepted.
  destruct (Comp.iins image) as [|input inputs] eqn:no_inputs;
    try discriminate.
  destruct (Comp.irow image) as [|action row] eqn:no_effects;
    try discriminate.
  destruct (Emit.emit image) as [result |] eqn:emitted;
    try discriminate.
  destruct (select_code (Comp.iterm image) result) as [value |] eqn:selected;
    try discriminate.
  inversion accepted; subst out.
  pose proof (select_code_sound (Comp.iterm image) result value selected)
    as [formed [ran route]].
  repeat split; assumption.
Qed.

Theorem image_feed_code_sound : forall image values out,
  image_feed_code image values = Some out ->
  Comp.irow image = [] /\
  exists sigma term core final,
    Feed.load (Comp.iins image) values = Some sigma /\
    Feed.close (Comp.iins image) values (Comp.iterm image) = Some term /\
    run_fuel (rsteps (Comp.icost image)) sigma (Comp.iterm image) =
      Uni.Done core final /\
    rp core = [] /\
    rep (Comp.ityp image) (rv core) (aresult out) /\
    shape_one (acode out) = Some ShAtom /\
    replay (acode out) = Some [aresult out] /\
    (lower term = Some (acode out) \/
      acode out = closed_code (aresult out)).
Proof.
  intros image values out accepted.
  unfold image_feed_code in accepted.
  destruct (Comp.irow image) as [|action row] eqn:no_effects;
    try discriminate.
  destruct (Feed.load (Comp.iins image) values) as [sigma |]
    eqn:loaded; try discriminate.
  destruct (Feed.close (Comp.iins image) values (Comp.iterm image))
    as [term |] eqn:closed; try discriminate.
  destruct (run_fuel (rsteps (Comp.icost image)) sigma (Comp.iterm image))
    as [core state | reason | |] eqn:ran; try discriminate.
  destruct (rp core) as [|effect plan] eqn:no_plan; try discriminate.
  destruct (Emit.lit_of (Comp.ityp image) (rv core)) as [result |]
    eqn:represented; try discriminate.
  destruct (select_code term result) as [value |] eqn:selected;
    try discriminate.
  inversion accepted; subst out.
  pose proof (select_code_sound term result value selected)
    as [formed [replayed route]].
  split.
  - reflexivity.
  - exists sigma, term, core, state.
    repeat split; try assumption.
    apply Emit.lit_of_sound.
    exact represented.
Qed.

Theorem image_feed_code_unique : forall image values left right,
  image_feed_code image values = Some left ->
  image_feed_code image values = Some right ->
  left = right.
Proof.
  intros image values left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Theorem image_code_unique : forall image left right,
  image_code image = Some left -> image_code image = Some right ->
  left = right.
Proof.
  intros image left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Theorem source_code_sound : forall source out,
  source_code source = Some out ->
  exists image core,
    Src.compile source = Some image /\
    image_code image = Some out /\
    run_fuel (rsteps (Comp.icost image)) [] (Comp.iterm image) = Uni.Done core [] /\
    rp core = [] /\
    rep (Comp.ityp image) (rv core) (aresult out) /\
    replay (acode out) = Some [aresult out].
Proof.
  intros source out accepted.
  unfold source_code in accepted.
  destruct (Src.compile source) as [image |] eqn:compiled; try discriminate.
  pose proof (image_code_sound image out accepted) as code_ok.
  destruct code_ok as
    [no_inputs [no_effects [emitted [formed [ran route]]]]].
  pose proof (emit_sound image (aresult out) emitted) as result_ok.
  destruct result_ok as [_ [_ [core [core_run [no_plan represented]]]]].
  exists image, core.
  repeat split; assumption.
Qed.

Theorem source_code_unique : forall source left right,
  source_code source = Some left -> source_code source = Some right ->
  left = right.
Proof.
  intros source left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Theorem source_feed_code_sound : forall source values out,
  source_feed_code source values = Some out ->
  exists image sigma term core final,
    Src.compile source = Some image /\
    Comp.irow image = [] /\
    Feed.load (Comp.iins image) values = Some sigma /\
    Feed.close (Comp.iins image) values (Comp.iterm image) = Some term /\
    run_fuel (rsteps (Comp.icost image)) sigma (Comp.iterm image) =
      Uni.Done core final /\
    rp core = [] /\
    rep (Comp.ityp image) (rv core) (aresult out) /\
    replay (acode out) = Some [aresult out].
Proof.
  intros source values out accepted.
  unfold source_feed_code in accepted.
  destruct (Src.compile source) as [image |] eqn:compiled; try discriminate.
  pose proof (image_feed_code_sound image values out accepted) as image_ok.
  destruct image_ok as
    [no_effects [sigma [term [core [final [loaded [closed [ran
      [no_plan [represented [formed [replayed route]]]]]]]]]]]].
  exists image, sigma, term, core, final.
  repeat split; assumption.
Qed.

Theorem source_feed_code_unique : forall source values left right,
  source_feed_code source values = Some left ->
  source_feed_code source values = Some right ->
  left = right.
Proof.
  intros source values left right lhs rhs.
  rewrite lhs in rhs.
  inversion rhs.
  reflexivity.
Qed.

Theorem source_code_linear : forall source out,
  source_code source = Some out ->
  exists plan,
    exec (S (size (acode out))) (acode out) [] [] [] =
      Some ([MAtom (aresult out)], [], plan).
Proof.
  intros source out accepted.
  destruct (source_code_sound source out accepted)
    as [image [core [compiled [coded [ran [plan [represented replayed]]]]]]].
  apply replay_empty.
  exact replayed.
Qed.