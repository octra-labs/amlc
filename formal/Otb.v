(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.

Require Import Bin.
Require Import Ser.
Require Import Mach.
Require Import Iwork.

Import ListNotations.

Inductive otype : Type :=
| OUnit : otype
| OBool : otype
| OInt : otype
| ONum : bool -> nat -> otype
| OBytes : nat -> otype
| OVec : nat -> otype -> otype
| OSeq : nat -> otype -> otype
| OCap : nat -> otype
| OEnc : nat -> nat -> otype
| OPair : otype -> otype -> otype
| OSum : otype -> otype -> otype.

Fixpoint otype_code (typ : otype) : Bin.code :=
  match typ with
  | OUnit => Bin.CTag 0 Bin.CNil
  | OBool => Bin.CTag 1 Bin.CNil
  | OInt => Bin.CTag 2 Bin.CNil
  | ONum signed width =>
      Bin.CTag 9
        (Bin.CCons (Bin.CNum (if signed then 0 else 1))
          (Bin.CCons (Bin.CNum width) Bin.CNil))
  | OBytes len => Bin.CTag 3 (Bin.CNum len)
  | OVec len elem =>
      Bin.CTag 4
        (Bin.CCons (Bin.CNum len)
          (Bin.CCons (otype_code elem) Bin.CNil))
  | OSeq cap elem =>
      Bin.CTag 10
        (Bin.CCons (Bin.CNum cap)
          (Bin.CCons (otype_code elem) Bin.CNil))
  | OCap kind => Bin.CTag 5 (Bin.CNum kind)
  | OEnc key rem =>
      Bin.CTag 8
        (Bin.CCons (Bin.CNum key)
          (Bin.CCons (Bin.CNum rem) Bin.CNil))
  | OPair first second =>
      Bin.CTag 6
        (Bin.CCons (otype_code first)
          (Bin.CCons (otype_code second) Bin.CNil))
  | OSum first second =>
      Bin.CTag 7
        (Bin.CCons (otype_code first)
          (Bin.CCons (otype_code second) Bin.CNil))
  end.

Fixpoint otype_get (input : Bin.code) : option otype :=
  match input with
  | Bin.CTag 0 Bin.CNil => Some OUnit
  | Bin.CTag 1 Bin.CNil => Some OBool
  | Bin.CTag 2 Bin.CNil => Some OInt
  | Bin.CTag 9
      (Bin.CCons (Bin.CNum signed)
        (Bin.CCons (Bin.CNum width) Bin.CNil)) =>
      match signed with
      | 0 => Some (ONum true width)
      | 1 => Some (ONum false width)
      | _ => None
      end
  | Bin.CTag 3 (Bin.CNum len) => Some (OBytes len)
  | Bin.CTag 4
      (Bin.CCons (Bin.CNum len) (Bin.CCons elem Bin.CNil)) =>
      match otype_get elem with
      | Some typ => Some (OVec len typ)
      | None => None
      end
  | Bin.CTag 10
      (Bin.CCons (Bin.CNum cap) (Bin.CCons elem Bin.CNil)) =>
      match otype_get elem with
      | Some typ => Some (OSeq cap typ)
      | None => None
      end
  | Bin.CTag 5 (Bin.CNum kind) => Some (OCap kind)
  | Bin.CTag 8
      (Bin.CCons (Bin.CNum key) (Bin.CCons (Bin.CNum rem) Bin.CNil)) =>
      Some (OEnc key rem)
  | Bin.CTag 6 (Bin.CCons first (Bin.CCons second Bin.CNil)) =>
      match otype_get first, otype_get second with
      | Some first_type, Some second_type => Some (OPair first_type second_type)
      | _, _ => None
      end
  | Bin.CTag 7 (Bin.CCons first (Bin.CCons second Bin.CNil)) =>
      match otype_get first, otype_get second with
      | Some first_type, Some second_type => Some (OSum first_type second_type)
      | _, _ => None
      end
  | _ => None
  end.

Lemma otype_get_code : forall typ,
  otype_get (otype_code typ) = Some typ.
Proof.
  induction typ; simpl; rewrite ?IHtyp, ?IHtyp1, ?IHtyp2; try reflexivity.
  destruct b; reflexivity.
Qed.

Fixpoint otype_depth (typ : otype) : nat :=
  match typ with
  | OUnit | OBool | OInt | ONum _ _ | OBytes _ | OCap _ | OEnc _ _ => 0
  | OVec _ elem | OSeq _ elem => S (otype_depth elem)
  | OPair first second | OSum first second =>
      S (Nat.max (otype_depth first) (otype_depth second))
  end.

Fixpoint otype_nodes (typ : otype) : nat :=
  match typ with
  | OUnit | OBool | OInt | ONum _ _ | OBytes _ | OCap _ | OEnc _ _ => 1
  | OVec _ elem | OSeq _ elem => S (otype_nodes elem)
  | OPair first second | OSum first second =>
      S (otype_nodes first + otype_nodes second)
  end.

Fixpoint plain_b (typ : otype) : bool :=
  match typ with
  | OUnit | OBool | OInt | ONum _ _ | OBytes _ => true
  | OVec _ elem | OSeq _ elem => plain_b elem
  | OPair first second | OSum first second => plain_b first && plain_b second
  | OCap _ | OEnc _ _ => false
  end.

Definition nat_b (value : nat) : bool := Nat.leb value 1000000.

Fixpoint otype_inner_b (typ : otype) : bool :=
  match typ with
  | OUnit | OBool | OInt => true
  | ONum _ width => Nat.leb 1 width && Nat.leb width 256
  | OBytes len | OCap len => nat_b len
  | OVec len elem => nat_b len && otype_inner_b elem
  | OSeq cap elem => nat_b cap && plain_b elem && otype_inner_b elem
  | OEnc key rem => nat_b key && nat_b rem
  | OPair first second | OSum first second =>
      otype_inner_b first && otype_inner_b second
  end.

Definition otype_b (typ : otype) : bool :=
  otype_inner_b typ
    && Nat.leb (otype_depth typ) 256
    && Nat.leb (otype_nodes typ) 4096.

Fixpoint otype_list_nodes (types : list otype) : nat :=
  match types with
  | [] => 0
  | typ :: rest => otype_nodes typ + otype_list_nodes rest
  end.

Definition frame_code (inputs : list otype) (output : otype)
    (results : list nat) : Bin.code :=
  Bin.CTag 0
    (Bin.CCons (list_code otype_code inputs)
      (Bin.CCons (otype_code output)
        (Bin.CCons (list_code Bin.CNum results) Bin.CNil))).

Definition frame_get (input : Bin.code)
    : option (list otype * otype * list nat) :=
  match input with
  | Bin.CTag 0
      (Bin.CCons inputs
        (Bin.CCons output (Bin.CCons results Bin.CNil))) =>
      match list_get otype_get inputs, otype_get output,
          list_get num_get results with
      | Some input_types, Some output_type, Some result_regs =>
          Some (input_types, output_type, result_regs)
      | _, _, _ => None
      end
  | _ => None
  end.

Lemma frame_get_code : forall inputs output results,
  frame_get (frame_code inputs output results) =
    Some (inputs, output, results).
Proof.
  intros inputs output results.
  unfold frame_get, frame_code.
  rewrite list_get_code, otype_get_code, list_get_code.
  - reflexivity.
  - intros value _.
    apply num_get_code.
  - intros value _.
    apply otype_get_code.
Qed.

Definition frame_bits inputs output results :=
  Ser.enc (fun item =>
    let '(input_types, output_type, result_regs) := item in
    frame_code input_types output_type result_regs)
    (inputs, output, results).

Definition type_set_b inputs output :=
  forallb otype_b (output :: inputs)
    && Nat.leb (otype_list_nodes (output :: inputs)) 4096.

Definition frame_b inputs output results :=
  negb (Nat.eqb (length inputs) 0)
    && type_set_b inputs output
    && result_regs_b results
    && Nat.leb (length (frame_bits inputs output results)) (4096 * 128).

Definition frame_read (input : Bin.bits)
    : option (list otype * otype * list nat) :=
  match
    Ser.dec
      (fun item =>
        let '(input_types, output_type, result_regs) := item in
        frame_code input_types output_type result_regs)
      frame_get input
  with
  | Some (inputs, output, results) =>
      if frame_b inputs output results then Some (inputs, output, results)
      else None
  | None => None
  end.

Fixpoint otype_shape (typ : otype) : option shape :=
  match typ with
  | OUnit => Some ShUnit
  | OBool | OInt | ONum _ _ | OBytes _ => Some ShAtom
  | OCap kind => Some (ShCap kind)
  | OVec len elem =>
      match otype_shape elem with
      | Some item => Some (ShVec len item)
      | None => None
      end
  | OSeq cap elem =>
      match otype_shape elem with
      | Some item => Some (ShPair ShAtom (ShVec cap item))
      | None => None
      end
  | OPair first second =>
      match otype_shape first, otype_shape second with
      | Some first_shape, Some second_shape =>
          Some (ShPair first_shape second_shape)
      | _, _ => None
      end
  | OSum first second =>
      match otype_shape first, otype_shape second with
      | Some first_shape, Some second_shape =>
          if shape_eqb first_shape second_shape then Some (ShSum first_shape)
          else None
      | _, _ => None
      end
  | OEnc _ _ => None
  end.

Fixpoint input_layout (types : list otype) : option (nat * nat) :=
  match types with
  | [] => Some (0, 0)
  | typ :: rest =>
      match otype_shape typ, input_layout rest with
      | Some form, Some (width, cells) =>
          Some (shape_width form + width, shape_cells form + cells)
      | _, _ => None
      end
  end.

Definition layout_b (inputs : list otype) (output : otype)
    (results : list nat) :=
  match input_layout inputs, otype_shape output with
  | Some (width, cells), Some form =>
      Nat.leb width 60
        && Nat.leb (cells + shape_cells form) 4096
        && Nat.eqb (shape_width form) (length results)
  | _, _ => false
  end.

Definition layout_read (input : Bin.bits)
    : option (list otype * otype * list nat) :=
  match frame_read input with
  | Some (inputs, output, results) =>
      if layout_b inputs output results then Some (inputs, output, results)
      else None
  | None => None
  end.

Inductive header_op : Type :=
| HMark : nat -> header_op
| HMem : nat -> nat -> header_op
| HMain : nat -> header_op
| HEqual : nat -> nat -> nat -> header_op
| HJump : nat -> nat -> header_op
| HRefuse : header_op
| HFrame : nat -> Bin.bits -> header_op.

Definition header (frame : Bin.bits) : list header_op := [
  HMark (dispatch_label 0);
  HMem 61 1000;
  HMain 62;
  HEqual 63 61 62;
  HJump 63 (dispatch_label 1);
  HRefuse;
  HMark (dispatch_label 1);
  HFrame 61 frame
].

Definition header_read (input : list header_op)
    : option (list otype * otype * list nat) :=
  match input with
  | [HMark start; HMem load_reg load_at; HMain name_reg;
      HEqual same_reg left_reg right_reg; HJump branch_reg entry;
      HRefuse; HMark mark; HFrame frame_reg frame] =>
      if Nat.eqb start (dispatch_label 0)
          && Nat.eqb load_reg 61
          && Nat.eqb load_at 1000
          && Nat.eqb name_reg 62
          && Nat.eqb same_reg 63
          && Nat.eqb left_reg 61
          && Nat.eqb right_reg 62
          && Nat.eqb branch_reg 63
          && Nat.eqb entry (dispatch_label 1)
          && Nat.eqb mark (dispatch_label 1)
          && Nat.eqb frame_reg 61
      then frame_read frame
      else None
  | _ => None
  end.

Definition header_op_cost (op : header_op) : nat :=
  match op with
  | HMark _ | HMain _ | HRefuse | HFrame _ _ => 1
  | HMem _ _ => 3
  | HEqual _ _ _ => 2
  | HJump _ _ => 5
  end.

Fixpoint header_cost (ops : list header_op) : nat :=
  match ops with
  | [] => 0
  | op :: rest => header_op_cost op + header_cost rest
  end.

Fixpoint arg_code (start count : nat) : list header_op :=
  match count with
  | 0 => []
  | S rest =>
      HMem (S start) (1001 + start) :: arg_code (S start) rest
  end.

Fixpoint arg_read (start : nat) (input : list header_op) : option nat :=
  match input with
  | [] => Some 0
  | (HMem reg addr) :: rest =>
      if Nat.eqb reg (S start) && Nat.eqb addr (1001 + start) then
        match arg_read (S start) rest with
        | Some count => Some (S count)
        | None => None
        end
      else None
  | _ => None
  end.

Inductive scalar : Type :=
| XInt : scalar
| XBool : scalar
| XBytes : nat -> scalar.

Inductive xop : Type :=
| XMem : nat -> nat -> xop
| XNum : nat -> nat -> xop
| XEmpty : nat -> xop
| XSub : nat -> nat -> nat -> xop
| XIf : nat -> nat -> xop
| XNoop : xop
| XJump : nat -> xop
| XMark : nat -> xop
| XEq : nat -> nat -> nat -> xop
| XSize : nat -> nat -> xop
| XRefuse : xop
| XSlice : nat -> nat -> nat -> nat -> xop
| XStop : xop
| XDiv : nat -> nat -> nat -> xop.

Definition xop_eq (left right : xop) : {left = right} + {left <> right}.
Proof.
  decide equality; apply Nat.eq_dec.
Defined.

Definition xop_b (left right : xop) : bool :=
  if xop_eq left right then true else false.

Fixpoint xops_b (left right : list xop) : bool :=
  match left, right with
  | [], [] => true
  | lhs :: left_rest, rhs :: right_rest =>
      xop_b lhs rhs && xops_b left_rest right_rest
  | _, _ => false
  end.

Definition input_yes index := check_label index 0.
Definition input_done index := check_label index 1.

Definition in_code (index : nat) (typ : scalar) : list xop :=
  let reg := S index in
  let load := XMem reg (1001 + index) in
  match typ with
  | XInt => [load; XNum 61 0; XSub reg reg 61]
  | XBool =>
      [load;
       XIf reg (input_yes index);
       XNoop;
       XJump (input_done index);
       XMark (input_yes index);
       XJump (input_done index);
       XMark (input_done index)]
  | XBytes len =>
      [load;
       XEmpty 61;
       XEq 63 reg 61;
       XSize 61 reg;
       XNum 62 len;
       XEq 63 61 62;
       XIf 63 (input_yes index);
       XRefuse;
       XMark (input_yes index);
       XNum 61 0;
       XSlice reg reg 61 62]
  end.

Definition in_read (index : nat) (input : list xop) : option scalar :=
  if xops_b input (in_code index XInt) then Some XInt
  else if xops_b input (in_code index XBool) then Some XBool
  else
    match nth_error input 4 with
    | Some (XNum _ len) =>
        if xops_b input (in_code index (XBytes len)) then Some (XBytes len)
        else None
    | _ => None
    end.

Definition out_code (first : nat) (typ : scalar) : list xop :=
  match typ with
  | XInt => [XNum 61 0; XSub 0 0 61; XStop]
  | XBool =>
      [XIf 0 (first + 3);
       XNoop;
       XJump (first + 5);
       XMark (first + 3);
       XJump (first + 5);
       XMark (first + 5);
       XStop]
  | XBytes len =>
      [XEmpty 61;
       XEq 63 0 61;
       XSize 61 0;
       XNum 62 len;
       XEq 63 61 62;
       XIf 63 (first + 9);
       XNum 61 1;
       XNum 62 0;
       XDiv 61 61 62;
       XMark (first + 9);
       XStop]
  end.

Definition out_read (first : nat) (input : list xop) : option scalar :=
  if xops_b input (out_code first XInt) then Some XInt
  else if xops_b input (out_code first XBool) then Some XBool
  else
    match nth_error input 3 with
    | Some (XNum _ len) =>
        if xops_b input (out_code first (XBytes len)) then Some (XBytes len)
        else None
    | _ => None
    end.

Definition xop_cost (op : xop) : nat :=
  match op with
  | XMem _ _ | XSub _ _ _ | XSize _ _ => 3
  | XIf _ _ | XSlice _ _ _ _ | XDiv _ _ _ => 5
  | XEq _ _ _ => 2
  | XNum _ _ | XEmpty _ | XNoop | XJump _ | XMark _ | XRefuse | XStop => 1
  end.

Fixpoint xops_cost (ops : list xop) : nat :=
  match ops with
  | [] => 0
  | op :: rest => xop_cost op + xops_cost rest
  end.

Definition in_cost (typ : scalar) : nat :=
  match typ with
  | XInt => 7
  | XBool => 13
  | XBytes _ => 25
  end.

Definition out_cost (typ : scalar) : nat :=
  match typ with
  | XInt => 5
  | XBool => 11
  | XBytes _ => 23
  end.

Inductive xvalue : Type :=
| XvInt : Z -> xvalue
| XvBool : bool -> xvalue
| XvBytes : list nat -> xvalue.

Definition octets_b (values : list nat) : bool :=
  forallb (fun value => Nat.ltb value 256) values.

Definition xvalue_b (typ : scalar) (value : xvalue) : bool :=
  match typ, value with
  | XInt, XvInt _ | XBool, XvBool _ => true
  | XBytes len, XvBytes values =>
      octets_b values && Nat.eqb (length values) len
  | _, _ => false
  end.

Definition in_run_cost (typ : scalar) (value : xvalue) : nat :=
  match typ, value with
  | XInt, XvInt number => 7 + Iwork.cells number
  | XBool, XvBool _ => 11
  | XBytes _, XvBytes values => 24 + length values / 256
  | _, _ => 0
  end.

Definition out_run_cost (typ : scalar) (value : xvalue) : nat :=
  match typ, value with
  | XInt, XvInt number => 5 + Iwork.cells number
  | XBool, XvBool _ => 9
  | XBytes _, XvBytes _ => 16
  | _, _ => 0
  end.

Definition in_turn (index : nat) (input : list xop) (value : xvalue)
    : option (xvalue * nat) :=
  match in_read index input with
  | Some typ =>
      if xvalue_b typ value then Some (value, in_run_cost typ value) else None
  | None => None
  end.

Definition out_turn (first : nat) (input : list xop) (value : xvalue)
    : option (xvalue * nat) :=
  match out_read first input with
  | Some typ =>
      if xvalue_b typ value then Some (value, out_run_cost typ value) else None
  | None => None
  end.

Definition xreg_b (op : xop) : bool :=
  let reg value := Nat.ltb value 64 in
  match op with
  | XMem dst _ | XNum dst _ | XEmpty dst | XIf dst _ => reg dst
  | XSub dst lhs rhs | XEq dst lhs rhs | XDiv dst lhs rhs =>
      reg dst && reg lhs && reg rhs
  | XSize dst source => reg dst && reg source
  | XSlice dst source first count =>
      reg dst && reg source && reg first && reg count
  | XNoop | XJump _ | XMark _ | XRefuse | XStop => true
  end.

Definition xregs_b (ops : list xop) : bool := forallb xreg_b ops.

Lemma xop_b_true : forall left right,
  xop_b left right = true -> left = right.
Proof.
  intros left right accepted.
  unfold xop_b in accepted.
  destruct (xop_eq left right); try discriminate.
  exact e.
Qed.

Lemma xops_b_refl : forall ops,
  xops_b ops ops = true.
Proof.
  induction ops; simpl.
  - reflexivity.
  - unfold xop_b at 1.
    destruct (xop_eq a a).
    + exact IHops.
    + contradiction.
Qed.

Lemma xops_b_true : forall left right,
  xops_b left right = true -> left = right.
Proof.
  induction left as [|lhs left_rest IH]; intros right accepted.
  - destruct right; simpl in accepted; try discriminate.
    reflexivity.
  - destruct right as [|rhs right_rest]; simpl in accepted; try discriminate.
    apply andb_true_iff in accepted as [head tail].
    apply xop_b_true in head.
    apply IH in tail.
    subst.
    reflexivity.
Qed.

Lemma xops_b_false : forall left right,
  left <> right -> xops_b left right = false.
Proof.
  intros left right distinct.
  destruct (xops_b left right) eqn:accepted.
  - apply xops_b_true in accepted.
    contradiction.
  - reflexivity.
Qed.

Theorem in_read_code : forall index typ,
  in_read index (in_code index typ) = Some typ.
Proof.
  intros index typ.
  destruct typ.
  - unfold in_read.
    rewrite xops_b_refl.
    reflexivity.
  - unfold in_read.
    rewrite xops_b_false.
    2: unfold in_code; discriminate.
    rewrite xops_b_refl.
    reflexivity.
  - unfold in_read.
    rewrite xops_b_false.
    2: unfold in_code; discriminate.
    rewrite xops_b_false.
    2: unfold in_code; discriminate.
    change
      ((if xops_b (in_code index (XBytes n))
          (in_code index (XBytes n))
        then Some (XBytes n) else None) = Some (XBytes n)).
    rewrite xops_b_refl.
    reflexivity.
Qed.

Theorem in_encode_decode : forall index input typ,
  in_read index input = Some typ -> input = in_code index typ.
Proof.
  intros index input typ accepted.
  unfold in_read in accepted.
  destruct (xops_b input (in_code index XInt)) eqn:int_code.
  - apply xops_b_true in int_code.
    injection accepted as same.
    subst typ.
    exact int_code.
  - destruct (xops_b input (in_code index XBool)) eqn:bool_code.
    + apply xops_b_true in bool_code.
      injection accepted as same.
      subst typ.
      exact bool_code.
    + destruct (nth_error input 4) as [op |] eqn:cell; try discriminate.
      destruct op; try discriminate.
      destruct (xops_b input (in_code index (XBytes n0))) eqn:bytes_code;
        try discriminate.
      apply xops_b_true in bytes_code.
      injection accepted as same.
      subst typ.
      exact bytes_code.
Qed.

Theorem out_read_code : forall first typ,
  out_read first (out_code first typ) = Some typ.
Proof.
  intros first typ.
  destruct typ.
  - unfold out_read.
    rewrite xops_b_refl.
    reflexivity.
  - unfold out_read.
    rewrite xops_b_false.
    2: unfold out_code; discriminate.
    rewrite xops_b_refl.
    reflexivity.
  - unfold out_read.
    rewrite xops_b_false.
    2: unfold out_code; discriminate.
    rewrite xops_b_false.
    2: unfold out_code; discriminate.
    change
      ((if xops_b (out_code first (XBytes n))
          (out_code first (XBytes n))
        then Some (XBytes n) else None) = Some (XBytes n)).
    rewrite xops_b_refl.
    reflexivity.
Qed.

Theorem out_encode_decode : forall first input typ,
  out_read first input = Some typ -> input = out_code first typ.
Proof.
  intros first input typ accepted.
  unfold out_read in accepted.
  destruct (xops_b input (out_code first XInt)) eqn:int_code.
  - apply xops_b_true in int_code.
    injection accepted as same.
    subst typ.
    exact int_code.
  - destruct (xops_b input (out_code first XBool)) eqn:bool_code.
    + apply xops_b_true in bool_code.
      injection accepted as same.
      subst typ.
      exact bool_code.
    + destruct (nth_error input 3) as [op |] eqn:cell; try discriminate.
      destruct op; try discriminate.
      destruct (xops_b input (out_code first (XBytes n0))) eqn:bytes_code;
        try discriminate.
      apply xops_b_true in bytes_code.
      injection accepted as same.
      subst typ.
      exact bytes_code.
Qed.

Theorem in_cost_exact : forall index typ,
  xops_cost (in_code index typ) = in_cost typ.
Proof.
  intros index typ.
  destruct typ; reflexivity.
Qed.

Theorem out_cost_exact : forall first typ,
  xops_cost (out_code first typ) = out_cost typ.
Proof.
  intros first typ.
  destruct typ; reflexivity.
Qed.

Theorem in_turn_code : forall index typ value,
  xvalue_b typ value = true ->
  in_turn index (in_code index typ) value =
    Some (value, in_run_cost typ value).
Proof.
  intros index typ value accepted.
  unfold in_turn.
  rewrite in_read_code, accepted.
  reflexivity.
Qed.

Theorem in_turn_refuse : forall index typ value,
  xvalue_b typ value = false ->
  in_turn index (in_code index typ) value = None.
Proof.
  intros index typ value refused.
  unfold in_turn.
  rewrite in_read_code, refused.
  reflexivity.
Qed.

Theorem in_turn_sound : forall index input value result cost,
  in_turn index input value = Some (result, cost) ->
  exists typ,
    input = in_code index typ /\
    xvalue_b typ value = true /\
    result = value /\
    cost = in_run_cost typ value.
Proof.
  intros index input value result cost accepted.
  unfold in_turn in accepted.
  destruct (in_read index input) as [typ |] eqn:read; try discriminate.
  destruct (xvalue_b typ value) eqn:typed; try discriminate.
  injection accepted as result_same cost_same.
  exists typ.
  repeat split.
  - apply in_encode_decode.
    exact read.
  - exact typed.
  - symmetry.
    exact result_same.
  - symmetry.
    exact cost_same.
Qed.

Theorem out_turn_code : forall first typ value,
  xvalue_b typ value = true ->
  out_turn first (out_code first typ) value =
    Some (value, out_run_cost typ value).
Proof.
  intros first typ value accepted.
  unfold out_turn.
  rewrite out_read_code, accepted.
  reflexivity.
Qed.

Theorem out_turn_refuse : forall first typ value,
  xvalue_b typ value = false ->
  out_turn first (out_code first typ) value = None.
Proof.
  intros first typ value refused.
  unfold out_turn.
  rewrite out_read_code, refused.
  reflexivity.
Qed.

Theorem out_turn_sound : forall first input value result cost,
  out_turn first input value = Some (result, cost) ->
  exists typ,
    input = out_code first typ /\
    xvalue_b typ value = true /\
    result = value /\
    cost = out_run_cost typ value.
Proof.
  intros first input value result cost accepted.
  unfold out_turn in accepted.
  destruct (out_read first input) as [typ |] eqn:read; try discriminate.
  destruct (xvalue_b typ value) eqn:typed; try discriminate.
  injection accepted as result_same cost_same.
  exists typ.
  repeat split.
  - apply out_encode_decode.
    exact read.
  - exact typed.
  - symmetry.
    exact result_same.
  - symmetry.
    exact cost_same.
Qed.

Theorem in_regs_safe : forall index typ,
  index < 60 -> xregs_b (in_code index typ) = true.
Proof.
  intros index typ limit.
  unfold xregs_b.
  destruct typ; cbn [in_code xreg_b forallb];
    repeat rewrite andb_true_iff; repeat split; try reflexivity;
    apply Nat.ltb_lt; lia.
Qed.

Theorem out_regs_safe : forall first typ,
  xregs_b (out_code first typ) = true.
Proof.
  intros first typ.
  destruct typ; reflexivity.
Qed.

Theorem frame_decode_encode : forall inputs output results,
  frame_b inputs output results = true ->
  frame_read (frame_bits inputs output results) =
    Some (inputs, output, results).
Proof.
  intros inputs output results valid.
  unfold frame_read, frame_bits.
  rewrite Ser.dec_enc.
  - rewrite valid.
    reflexivity.
  - apply frame_get_code.
Qed.

Theorem frame_encode_decode : forall input inputs output results,
  frame_read input = Some (inputs, output, results) ->
  frame_bits inputs output results = input.
Proof.
  intros input inputs output results accepted.
  unfold frame_read in accepted.
  destruct
    (Ser.dec
      (fun item =>
        let '(input_types, output_type, result_regs) := item in
        frame_code input_types output_type result_regs)
      frame_get input)
    as [[[found_inputs found_output] found_results] |] eqn:decoded;
    try discriminate.
  destruct (frame_b found_inputs found_output found_results) eqn:valid;
    try discriminate.
  inversion accepted; subst.
  unfold frame_bits.
  eapply Ser.enc_dec.
  exact decoded.
Qed.

Theorem layout_decode_encode : forall inputs output results,
  frame_b inputs output results = true ->
  layout_b inputs output results = true ->
  layout_read (frame_bits inputs output results) =
    Some (inputs, output, results).
Proof.
  intros inputs output results frame_ok layout_ok.
  unfold layout_read.
  rewrite frame_decode_encode, layout_ok.
  - reflexivity.
  - exact frame_ok.
Qed.

Theorem layout_encode_decode : forall input inputs output results,
  layout_read input = Some (inputs, output, results) ->
  frame_bits inputs output results = input.
Proof.
  intros input inputs output results accepted.
  unfold layout_read in accepted.
  destruct (frame_read input)
    as [[[found_inputs found_output] found_results] |] eqn:decoded;
    try discriminate.
  destruct (layout_b found_inputs found_output found_results);
    try discriminate.
  inversion accepted; subst.
  apply frame_encode_decode.
  exact decoded.
Qed.

Theorem layout_safe : forall inputs output results,
  layout_b inputs output results = true ->
  exists width cells form,
    input_layout inputs = Some (width, cells) /\
    otype_shape output = Some form /\
    width <= 60 /\
    cells + shape_cells form <= 4096 /\
    shape_width form = length results.
Proof.
  intros inputs output results accepted.
  unfold layout_b in accepted.
  destruct (input_layout inputs) as [[width cells] |] eqn:input_shape;
    try discriminate.
  destruct (otype_shape output) as [form |] eqn:output_shape;
    try discriminate.
  apply andb_true_iff in accepted as [accepted results_ok].
  apply andb_true_iff in accepted as [width_ok cells_ok].
  apply Nat.leb_le in width_ok.
  apply Nat.leb_le in cells_ok.
  apply Nat.eqb_eq in results_ok.
  exists width, cells, form.
  repeat split; assumption.
Qed.

Theorem frame_decode_unique : forall input left_inputs left_output left_results
    right_inputs right_output right_results,
  frame_read input = Some (left_inputs, left_output, left_results) ->
  frame_read input = Some (right_inputs, right_output, right_results) ->
  left_inputs = right_inputs /\ left_output = right_output /\
    left_results = right_results.
Proof.
  intros input left_inputs left_output left_results right_inputs right_output
    right_results left right.
  rewrite left in right.
  inversion right.
  repeat split; reflexivity.
Qed.

Theorem frame_types_safe : forall input inputs output results,
  frame_read input = Some (inputs, output, results) ->
  inputs <> [] /\ type_set_b inputs output = true.
Proof.
  intros input inputs output results accepted.
  unfold frame_read in accepted.
  destruct
    (Ser.dec
      (fun item =>
        let '(input_types, output_type, result_regs) := item in
        frame_code input_types output_type result_regs)
      frame_get input)
    as [[[found_inputs found_output] found_results] |] eqn:decoded;
    try discriminate.
  destruct (frame_b found_inputs found_output found_results) eqn:valid;
    try discriminate.
  inversion accepted; subst.
  unfold frame_b in valid.
  apply andb_true_iff in valid as [valid size_ok].
  apply andb_true_iff in valid as [valid results_ok].
  apply andb_true_iff in valid as [nonempty types].
  split.
  - apply negb_true_iff in nonempty.
    intro empty.
    subst.
    discriminate.
  - exact types.
Qed.

Theorem frame_results_safe : forall input inputs output results,
  frame_read input = Some (inputs, output, results) ->
  NoDup results /\ (forall value, In value results -> value < 61).
Proof.
  intros input inputs output results accepted.
  unfold frame_read in accepted.
  destruct
    (Ser.dec
      (fun item =>
        let '(input_types, output_type, result_regs) := item in
        frame_code input_types output_type result_regs)
      frame_get input)
    as [[[found_inputs found_output] found_results] |] eqn:decoded;
    try discriminate.
  destruct (frame_b found_inputs found_output found_results) eqn:valid;
    try discriminate.
  inversion accepted; subst.
  unfold frame_b in valid.
  apply andb_true_iff in valid as [valid size_ok].
  apply andb_true_iff in valid as [valid results_ok].
  apply andb_true_iff in valid as [nonempty types].
  apply result_regs_safe.
  exact results_ok.
Qed.

Theorem frame_size_safe : forall input inputs output results,
  frame_read input = Some (inputs, output, results) ->
  length input <= 4096 * 128.
Proof.
  intros input inputs output results accepted.
  pose proof frame_encode_decode input inputs output results accepted as exact.
  rewrite <- exact.
  unfold frame_read in accepted.
  destruct
    (Ser.dec
      (fun item =>
        let '(input_types, output_type, result_regs) := item in
        frame_code input_types output_type result_regs)
      frame_get input)
    as [[[found_inputs found_output] found_results] |] eqn:decoded;
    try discriminate.
  destruct (frame_b found_inputs found_output found_results) eqn:valid;
    try discriminate.
  inversion accepted; subst.
  unfold frame_b in valid.
  apply andb_true_iff in valid as [valid size_ok].
  apply andb_true_iff in valid as [valid results_ok].
  apply andb_true_iff in valid as [nonempty types].
  apply Nat.leb_le.
  exact size_ok.
Qed.

Theorem header_decode_encode : forall inputs output results,
  frame_b inputs output results = true ->
  header_read (header (frame_bits inputs output results)) =
    Some (inputs, output, results).
Proof.
  intros inputs output results valid.
  cbn [header_read header dispatch_label].
  apply frame_decode_encode.
  exact valid.
Qed.

Theorem header_cost_exact : forall frame,
  header_cost (header frame) = 15.
Proof.
  reflexivity.
Qed.

Theorem arg_read_code : forall start count,
  arg_read start (arg_code start count) = Some count.
Proof.
  intros start count.
  revert start.
  induction count; intros start; simpl.
  - reflexivity.
  - rewrite !Nat.eqb_refl, IHcount.
    reflexivity.
Qed.

Theorem arg_encode_decode : forall start input count,
  arg_read start input = Some count ->
  input = arg_code start count.
Proof.
  intros start input.
  revert start.
  induction input as [|op rest IH]; intros start count accepted.
  - simpl in accepted.
    inversion accepted; subst count.
    reflexivity.
  - destruct op; cbn [arg_read] in accepted; try discriminate.
    destruct
      (Nat.eqb n (S start) && Nat.eqb n0 (1001 + start))
      eqn:cells;
      try discriminate.
    destruct (arg_read (S start) rest) as [found |] eqn:read;
      try discriminate.
    injection accepted as count_same.
    apply andb_true_iff in cells as [reg_same addr_same].
    apply Nat.eqb_eq in reg_same.
    apply Nat.eqb_eq in addr_same.
    subst n n0 count.
    simpl.
    f_equal.
    apply IH.
    exact read.
Qed.

Theorem arg_cost_exact : forall start count,
  header_cost (arg_code start count) = 3 * count.
Proof.
  intros start count.
  revert start.
  induction count; intros start; simpl.
  - reflexivity.
  - rewrite IHcount.
    lia.
Qed.

Theorem arg_cells_safe : forall start count reg addr,
  start + count <= 60 ->
  In (HMem reg addr) (arg_code start count) ->
  start < reg /\ reg <= start + count /\ addr = 1000 + reg.
Proof.
  intros start count.
  revert start.
  induction count; intros start reg addr within present; simpl in present.
  - contradiction.
  - destruct present as [same | present].
    + inversion same; subst.
      repeat split; lia.
    + apply IHcount in present.
      * destruct present as [above [below exact]].
        repeat split; lia.
      * lia.
Qed.

Theorem layout_arg_safe : forall inputs output results,
  layout_b inputs output results = true ->
  exists width cells form,
    input_layout inputs = Some (width, cells) /\
    otype_shape output = Some form /\
    header_cost (arg_code 0 width) = 3 * width /\
    (forall reg addr,
      In (HMem reg addr) (arg_code 0 width) ->
      0 < reg /\ reg < 61 /\ addr = 1000 + reg).
Proof.
  intros inputs output results accepted.
  destruct (layout_safe inputs output results accepted)
    as [width [cells [form [input_shape [output_shape [width_ok _]]]]]].
  exists width, cells, form.
  split.
  - exact input_shape.
  - split.
    + exact output_shape.
    + split.
      * apply arg_cost_exact.
      * intros reg addr present.
        pose proof (arg_cells_safe 0 width reg addr width_ok present)
          as [positive [within exact]].
        repeat split; lia.
Qed.