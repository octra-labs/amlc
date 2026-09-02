(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.

Import ListNotations.

Inductive mul : Type := M0 | M1 | MM.

Inductive ty : Type :=
| TUnit : ty
| TBool : ty
| TInt : ty
| TBytes : nat -> ty
| TVec : nat -> ty -> ty
| TCap : nat -> ty
| TEnc : nat -> nat -> ty
| TPair : ty -> ty -> ty
| TSum : ty -> ty -> ty.

Fixpoint data (typ : ty) : Prop :=
  match typ with
  | TUnit | TBool | TInt | TBytes _ | TEnc _ _ => True
  | TVec count elem =>
      match count with
      | 0 => True
      | S _ => data elem
      end
  | TCap _ => False
  | TPair first second | TSum first second => data first /\ data second
  end.

Fixpoint eqty (typ : ty) : Prop :=
  match typ with
  | TUnit | TBool | TInt | TBytes _ => True
  | TVec count elem =>
      match count with
      | 0 => True
      | S _ => eqty elem
      end
  | TCap _ | TEnc _ _ => False
  | TPair first second | TSum first second => eqty first /\ eqty second
  end.

Fixpoint eqw (typ : ty) : nat :=
  match typ with
  | TUnit | TBool | TInt | TCap _ | TEnc _ _ => 1
  | TBytes len => S len
  | TVec len elem => S (len * eqw elem)
  | TPair first second => S (eqw first + eqw second)
  | TSum first second => S (Nat.max (eqw first) (eqw second))
  end.

Inductive value : Type :=
| VUnit : value
| VBool : bool -> value
| VInt : Z -> value
| VBytes : list nat -> value
| VVec : list value -> value
| VCap : nat -> nat -> value
| VEnc : nat -> nat -> Z -> value
| VPair : value -> value -> value
| VInl : value -> value
| VInr : value -> value.

Definition field (value : Z) : Prop :=
  (0 <= value < 2 ^ 127 - 1)%Z.

Fixpoint value_eq_dec (left right : value) : {left = right} + {left <> right}.
Proof.
  decide equality.
  all: repeat decide equality.
Defined.

Definition value_eqb (left right : value) : bool :=
  if value_eq_dec left right then true else false.

Fixpoint vwork (typ : ty) (value : value) {struct typ} : nat :=
  match typ, value with
  | TUnit, VUnit | TBool, VBool _ | TInt, VInt _ | TCap _, VCap _ _
  | TEnc _ _, VEnc _ _ _ => 1
  | TBytes _, VBytes bytes => S (length bytes)
  | TVec _ elem, VVec values =>
      S (fold_right (fun value work => vwork elem value + work) 0 values)
  | TPair first_ty second_ty, VPair first second =>
      S (vwork first_ty first + vwork second_ty second)
  | TSum first_ty _, VInl item => S (vwork first_ty item)
  | TSum _ second_ty, VInr item => S (vwork second_ty item)
  | _, _ => 1
  end.

Definition cmpw (typ : ty) (left right : value) : nat :=
  Nat.max (vwork typ left) (vwork typ right).

Inductive hasv : value -> ty -> Prop :=
| HVUnit : hasv VUnit TUnit
| HVBool : forall flag, hasv (VBool flag) TBool
| HVInt : forall number, hasv (VInt number) TInt
| HVBytes : forall bytes,
    Forall (fun byte => byte < 256) bytes ->
    hasv (VBytes bytes) (TBytes (length bytes))
| HVVec : forall values elem,
    Forall (fun item => hasv item elem) values ->
    hasv (VVec values) (TVec (length values) elem)
| HVCap : forall kind id, hasv (VCap kind id) (TCap kind)
| HVEnc : forall key rem value,
    field value ->
    hasv (VEnc key rem value) (TEnc key rem)
| HVPair : forall left right left_ty right_ty,
    hasv left left_ty ->
    hasv right right_ty ->
    hasv (VPair left right) (TPair left_ty right_ty)
| HVInl : forall value left right,
    hasv value left ->
    hasv (VInl value) (TSum left right)
| HVInr : forall value left right,
    hasv value right ->
    hasv (VInr value) (TSum left right).

Lemma vlist_limit : forall values elem,
  Forall (fun value => hasv value elem) values ->
  (forall value, hasv value elem -> vwork elem value <= eqw elem) ->
  fold_right (fun value work => vwork elem value + work) 0 values <=
    length values * eqw elem.
Proof.
  intros values elem typed limit.
  induction typed.
  - simpl.
    lia.
  - simpl.
    pose proof (limit x H).
    nia.
Qed.

Lemma vwork_limit : forall typ value,
  hasv value typ ->
  vwork typ value <= eqw typ.
Proof.
  induction typ; intros value typed; inversion typed; subst; simpl; try lia.
  - pose proof (vlist_limit values typ H1 IHtyp).
    lia.
  - match goal with
    | first_ok : hasv ?first typ1, second_ok : hasv ?second typ2 |- _ =>
        pose proof (IHtyp1 first first_ok);
        pose proof (IHtyp2 second second_ok)
    end.
    lia.
  - match goal with
    | item_ok : hasv ?item typ1 |- _ => pose proof (IHtyp1 item item_ok)
    end.
    pose proof (Nat.le_max_l (eqw typ1) (eqw typ2)).
    lia.
  - match goal with
    | item_ok : hasv ?item typ2 |- _ => pose proof (IHtyp2 item item_ok)
    end.
    pose proof (Nat.le_max_r (eqw typ1) (eqw typ2)).
    lia.
Qed.

Lemma cmpw_limit : forall typ left right,
  hasv left typ ->
  hasv right typ ->
  cmpw typ left right <= eqw typ.
Proof.
  intros typ left right left_ok right_ok.
  unfold cmpw.
  apply Nat.max_lub.
  - apply vwork_limit with (value := left).
    exact left_ok.
  - apply vwork_limit with (value := right).
    exact right_ok.
Qed.

Inductive base : ty -> Prop :=
| BUnit : base TUnit
| BBool : base TBool
| BInt : base TInt.

Inductive atom : Type :=
| ARead : nat -> atom
| AWrite : nat -> atom
| AEmit : nat -> atom
| AFail : nat -> atom
| AClose : nat -> atom.

Inductive origin : Type :=
| ODirect : origin
| OHeld : nat -> nat -> origin.

Record action : Type := Action {
  aa : atom;
  av : value;
  ao : origin
}.

Definition atoms (actions : list action) : list atom := map aa actions.

Inductive rel : Type :=
| RLt : rel
| RLe : rel
| RGt : rel
| RGe : rel.

Definition relb (kind : rel) (left right : Z) : bool :=
  match kind with
  | RLt => Z.ltb left right
  | RLe => Z.leb left right
  | RGt => Z.ltb right left
  | RGe => Z.leb right left
  end.

Definition within (plan row : list atom) : Prop :=
  Forall (fun action => In action row) plan.

Record bind : Type := Bind {
  bid : nat;
  bmul : mul;
  bty : ty
}.

Inductive tm : Type :=
| K : value -> ty -> tm
| Bytes : list nat -> tm
| Vnil : ty -> tm
| Var : nat -> tm
| Let : bind -> tm -> tm -> tm
| If : tm -> tm -> tm -> tm
| Pair : tm -> tm -> tm
| Unpair : tm -> bind -> bind -> tm -> tm
| Fst : tm -> tm
| Snd : tm -> tm
| Inl : tm -> ty -> tm
| Inr : ty -> tm -> tm
| Case : tm -> bind -> tm -> bind -> tm -> tm
| Act : atom -> tm -> tm
| Add : tm -> tm -> tm
| Sub : tm -> tm -> tm
| Mul : tm -> tm -> tm
| Div : tm -> tm -> tm
| Mod : tm -> tm -> tm
| Neg : tm -> tm
| Abs : tm -> tm
| Eq : ty -> tm -> tm -> tm
| Cmp : rel -> tm -> tm -> tm
| Cat : tm -> tm -> tm
| Take : nat -> tm -> tm
| Drop : nat -> tm -> tm
| Vcons : tm -> tm -> tm
| Vcat : tm -> tm -> tm
| At : nat -> tm -> tm
| Uncons : tm -> tm
| Fold : nat -> tm -> tm -> bind -> bind -> tm -> tm
| Step : tm -> tm -> tm
| Close : tm -> tm.

Fixpoint vlist (elem : ty) (values : list tm) : tm :=
  match values with
  | [] => Vnil elem
  | first :: rest => Vcons first (vlist elem rest)
  end.

Record cell : Type := Cell {
  cid : nat;
  cmul : mul;
  cty : ty;
  clive : bool
}.

Definition ctx := list cell.

Fixpoint ids (gamma : ctx) : list nat :=
  match gamma with
  | [] => []
  | slot :: rest => cid slot :: ids rest
  end.

Definition fresh (id : nat) (gamma : ctx) : Prop := ~ In id (ids gamma).

Inductive takec : nat -> ctx -> ty -> ctx -> Prop :=
| TCOne : forall id typ rest,
    takec id (Cell id M1 typ true :: rest) typ
      (Cell id M1 typ false :: rest)
| TCMany : forall id typ live rest,
    data typ ->
    takec id (Cell id MM typ live :: rest) typ
      (Cell id MM typ live :: rest)
| TCNext : forall id typ head rest next,
    cid head <> id ->
    takec id rest typ next ->
    takec id (head :: rest) typ (head :: next).

Inductive openc : bind -> ctx -> ctx -> Prop :=
| OCZero : forall id typ gamma,
    data typ ->
    fresh id gamma ->
    openc (Bind id M0 typ) gamma gamma
| OCOne : forall id typ gamma,
    fresh id gamma ->
    openc (Bind id M1 typ) gamma (Cell id M1 typ true :: gamma)
| OCMany : forall id typ gamma,
    data typ ->
    fresh id gamma ->
    openc (Bind id MM typ) gamma (Cell id MM typ true :: gamma).

Inductive closec : bind -> ctx -> ctx -> Prop :=
| CCZero : forall id typ gamma,
    closec (Bind id M0 typ) gamma gamma
| CCOne : forall id typ gamma,
    closec (Bind id M1 typ) (Cell id M1 typ false :: gamma) gamma
| CCMany : forall id typ live gamma,
    closec (Bind id MM typ) (Cell id MM typ live :: gamma) gamma.

Inductive axis : Type := AxStep | AxDepth | AxWork.

Record res : Type := Res {
  rsteps : nat;
  rdepth : nat;
  rwork : nat
}.

Definition rat (axis : axis) (value : res) : nat :=
  match axis with
  | AxStep => rsteps value
  | AxDepth => rdepth value
  | AxWork => rwork value
  end.

Definition rzero : res := Res 0 0 0.
Definition rone : res := Res 1 0 1.
Definition rscan (steps : nat) : res := Res steps 0 steps.
Definition rlevel (depth : nat) : res := Res 0 depth 0.
Definition reffort (work : nat) : res := Res 0 0 work.
Definition radd (left right : res) : res :=
  Res (rsteps left + rsteps right) (rdepth left + rdepth right)
    (rwork left + rwork right).
Definition rsucc (value : res) : res := radd rone value.
Definition rmax (left right : res) : res :=
  Res (Nat.max (rsteps left) (rsteps right))
    (Nat.max (rdepth left) (rdepth right))
    (Nat.max (rwork left) (rwork right)).
Definition rscale (count : nat) (value : res) : res :=
  Res (count * rsteps value) (count * rdepth value)
    (count * rwork value).
Definition rle (left right : res) : Prop :=
  forall axis : axis, rat axis left <= rat axis right.

Lemma rle_intro : forall left right,
  rsteps left <= rsteps right ->
  rdepth left <= rdepth right ->
  rwork left <= rwork right ->
  rle left right.
Proof.
  intros left right steps depth work axis.
  destruct axis; assumption.
Qed.

Lemma rle_steps : forall left right,
  rle left right -> rsteps left <= rsteps right.
Proof.
  intros left right order.
  exact (order AxStep).
Qed.

Lemma rle_depth : forall left right,
  rle left right -> rdepth left <= rdepth right.
Proof.
  intros left right order.
  exact (order AxDepth).
Qed.

Lemma rle_work : forall left right,
  rle left right -> rwork left <= rwork right.
Proof.
  intros left right order.
  exact (order AxWork).
Qed.

Lemma rmax_l : forall left right, rle left (rmax left right).
Proof.
  intros [ls ld lw] [rs rd rw].
  apply rle_intro; apply Nat.le_max_l.
Qed.

Lemma rmax_r : forall left right, rle right (rmax left right).
Proof.
  intros [ls ld lw] [rs rd rw].
  apply rle_intro; apply Nat.le_max_r.
Qed.

Inductive check : ctx -> tm -> ty -> list atom -> res -> ctx -> Prop :=
| CK : forall gamma value typ,
    base typ ->
    hasv value typ ->
    check gamma (K value typ) typ [] rone gamma
| CBytes : forall gamma bytes,
    Forall (fun byte => byte < 256) bytes ->
    check gamma (Bytes bytes) (TBytes (length bytes)) []
      (rsucc (rscan (length bytes))) gamma
| CVnil : forall gamma elem,
    check gamma (Vnil elem) (TVec 0 elem) [] rone gamma
| CVar : forall gamma id typ next,
    takec id gamma typ next ->
    check gamma (Var id) typ [] rone next
| CLet0 : forall gamma id typ value body out row body_cost value_cost opened prior next,
    check gamma value typ [] value_cost gamma ->
    openc (Bind id M0 typ) gamma opened ->
    check opened body out row body_cost prior ->
    closec (Bind id M0 typ) prior next ->
    check gamma (Let (Bind id M0 typ) value body) out row
      (rsucc body_cost) next
| CLet1 : forall gamma id typ value body mid opened prior out row1 row2 cost1 cost2 next,
    check gamma value typ row1 cost1 mid ->
    openc (Bind id M1 typ) mid opened ->
    check opened body out row2 cost2 prior ->
    closec (Bind id M1 typ) prior next ->
    check gamma (Let (Bind id M1 typ) value body) out (row1 ++ row2)
      (rsucc (radd cost1 cost2)) next
| CLetM : forall gamma id typ value body mid opened prior out row1 row2 cost1 cost2 next,
    check gamma value typ row1 cost1 mid ->
    openc (Bind id MM typ) mid opened ->
    check opened body out row2 cost2 prior ->
    closec (Bind id MM typ) prior next ->
    check gamma (Let (Bind id MM typ) value body) out (row1 ++ row2)
      (rsucc (radd cost1 cost2)) next
| CIf : forall gamma guard yes no typ rowg rowy rown costg costy costn mid next,
    check gamma guard TBool rowg costg mid ->
    check mid yes typ rowy costy next ->
    check mid no typ rown costn next ->
    check gamma (If guard yes no) typ (rowg ++ rowy ++ rown)
      (rsucc (radd costg (rmax costy costn))) next
| CPair : forall gamma left right lty rty rowl rowr costl costr mid next,
    check gamma left lty rowl costl mid ->
    check mid right rty rowr costr next ->
    check gamma (Pair left right) (TPair lty rty) (rowl ++ rowr)
      (rsucc (radd costl costr)) next
| CUnpair : forall gamma pair left right body lty rty out rowp rowb costp costb mid first second prior last next,
    check gamma pair (TPair lty rty) rowp costp mid ->
    bty left = lty ->
    bty right = rty ->
    openc left mid first ->
    openc right first second ->
    check second body out rowb costb prior ->
    closec right prior last ->
    closec left last next ->
    check gamma (Unpair pair left right body) out (rowp ++ rowb)
      (rsucc (radd costp costb)) next
| CFst : forall gamma pair left right row cost next,
    data right ->
    check gamma pair (TPair left right) row cost next ->
    check gamma (Fst pair) left row (rsucc cost) next
| CSnd : forall gamma pair left right row cost next,
    data left ->
    check gamma pair (TPair left right) row cost next ->
    check gamma (Snd pair) right row (rsucc cost) next
| CInl : forall gamma value left right row cost next,
    check gamma value left row cost next ->
    check gamma (Inl value right) (TSum left right) row (rsucc cost) next
| CInr : forall gamma value left right row cost next,
    check gamma value right row cost next ->
    check gamma (Inr left value) (TSum left right) row (rsucc cost) next
| CCase : forall gamma value left yes right no lty rty out rowv rowy rown costv costy costn mid ly ln py pn next,
    check gamma value (TSum lty rty) rowv costv mid ->
    bty left = lty ->
    bty right = rty ->
    openc left mid ly ->
    check ly yes out rowy costy py ->
    closec left py next ->
    openc right mid ln ->
    check ln no out rown costn pn ->
    closec right pn next ->
    check gamma (Case value left yes right no) out (rowv ++ rowy ++ rown)
      (rsucc (radd costv (rmax costy costn))) next
| CAct : forall gamma action body typ row cost next,
    check gamma body typ row cost next ->
    check gamma (Act action body) typ (action :: row) (rsucc cost) next
| CAdd : forall gamma left right rowl rowr costl costr mid next,
    check gamma left TInt rowl costl mid ->
    check mid right TInt rowr costr next ->
    check gamma (Add left right) TInt (rowl ++ rowr)
      (rsucc (radd costl costr)) next
| CSub : forall gamma left right rowl rowr costl costr mid next,
    check gamma left TInt rowl costl mid ->
    check mid right TInt rowr costr next ->
    check gamma (Sub left right) TInt (rowl ++ rowr)
      (rsucc (radd costl costr)) next
| CMul : forall gamma left right rowl rowr costl costr mid next,
    check gamma left TInt rowl costl mid ->
    check mid right TInt rowr costr next ->
    check gamma (Mul left right) TInt (rowl ++ rowr)
      (rsucc (radd costl costr)) next
| CDiv : forall gamma left right rowl rowr costl costr mid next,
    check gamma left TInt rowl costl mid ->
    check mid right TInt rowr costr next ->
    check gamma (Div left right) TInt (rowl ++ rowr)
      (rsucc (radd costl costr)) next
| CMod : forall gamma left right rowl rowr costl costr mid next,
    check gamma left TInt rowl costl mid ->
    check mid right TInt rowr costr next ->
    check gamma (Mod left right) TInt (rowl ++ rowr)
      (rsucc (radd costl costr)) next
| CNeg : forall gamma value row cost next,
    check gamma value TInt row cost next ->
    check gamma (Neg value) TInt row (rsucc cost) next
| CAbs : forall gamma value row cost next,
    check gamma value TInt row cost next ->
    check gamma (Abs value) TInt row (rsucc cost) next
| CEq : forall gamma left right typ rowl rowr costl costr mid next,
    eqty typ ->
    check gamma left typ rowl costl mid ->
    check mid right typ rowr costr next ->
    check gamma (Eq typ left right) TBool (rowl ++ rowr)
      (radd (rsucc (radd costl costr)) (reffort (eqw typ))) next
| CCmp : forall gamma kind left right rowl rowr costl costr mid next,
    check gamma left TInt rowl costl mid ->
    check mid right TInt rowr costr next ->
    check gamma (Cmp kind left right) TBool (rowl ++ rowr)
      (rsucc (radd costl costr)) next
| CCat : forall gamma left right ln rn rowl rowr costl costr mid next,
    check gamma left (TBytes ln) rowl costl mid ->
    check mid right (TBytes rn) rowr costr next ->
    check gamma (Cat left right) (TBytes (ln + rn)) (rowl ++ rowr)
      (rsucc (radd (radd costl costr) (rscan (ln + rn)))) next
| CTake : forall gamma len value total row cost next,
    len <= total ->
    check gamma value (TBytes total) row cost next ->
    check gamma (Take len value) (TBytes len) row
      (rsucc (radd cost (rscan len))) next
| CDrop : forall gamma len value total row cost next,
    len <= total ->
    check gamma value (TBytes total) row cost next ->
    check gamma (Drop len value) (TBytes (total - len)) row
      (rsucc (radd cost (rscan (total - len)))) next
| CVcons : forall gamma first rest len elem rowf rowr costf costr mid next,
    check gamma first elem rowf costf mid ->
    check mid rest (TVec len elem) rowr costr next ->
    check gamma (Vcons first rest) (TVec (S len) elem) (rowf ++ rowr)
      (rsucc (radd costf costr)) next
| CVcat : forall gamma left right ln rn elem rowl rowr costl costr mid next,
    check gamma left (TVec ln elem) rowl costl mid ->
    check mid right (TVec rn elem) rowr costr next ->
    check gamma (Vcat left right) (TVec (ln + rn) elem) (rowl ++ rowr)
      (rsucc (radd (radd costl costr) (rscan (ln + rn)))) next
| CAt : forall gamma index value len elem row cost next,
    index < len ->
    data elem ->
    check gamma value (TVec len elem) row cost next ->
    check gamma (At index value) elem row (rsucc cost) next
| CUncons : forall gamma value len elem row cost next,
    check gamma value (TVec (S len) elem) row cost next ->
    check gamma (Uncons value) (TPair elem (TVec len elem)) row
      (rsucc (radd cost (rscan len))) next
| CFold : forall gamma n vector seed item state body elem acc rowv rows rowb costv costs costb mid outer opened_item opened_state prior after_state,
    check gamma vector (TVec n elem) rowv costv mid ->
    check mid seed acc rows costs outer ->
    bty item = elem ->
    bty state = acc ->
    openc item outer opened_item ->
    openc state opened_item opened_state ->
    check opened_state body acc rowb costb prior ->
    closec state prior after_state ->
    closec item after_state outer ->
    check gamma (Fold n vector seed item state body) acc
      (rowv ++ rows ++ rowb)
      (rsucc (radd costv (radd costs (rscale n (rsucc costb))))) outer
| CStep : forall gamma cap value kind typ rowc rowv costc costv mid next,
    check gamma cap (TCap kind) rowc costc mid ->
    check mid value typ rowv costv next ->
    check gamma (Step cap value) (TPair (TCap kind) typ)
      (rowc ++ rowv ++ [AWrite kind]) (rsucc (radd costc costv)) next
| CClose : forall gamma cap kind row cost next,
    check gamma cap (TCap kind) row cost next ->
    check gamma (Close cap) TUnit (row ++ [AClose kind])
      (rsucc cost) next.

Record slot : Type := Slot {
  sid : nat;
  smul : mul;
  sty : ty;
  sval : value;
  slive : bool
}.

Definition env := list slot.

Inductive env_ok : ctx -> env -> Prop :=
| EONil : env_ok [] []
| EOCons : forall id mode typ live value gamma sigma,
    hasv value typ ->
    env_ok gamma sigma ->
    env_ok (Cell id mode typ live :: gamma)
      (Slot id mode typ value live :: sigma).

Inductive takev : nat -> env -> value -> env -> Prop :=
| TVOne : forall id typ value rest,
    takev id (Slot id M1 typ value true :: rest) value
      (Slot id M1 typ value false :: rest)
| TVMany : forall id typ value live rest,
    takev id (Slot id MM typ value live :: rest) value
      (Slot id MM typ value live :: rest)
| TVNext : forall id value head rest next,
    sid head <> id ->
    takev id rest value next ->
    takev id (head :: rest) value (head :: next).

Inductive openv : bind -> value -> env -> env -> Prop :=
| OVZero : forall id typ value sigma,
    openv (Bind id M0 typ) value sigma sigma
| OVOne : forall id typ value sigma,
    openv (Bind id M1 typ) value sigma
      (Slot id M1 typ value true :: sigma)
| OVMany : forall id typ value sigma,
    openv (Bind id MM typ) value sigma
      (Slot id MM typ value true :: sigma).

Inductive closev : bind -> env -> env -> Prop :=
| CVZero : forall id typ sigma,
    closev (Bind id M0 typ) sigma sigma
| CVOne : forall id typ value sigma,
    closev (Bind id M1 typ) (Slot id M1 typ value false :: sigma) sigma
| CVMany : forall id typ value live sigma,
    closev (Bind id MM typ) (Slot id MM typ value live :: sigma) sigma.

Record run : Type := Run {
  rv : value;
  rp : list atom;
  ra : list action;
  rs : nat;
  rw : nat
}.

Definition used (out : run) : res := Res (rs out) 0 (rw out).

Ltac ruse :=
  repeat match goal with
  | order : rle ?left ?right |- _ =>
      let steps := fresh "steps" in
      let depth := fresh "depth" in
      let work := fresh "work" in
      pose proof (rle_steps left right order) as steps;
      pose proof (rle_depth left right order) as depth;
      pose proof (rle_work left right order) as work;
      clear order
  end.

Ltac rlia :=
  ruse;
  first
    [ apply rle_intro;
      unfold used, rzero, rone, rscan, reffort, radd, rsucc, rmax, rscale in *;
      simpl in *; lia
    | unfold used, rzero, rone, rscan, reffort, radd, rsucc, rmax, rscale in *;
      simpl in *; lia ].

Ltac rnia :=
  ruse;
  first
    [ apply rle_intro;
      unfold used, rzero, rone, rscan, reffort, radd, rsucc, rmax, rscale in *;
      simpl in *; nia
    | unfold used, rzero, rone, rscan, reffort, radd, rsucc, rmax, rscale in *;
      simpl in *; nia ].

Definition one (value : value) : run := Run value [] [] 1 1.

Definition seq (left right : run) (value : value) : run :=
  Run value (rp left ++ rp right) (ra left ++ ra right)
    (S (rs left + rs right))
    (S (rw left + rw right)).

Definition eqrun (typ : ty) (left right : run) : run :=
  Run (VBool (value_eqb (rv left) (rv right))) (rp left ++ rp right)
    (ra left ++ ra right)
    (S (rs left + rs right))
    (cmpw typ (rv left) (rv right) + S (rw left + rw right)).

Definition add_action (out : run) (atom : atom) (payload : value)
    (origin : origin) : run :=
  Run (rv out) (atom :: rp out)
    (Action atom payload origin :: ra out)
    (S (rs out)) (S (rw out)).

Fixpoint takef (id : nat) (sigma : env) : option (value * env) :=
  match sigma with
  | [] => None
  | slot :: rest =>
      if Nat.eqb (sid slot) id then
        match smul slot, slive slot with
        | M1, true =>
            Some (sval slot,
              Slot (sid slot) M1 (sty slot) (sval slot) false :: rest)
        | MM, _ => Some (sval slot, slot :: rest)
        | _, _ => None
        end
      else
        match takef id rest with
        | Some (value, next) => Some (value, slot :: next)
        | None => None
        end
  end.

Definition openf (binder : bind) (value : value) (sigma : env) : option env :=
  match bmul binder with
  | M0 => Some sigma
  | M1 => Some (Slot (bid binder) M1 (bty binder) value true :: sigma)
  | MM => Some (Slot (bid binder) MM (bty binder) value true :: sigma)
  end.

Definition closef (binder : bind) (sigma : env) : option env :=
  match bmul binder with
  | M0 => Some sigma
  | M1 =>
      match sigma with
      | Slot id M1 _ _ false :: rest =>
          if Nat.eqb id (bid binder) then Some rest else None
      | _ => None
      end
  | MM =>
      match sigma with
      | Slot id MM _ _ _ :: rest =>
          if Nat.eqb id (bid binder) then Some rest else None
      | _ => None
      end
  end.

Inductive reject : Type :=
| DivideZero : reject
| ModuloZero : reject.

Inductive ans : Type :=
| Done : run -> env -> ans
| Rejected : reject -> ans
| OutOfFuel : ans
| Stuck : ans.

Definition keep (fuel : nat) (out : run) (sigma : env) : ans :=
  if Nat.leb (rs out) fuel then Done out sigma else OutOfFuel.

Fixpoint run_fuel (fuel : nat) (sigma : env) (term : tm) {struct fuel} : ans :=
  match fuel with
  | 0 => OutOfFuel
  | S rest =>
      match term with
      | K value _ => keep fuel (one value) sigma
      | Bytes bytes =>
          keep fuel
            (Run (VBytes bytes) [] [] (S (length bytes)) (S (length bytes))) sigma
      | Vnil _ => keep fuel (one (VVec [])) sigma
      | Var id =>
          match takef id sigma with
          | Some (value, next) => keep fuel (one value) next
          | None => Stuck
          end
      | Let binder value body =>
          match bmul binder with
          | M0 =>
              match run_fuel rest sigma body with
              | Done out next =>
                  keep fuel
                    (Run (rv out) (rp out) (ra out)
                      (S (rs out)) (S (rw out))) next
              | Rejected reason => Rejected reason
              | OutOfFuel => OutOfFuel
              | Stuck => Stuck
              end
          | M1 | MM =>
              match run_fuel rest sigma value with
              | Done value_out mid =>
                  match openf binder (rv value_out) mid with
                  | Some opened =>
                      match run_fuel rest opened body with
                      | Done body_out prior =>
                          match closef binder prior with
                          | Some next =>
                              keep fuel (seq value_out body_out (rv body_out)) next
                          | None => Stuck
                          end
                      | Rejected reason => Rejected reason
                      | OutOfFuel => OutOfFuel
                      | Stuck => Stuck
                      end
                  | None => Stuck
                  end
              | Rejected reason => Rejected reason
              | OutOfFuel => OutOfFuel
              | Stuck => Stuck
              end
          end
      | If guard yes no =>
          match run_fuel rest sigma guard with
          | Done guard_out mid =>
              match rv guard_out with
              | VBool flag =>
                  match run_fuel rest mid (if flag then yes else no) with
                  | Done body_out next =>
                      keep fuel (seq guard_out body_out (rv body_out)) next
                  | Rejected reason => Rejected reason
                  | OutOfFuel => OutOfFuel
                  | Stuck => Stuck
                  end
              | _ => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Pair x y =>
          match run_fuel rest sigma x with
          | Done left_out mid =>
              match run_fuel rest mid y with
              | Done right_out next =>
                  keep fuel
                    (seq left_out right_out (VPair (rv left_out) (rv right_out))) next
              | Rejected reason => Rejected reason
              | OutOfFuel => OutOfFuel
              | Stuck => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Unpair pair_term lbind rbind body =>
          match run_fuel rest sigma pair_term with
          | Done pair_out mid =>
              match rv pair_out with
              | VPair lv rvv =>
                  match openf lbind lv mid with
                  | Some first =>
                      match openf rbind rvv first with
                      | Some second =>
                          match run_fuel rest second body with
                          | Done body_out prior =>
                              match closef rbind prior with
                              | Some last =>
                                  match closef lbind last with
                                  | Some next =>
                                      keep fuel
                                        (seq pair_out body_out (rv body_out)) next
                                  | None => Stuck
                                  end
                              | None => Stuck
                              end
                          | Rejected reason => Rejected reason
                          | OutOfFuel => OutOfFuel
                          | Stuck => Stuck
                          end
                      | None => Stuck
                      end
                  | None => Stuck
                  end
              | _ => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Fst pair_term =>
          match run_fuel rest sigma pair_term with
          | Done pair_out next =>
              match rv pair_out with
              | VPair first _ =>
                  keep fuel
                    (Run first (rp pair_out) (ra pair_out) (S (rs pair_out))
                      (S (rw pair_out))) next
              | _ => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Snd pair_term =>
          match run_fuel rest sigma pair_term with
          | Done pair_out next =>
              match rv pair_out with
              | VPair _ second =>
                  keep fuel
                    (Run second (rp pair_out) (ra pair_out) (S (rs pair_out))
                      (S (rw pair_out))) next
              | _ => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Inl value _ =>
          match run_fuel rest sigma value with
          | Done out next =>
              keep fuel
                (Run (VInl (rv out)) (rp out) (ra out)
                  (S (rs out)) (S (rw out))) next
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Inr _ value =>
          match run_fuel rest sigma value with
          | Done out next =>
              keep fuel
                (Run (VInr (rv out)) (rp out) (ra out)
                  (S (rs out)) (S (rw out))) next
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Case value lbind yes rbind no =>
          match run_fuel rest sigma value with
          | Done value_out mid =>
              match rv value_out with
              | VInl payload =>
                  match openf lbind payload mid with
                  | Some opened =>
                      match run_fuel rest opened yes with
                      | Done body_out prior =>
                          match closef lbind prior with
                          | Some next =>
                              keep fuel (seq value_out body_out (rv body_out)) next
                          | None => Stuck
                          end
                      | Rejected reason => Rejected reason
                      | OutOfFuel => OutOfFuel
                      | Stuck => Stuck
                      end
                  | None => Stuck
                  end
              | VInr payload =>
                  match openf rbind payload mid with
                  | Some opened =>
                      match run_fuel rest opened no with
                      | Done body_out prior =>
                          match closef rbind prior with
                          | Some next =>
                              keep fuel (seq value_out body_out (rv body_out)) next
                          | None => Stuck
                          end
                      | Rejected reason => Rejected reason
                      | OutOfFuel => OutOfFuel
                      | Stuck => Stuck
                      end
                  | None => Stuck
                  end
              | _ => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Act action body =>
          match run_fuel rest sigma body with
          | Done out next =>
              keep fuel
                (add_action out action (rv out) ODirect) next
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Add x y =>
          match run_fuel rest sigma x with
          | Done left_out mid =>
              match run_fuel rest mid y with
              | Done right_out next =>
                  match rv left_out, rv right_out with
                  | VInt x, VInt y =>
                      keep fuel (seq left_out right_out (VInt (Z.add x y))) next
                  | _, _ => Stuck
                  end
              | Rejected reason => Rejected reason
              | OutOfFuel => OutOfFuel
              | Stuck => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Sub x y =>
          match run_fuel rest sigma x with
          | Done left_out mid =>
              match run_fuel rest mid y with
              | Done right_out next =>
                  match rv left_out, rv right_out with
                  | VInt x, VInt y =>
                      keep fuel (seq left_out right_out (VInt (Z.sub x y))) next
                  | _, _ => Stuck
                  end
              | Rejected reason => Rejected reason
              | OutOfFuel => OutOfFuel
              | Stuck => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Mul x y =>
          match run_fuel rest sigma x with
          | Done left_out mid =>
              match run_fuel rest mid y with
              | Done right_out next =>
                  match rv left_out, rv right_out with
                  | VInt x, VInt y =>
                      keep fuel (seq left_out right_out (VInt (Z.mul x y))) next
                  | _, _ => Stuck
                  end
              | Rejected reason => Rejected reason
              | OutOfFuel => OutOfFuel
              | Stuck => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Div x y =>
          match run_fuel rest sigma x with
          | Done left_out mid =>
              match run_fuel rest mid y with
              | Done right_out next =>
                  match rv left_out, rv right_out with
                  | VInt x, VInt y =>
                      if Z.eqb y 0 then Rejected DivideZero
                      else keep fuel
                        (seq left_out right_out (VInt (Z.quot x y))) next
                  | _, _ => Stuck
                  end
              | Rejected reason => Rejected reason
              | OutOfFuel => OutOfFuel
              | Stuck => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Mod x y =>
          match run_fuel rest sigma x with
          | Done left_out mid =>
              match run_fuel rest mid y with
              | Done right_out next =>
                  match rv left_out, rv right_out with
                  | VInt x, VInt y =>
                      if Z.eqb y 0 then Rejected ModuloZero
                      else keep fuel
                        (seq left_out right_out (VInt (Z.rem x y))) next
                  | _, _ => Stuck
                  end
              | Rejected reason => Rejected reason
              | OutOfFuel => OutOfFuel
              | Stuck => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Neg value =>
          match run_fuel rest sigma value with
          | Done out next =>
              match rv out with
              | VInt number =>
                  keep fuel
                    (Run (VInt (Z.opp number)) (rp out)
                      (ra out)
                      (S (rs out)) (S (rw out))) next
              | _ => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Abs value =>
          match run_fuel rest sigma value with
          | Done out next =>
              match rv out with
              | VInt number =>
                  keep fuel
                    (Run (VInt (Z.abs number)) (rp out)
                      (ra out)
                      (S (rs out)) (S (rw out))) next
              | _ => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Eq typ x y =>
          match run_fuel rest sigma x with
          | Done left_out mid =>
              match run_fuel rest mid y with
              | Done right_out next =>
                  keep fuel (eqrun typ left_out right_out) next
              | Rejected reason => Rejected reason
              | OutOfFuel => OutOfFuel
              | Stuck => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Cmp kind x y =>
          match run_fuel rest sigma x with
          | Done left_out mid =>
              match run_fuel rest mid y with
              | Done right_out next =>
                  match rv left_out, rv right_out with
                  | VInt lhs, VInt rhs =>
                      keep fuel
                        (seq left_out right_out (VBool (relb kind lhs rhs)))
                        next
                  | _, _ => Stuck
                  end
              | Rejected reason => Rejected reason
              | OutOfFuel => OutOfFuel
              | Stuck => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Cat x y =>
          match run_fuel rest sigma x with
          | Done left_out mid =>
              match run_fuel rest mid y with
              | Done right_out next =>
                  match rv left_out, rv right_out with
                  | VBytes x, VBytes y =>
                      keep fuel
                        (Run (VBytes (x ++ y)) (rp left_out ++ rp right_out)
                          (ra left_out ++ ra right_out)
                          (S (rs left_out + rs right_out + length x + length y))
                          (S (rw left_out + rw right_out + length x + length y))) next
                  | _, _ => Stuck
                  end
              | Rejected reason => Rejected reason
              | OutOfFuel => OutOfFuel
              | Stuck => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Take len value =>
          match run_fuel rest sigma value with
          | Done out next =>
              match rv out with
              | VBytes bytes =>
                  if Nat.leb len (length bytes) then
                    keep fuel
                      (Run (VBytes (firstn len bytes)) (rp out)
                        (ra out)
                        (S (rs out + len)) (S (rw out + len))) next
                  else Stuck
              | _ => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Drop len value =>
          match run_fuel rest sigma value with
          | Done out next =>
              match rv out with
              | VBytes bytes =>
                  if Nat.leb len (length bytes) then
                    keep fuel
                      (Run (VBytes (skipn len bytes)) (rp out)
                        (ra out)
                        (S (rs out + length bytes - len))
                        (S (rw out + length bytes - len))) next
                  else Stuck
              | _ => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Vcons first rest_value =>
          match run_fuel rest sigma first with
          | Done first_out mid =>
              match run_fuel rest mid rest_value with
              | Done rest_out next =>
                  match rv rest_out with
                  | VVec values =>
                      keep fuel
                        (seq first_out rest_out
                          (VVec (rv first_out :: values))) next
                  | _ => Stuck
                  end
              | Rejected reason => Rejected reason
              | OutOfFuel => OutOfFuel
              | Stuck => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Vcat x y =>
          match run_fuel rest sigma x with
          | Done left_out mid =>
              match run_fuel rest mid y with
              | Done right_out next =>
                  match rv left_out, rv right_out with
                  | VVec x, VVec y =>
                      keep fuel
                        (Run (VVec (x ++ y)) (rp left_out ++ rp right_out)
                          (ra left_out ++ ra right_out)
                          (S (rs left_out + rs right_out + length x + length y))
                          (S (rw left_out + rw right_out + length x + length y))) next
                  | _, _ => Stuck
                  end
              | Rejected reason => Rejected reason
              | OutOfFuel => OutOfFuel
              | Stuck => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | At index value =>
          match run_fuel rest sigma value with
          | Done out next =>
              match rv out with
              | VVec values =>
                  match nth_error values index with
                  | Some item =>
                      keep fuel
                        (Run item (rp out) (ra out)
                          (S (rs out)) (S (rw out))) next
                  | None => Stuck
                  end
              | _ => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Uncons value =>
          match run_fuel rest sigma value with
          | Done out next =>
              match rv out with
              | VVec (first :: tail) =>
                  keep fuel
                    (Run (VPair first (VVec tail)) (rp out)
                      (ra out)
                      (S (rs out + length tail))
                      (S (rw out + length tail))) next
              | _ => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Fold n vector seed item state body =>
          match run_fuel rest sigma vector with
          | Done vector_out mid =>
              match rv vector_out with
              | VVec values =>
                  if Nat.eqb (length values) n then
                    match run_fuel rest mid seed with
                    | Done seed_out outer =>
                        match fold_fuel rest outer item state body values (rv seed_out) with
                        | Done fold_out next =>
                            keep fuel
                              (Run (rv fold_out)
                                (rp vector_out ++ rp seed_out ++ rp fold_out)
                                (ra vector_out ++ ra seed_out ++ ra fold_out)
                                (S (rs vector_out + rs seed_out + rs fold_out))
                                (S (rw vector_out + rw seed_out + rw fold_out))) next
                        | Rejected reason => Rejected reason
                        | OutOfFuel => OutOfFuel
                        | Stuck => Stuck
                        end
                    | Rejected reason => Rejected reason
                    | OutOfFuel => OutOfFuel
                    | Stuck => Stuck
                    end
                  else Stuck
              | _ => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Step cap value =>
          match run_fuel rest sigma cap with
          | Done cap_out mid =>
              match run_fuel rest mid value with
              | Done value_out next =>
                  match rv cap_out with
                  | VCap kind id =>
                      keep fuel
                        (Run (VPair (VCap kind id) (rv value_out))
                          (rp cap_out ++ rp value_out ++ [AWrite kind])
                          (ra cap_out ++ ra value_out ++
                            [Action (AWrite kind) (rv value_out) (OHeld kind id)])
                          (S (rs cap_out + rs value_out))
                          (S (rw cap_out + rw value_out))) next
                  | _ => Stuck
                  end
              | Rejected reason => Rejected reason
              | OutOfFuel => OutOfFuel
              | Stuck => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      | Close cap =>
          match run_fuel rest sigma cap with
          | Done out next =>
              match rv out with
              | VCap kind id =>
                  keep fuel
                    (Run VUnit (rp out ++ [AClose kind])
                      (ra out ++ [Action (AClose kind) VUnit (OHeld kind id)])
                      (S (rs out)) (S (rw out))) next
              | _ => Stuck
              end
          | Rejected reason => Rejected reason
          | OutOfFuel => OutOfFuel
          | Stuck => Stuck
          end
      end
  end

with fold_fuel (fuel : nat) (sigma : env) (item state : bind) (body : tm)
    (values : list value) (seed : value) {struct fuel} : ans :=
  match values with
  | [] => Done (Run seed [] [] 0 0) sigma
  | first :: rest =>
      match fuel with
      | 0 => OutOfFuel
      | S fuel_rest =>
          match openf item first sigma with
          | Some opened_item =>
              match openf state seed opened_item with
              | Some opened_state =>
                  match run_fuel fuel_rest opened_state body with
                  | Done head prior =>
                      match closef state prior with
                      | Some after_state =>
                          match closef item after_state with
                          | Some outer =>
                              match fold_fuel fuel_rest outer item state body rest (rv head) with
                              | Done tail next =>
                                  keep fuel
                                    (Run (rv tail) (rp head ++ rp tail)
                                      (ra head ++ ra tail)
                                      (S (rs head + rs tail))
                                      (S (rw head + rw tail))) next
                              | Rejected reason => Rejected reason
                              | OutOfFuel => OutOfFuel
                              | Stuck => Stuck
                              end
                          | None => Stuck
                          end
                      | None => Stuck
                      end
                  | Rejected reason => Rejected reason
                  | OutOfFuel => OutOfFuel
                  | Stuck => Stuck
                  end
              | None => Stuck
              end
          | None => Stuck
          end
      end
  end.

Inductive evalR : env -> tm -> run -> env -> Prop :=
| EK : forall sigma value typ,
    evalR sigma (K value typ) (one value) sigma
| EBytes : forall sigma bytes,
    evalR sigma (Bytes bytes)
      (Run (VBytes bytes) [] [] (S (length bytes)) (S (length bytes))) sigma
| EVnil : forall sigma elem,
    evalR sigma (Vnil elem) (one (VVec [])) sigma
| EVar : forall sigma id value next,
    takev id sigma value next ->
    evalR sigma (Var id) (one value) next
| ELet0 : forall sigma id typ value body out next,
    evalR sigma body out next ->
    evalR sigma (Let (Bind id M0 typ) value body)
      (Run (rv out) (rp out) (ra out) (S (rs out)) (S (rw out))) next
| ELet1 : forall sigma id typ value body value_out mid opened body_out prior next,
    evalR sigma value value_out mid ->
    openv (Bind id M1 typ) (rv value_out) mid opened ->
    evalR opened body body_out prior ->
    closev (Bind id M1 typ) prior next ->
    evalR sigma (Let (Bind id M1 typ) value body)
      (seq value_out body_out (rv body_out)) next
| ELetM : forall sigma id typ value body value_out mid opened body_out prior next,
    evalR sigma value value_out mid ->
    openv (Bind id MM typ) (rv value_out) mid opened ->
    evalR opened body body_out prior ->
    closev (Bind id MM typ) prior next ->
    evalR sigma (Let (Bind id MM typ) value body)
      (seq value_out body_out (rv body_out)) next
| EIfYes : forall sigma guard yes no guard_out mid body_out next,
    evalR sigma guard guard_out mid ->
    rv guard_out = VBool true ->
    evalR mid yes body_out next ->
    evalR sigma (If guard yes no)
      (seq guard_out body_out (rv body_out)) next
| EIfNo : forall sigma guard yes no guard_out mid body_out next,
    evalR sigma guard guard_out mid ->
    rv guard_out = VBool false ->
    evalR mid no body_out next ->
    evalR sigma (If guard yes no)
      (seq guard_out body_out (rv body_out)) next
| EPair : forall sigma left right left_out mid right_out next,
    evalR sigma left left_out mid ->
    evalR mid right right_out next ->
    evalR sigma (Pair left right)
      (seq left_out right_out (VPair (rv left_out) (rv right_out))) next
| EUnpair : forall sigma pair left right body pair_out mid lv rvv first second body_out prior last next,
    evalR sigma pair pair_out mid ->
    rv pair_out = VPair lv rvv ->
    openv left lv mid first ->
    openv right rvv first second ->
    evalR second body body_out prior ->
    closev right prior last ->
    closev left last next ->
    evalR sigma (Unpair pair left right body)
      (seq pair_out body_out (rv body_out)) next
| EFst : forall sigma pair pair_out next left right,
    evalR sigma pair pair_out next ->
    rv pair_out = VPair left right ->
    evalR sigma (Fst pair)
      (Run left (rp pair_out) (ra pair_out)
        (S (rs pair_out)) (S (rw pair_out))) next
| ESnd : forall sigma pair pair_out next left right,
    evalR sigma pair pair_out next ->
    rv pair_out = VPair left right ->
    evalR sigma (Snd pair)
      (Run right (rp pair_out) (ra pair_out)
        (S (rs pair_out)) (S (rw pair_out))) next
| EInl : forall sigma value right out next,
    evalR sigma value out next ->
    evalR sigma (Inl value right)
      (Run (VInl (rv out)) (rp out) (ra out)
        (S (rs out)) (S (rw out))) next
| EInr : forall sigma left value out next,
    evalR sigma value out next ->
    evalR sigma (Inr left value)
      (Run (VInr (rv out)) (rp out) (ra out)
        (S (rs out)) (S (rw out))) next
| ECaseL : forall sigma value left yes right no value_out mid payload opened body_out prior next,
    evalR sigma value value_out mid ->
    rv value_out = VInl payload ->
    openv left payload mid opened ->
    evalR opened yes body_out prior ->
    closev left prior next ->
    evalR sigma (Case value left yes right no)
      (seq value_out body_out (rv body_out)) next
| ECaseR : forall sigma value left yes right no value_out mid payload opened body_out prior next,
    evalR sigma value value_out mid ->
    rv value_out = VInr payload ->
    openv right payload mid opened ->
    evalR opened no body_out prior ->
    closev right prior next ->
    evalR sigma (Case value left yes right no)
      (seq value_out body_out (rv body_out)) next
| EAct : forall sigma action body out next,
    evalR sigma body out next ->
    evalR sigma (Act action body)
      (add_action out action (rv out) ODirect) next
| EAdd : forall sigma left right left_out mid right_out next x y,
    evalR sigma left left_out mid ->
    evalR mid right right_out next ->
    rv left_out = VInt x ->
    rv right_out = VInt y ->
    evalR sigma (Add left right)
      (seq left_out right_out (VInt (Z.add x y))) next
| ESub : forall sigma left right left_out mid right_out next x y,
    evalR sigma left left_out mid ->
    evalR mid right right_out next ->
    rv left_out = VInt x ->
    rv right_out = VInt y ->
    evalR sigma (Sub left right)
      (seq left_out right_out (VInt (Z.sub x y))) next
| EMul : forall sigma left right left_out mid right_out next x y,
    evalR sigma left left_out mid ->
    evalR mid right right_out next ->
    rv left_out = VInt x ->
    rv right_out = VInt y ->
    evalR sigma (Mul left right)
      (seq left_out right_out (VInt (Z.mul x y))) next
| EDiv : forall sigma left right left_out mid right_out next x y,
    evalR sigma left left_out mid ->
    evalR mid right right_out next ->
    rv left_out = VInt x ->
    rv right_out = VInt y ->
    y <> 0%Z ->
    evalR sigma (Div left right)
      (seq left_out right_out (VInt (Z.quot x y))) next
| EMod : forall sigma left right left_out mid right_out next x y,
    evalR sigma left left_out mid ->
    evalR mid right right_out next ->
    rv left_out = VInt x ->
    rv right_out = VInt y ->
    y <> 0%Z ->
    evalR sigma (Mod left right)
      (seq left_out right_out (VInt (Z.rem x y))) next
| ENeg : forall sigma value out next number,
    evalR sigma value out next ->
    rv out = VInt number ->
    evalR sigma (Neg value)
      (Run (VInt (Z.opp number)) (rp out) (ra out)
        (S (rs out)) (S (rw out))) next
| EAbs : forall sigma value out next number,
    evalR sigma value out next ->
    rv out = VInt number ->
    evalR sigma (Abs value)
      (Run (VInt (Z.abs number)) (rp out) (ra out)
        (S (rs out)) (S (rw out))) next
| EEq : forall sigma typ left right left_out mid right_out next,
    evalR sigma left left_out mid ->
    evalR mid right right_out next ->
    evalR sigma (Eq typ left right) (eqrun typ left_out right_out) next
| ECmp : forall sigma kind left right left_out mid right_out next x y,
    evalR sigma left left_out mid ->
    evalR mid right right_out next ->
    rv left_out = VInt x ->
    rv right_out = VInt y ->
    evalR sigma (Cmp kind left right)
      (seq left_out right_out (VBool (relb kind x y))) next
| ECat : forall sigma left right left_out mid right_out next x y,
    evalR sigma left left_out mid ->
    evalR mid right right_out next ->
    rv left_out = VBytes x ->
    rv right_out = VBytes y ->
    evalR sigma (Cat left right)
      (Run (VBytes (x ++ y)) (rp left_out ++ rp right_out)
        (ra left_out ++ ra right_out)
        (S (rs left_out + rs right_out + length x + length y))
        (S (rw left_out + rw right_out + length x + length y))) next
| ETake : forall sigma len value out next bytes,
    evalR sigma value out next ->
    rv out = VBytes bytes ->
    len <= length bytes ->
    evalR sigma (Take len value)
      (Run (VBytes (firstn len bytes)) (rp out)
        (ra out)
        (S (rs out + len)) (S (rw out + len))) next
| EDrop : forall sigma len value out next bytes,
    evalR sigma value out next ->
    rv out = VBytes bytes ->
    len <= length bytes ->
    evalR sigma (Drop len value)
      (Run (VBytes (skipn len bytes)) (rp out)
        (ra out)
        (S (rs out + length bytes - len))
        (S (rw out + length bytes - len))) next
| EVcons : forall sigma first rest first_out mid rest_out next values,
    evalR sigma first first_out mid ->
    evalR mid rest rest_out next ->
    rv rest_out = VVec values ->
    evalR sigma (Vcons first rest)
      (seq first_out rest_out (VVec (rv first_out :: values))) next
| EVcat : forall sigma left right left_out mid right_out next x y,
    evalR sigma left left_out mid ->
    evalR mid right right_out next ->
    rv left_out = VVec x ->
    rv right_out = VVec y ->
    evalR sigma (Vcat left right)
      (Run (VVec (x ++ y)) (rp left_out ++ rp right_out)
        (ra left_out ++ ra right_out)
        (S (rs left_out + rs right_out + length x + length y))
        (S (rw left_out + rw right_out + length x + length y))) next
| EAt : forall sigma index value out next values item,
    evalR sigma value out next ->
    rv out = VVec values ->
    nth_error values index = Some item ->
    evalR sigma (At index value)
      (Run item (rp out) (ra out) (S (rs out)) (S (rw out))) next
| EUncons : forall sigma value out next first rest,
    evalR sigma value out next ->
    rv out = VVec (first :: rest) ->
    evalR sigma (Uncons value)
      (Run (VPair first (VVec rest)) (rp out)
        (ra out)
        (S (rs out + length rest)) (S (rw out + length rest))) next
| EFold : forall sigma n vector seed item state body vector_out mid values seed_out outer fold_out next,
    evalR sigma vector vector_out mid ->
    rv vector_out = VVec values ->
    length values = n ->
    evalR mid seed seed_out outer ->
    foldR outer item state body values (rv seed_out) fold_out next ->
    evalR sigma (Fold n vector seed item state body)
      (Run (rv fold_out) (rp vector_out ++ rp seed_out ++ rp fold_out)
        (ra vector_out ++ ra seed_out ++ ra fold_out)
        (S (rs vector_out + rs seed_out + rs fold_out))
        (S (rw vector_out + rw seed_out + rw fold_out))) next
| EStep : forall sigma cap value cap_out mid value_out next kind id,
    evalR sigma cap cap_out mid ->
    evalR mid value value_out next ->
    rv cap_out = VCap kind id ->
    evalR sigma (Step cap value)
      (Run (VPair (VCap kind id) (rv value_out))
        (rp cap_out ++ rp value_out ++ [AWrite kind])
        (ra cap_out ++ ra value_out ++
          [Action (AWrite kind) (rv value_out) (OHeld kind id)])
        (S (rs cap_out + rs value_out))
        (S (rw cap_out + rw value_out))) next
| EClose : forall sigma cap out next kind id,
    evalR sigma cap out next ->
    rv out = VCap kind id ->
    evalR sigma (Close cap)
      (Run VUnit (rp out ++ [AClose kind])
        (ra out ++ [Action (AClose kind) VUnit (OHeld kind id)])
        (S (rs out)) (S (rw out))) next

with foldR : env -> bind -> bind -> tm -> list value -> value -> run -> env -> Prop :=
| FRNil : forall sigma item state body value,
    foldR sigma item state body [] value (Run value [] [] 0 0) sigma
| FRCons : forall sigma item state body first rest value opened_item opened_state head prior after_state outer tail next,
    openv item first sigma opened_item ->
    openv state value opened_item opened_state ->
    evalR opened_state body head prior ->
    closev state prior after_state ->
    closev item after_state outer ->
    foldR outer item state body rest (rv head) tail next ->
    foldR sigma item state body (first :: rest) value
      (Run (rv tail) (rp head ++ rp tail)
        (ra head ++ ra tail)
        (S (rs head + rs tail)) (S (rw head + rw tail))) next.

Scheme evalR_ind' := Induction for evalR Sort Prop
with foldR_ind' := Induction for foldR Sort Prop.

Combined Scheme run_ind from evalR_ind', foldR_ind'.

Theorem run_actions :
  (forall sigma term out next,
    evalR sigma term out next ->
    atoms (ra out) = rp out) /\
  (forall sigma item state body values seed out next,
    foldR sigma item state body values seed out next ->
    atoms (ra out) = rp out).
Proof.
  apply run_ind; intros;
    cbn [one seq eqrun add_action] in *;
    unfold atoms in *;
    cbn in *;
    repeat rewrite map_app;
    repeat match goal with
    | same : map aa (ra ?out) = rp ?out |- _ => rewrite same
    end;
    reflexivity.
Qed.

Corollary eval_actions : forall sigma term out next,
  evalR sigma term out next ->
  atoms (ra out) = rp out.
Proof.
  exact (proj1 run_actions).
Qed.

Corollary fold_actions : forall sigma item state body values seed out next,
  foldR sigma item state body values seed out next ->
  atoms (ra out) = rp out.
Proof.
  exact (proj2 run_actions).
Qed.

Lemma takef_run : forall id sigma value next,
  takev id sigma value next ->
  takef id sigma = Some (value, next).
Proof.
  intros id sigma value next read.
  induction read.
  - simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - simpl.
    rewrite Nat.eqb_refl.
    reflexivity.
  - simpl.
    destruct (Nat.eqb (sid head) id) eqn:same.
    + apply Nat.eqb_eq in same.
      contradiction.
    + rewrite IHread.
      reflexivity.
Qed.

Lemma openf_run : forall binder value sigma next,
  openv binder value sigma next ->
  openf binder value sigma = Some next.
Proof.
  intros binder value sigma next opened.
  inversion opened; reflexivity.
Qed.

Lemma closef_run : forall binder sigma next,
  closev binder sigma next ->
  closef binder sigma = Some next.
Proof.
  intros binder sigma next closed.
  inversion closed; subst; unfold closef; simpl; rewrite ?Nat.eqb_refl; reflexivity.
Qed.

Lemma keep_run : forall fuel out sigma,
  rs out <= fuel ->
  keep fuel out sigma = Done out sigma.
Proof.
  intros fuel out sigma enough.
  unfold keep.
  destruct (Nat.leb (rs out) fuel) eqn:within.
  - reflexivity.
  - apply Nat.leb_gt in within.
    lia.
Qed.

Lemma within_nil : forall row, within [] row.
Proof.
  intros row.
  constructor.
Qed.

Lemma within_one : forall action row,
  In action row ->
  within [action] row.
Proof.
  intros action row present.
  constructor.
  - exact present.
  - constructor.
Qed.

Lemma within_app : forall left right row,
  within left row ->
  within right row ->
  within (left ++ right) row.
Proof.
  intros left right row left_ok right_ok.
  unfold within in *.
  apply Forall_app.
  split; assumption.
Qed.

Lemma within_left : forall plan left right,
  within plan left ->
  within plan (left ++ right).
Proof.
  intros plan left right accepted.
  unfold within in *.
  apply Forall_impl with (P := fun action => In action left).
  - intros action present.
    apply in_or_app.
    left.
    exact present.
  - exact accepted.
Qed.

Lemma within_right : forall plan left right,
  within plan right ->
  within plan (left ++ right).
Proof.
  intros plan left right accepted.
  unfold within in *.
  apply Forall_impl with (P := fun action => In action right).
  - intros action present.
    apply in_or_app.
    right.
    exact present.
  - exact accepted.
Qed.

Lemma take_ok : forall id gamma typ next sigma,
  takec id gamma typ next ->
  env_ok gamma sigma ->
  exists value out,
    takev id sigma value out /\
    hasv value typ /\
    env_ok next out.
Proof.
  intros id gamma typ next sigma taken.
  revert sigma.
  induction taken; intros sigma matched.
  - inversion matched as [|id' mode' typ' live' item gamma' sigma' item_has tail_ok]; subst.
    exists item, (Slot id M1 typ item false :: sigma').
    split.
    + constructor.
    + split; [assumption | constructor; assumption].
  - inversion matched as [|id' mode' typ' live' item gamma' sigma' item_has tail_ok]; subst.
    exists item, (Slot id MM typ item live :: sigma').
    split.
    + constructor.
    + split; [assumption | constructor; assumption].
  - inversion matched as [|id' mode' typ' live' item gamma' sigma' item_has tail_ok]; subst.
    destruct (IHtaken sigma' tail_ok) as [found [out [read [typed rest_ok]]]].
    exists found, (Slot id' mode' typ' item live' :: out).
    split.
    + apply TVNext.
      * simpl.
        exact H.
      * exact read.
    + split.
      * exact typed.
      * constructor; assumption.
Qed.

Lemma open_ok : forall binder gamma next value sigma,
  openc binder gamma next ->
  hasv value (bty binder) ->
  env_ok gamma sigma ->
  exists out,
    openv binder value sigma out /\
    env_ok next out.
Proof.
  intros binder gamma next value sigma opened typed matched.
  inversion opened; subst.
  - exists sigma.
    split; [constructor | exact matched].
  - exists (Slot id M1 typ value true :: sigma).
    split.
    + constructor.
    + constructor; assumption.
  - exists (Slot id MM typ value true :: sigma).
    split.
    + constructor.
    + constructor; assumption.
Qed.

Lemma close_ok : forall binder gamma next sigma,
  closec binder gamma next ->
  env_ok gamma sigma ->
  exists out,
    closev binder sigma out /\
    env_ok next out.
Proof.
  intros binder gamma next sigma closed matched.
  inversion closed; subst.
  - exists sigma.
    split; [constructor | exact matched].
  - inversion matched; subst.
    exists sigma0.
    split; [constructor | assumption].
  - inversion matched; subst.
    exists sigma0.
    split; [constructor | assumption].
Qed.

Definition spentv (id : nat) (sigma : env) : Prop :=
  forall value next, ~ takev id sigma value next.

Lemma closev_one_spent : forall id typ sigma next,
  closev (Bind id M1 typ) sigma next ->
  spentv id sigma.
Proof.
  intros id typ sigma next closed value after taken.
  inversion closed; subst.
  inversion taken; subst; simpl in *; try discriminate; contradiction.
Qed.

Lemma nth_has : forall values elem index value,
  Forall (fun item => hasv item elem) values ->
  nth_error values index = Some value ->
  hasv value elem.
Proof.
  intros values elem.
  induction values as [|first rest repeat]; intros index value all found.
  - destruct index; discriminate.
  - inversion all; subst.
    destruct index.
    + inversion found; subst.
      assumption.
    + apply repeat with index.
      * assumption.
      * exact found.
Qed.

Lemma bytes_first : forall bytes len,
  Forall (fun byte => byte < 256) bytes ->
  Forall (fun byte => byte < 256) (firstn len bytes).
Proof.
  intros bytes len accepted.
  revert len.
  induction accepted; intros len.
  - destruct len; constructor.
  - destruct len.
    + constructor.
    + simpl.
      constructor; auto.
Qed.

Lemma bytes_skip : forall bytes len,
  Forall (fun byte => byte < 256) bytes ->
  Forall (fun byte => byte < 256) (skipn len bytes).
Proof.
  intros bytes len accepted.
  revert len.
  induction accepted; intros len.
  - destruct len; constructor.
  - destruct len.
    + simpl.
      constructor; assumption.
    + simpl.
      apply IHaccepted.
Qed.

Lemma fold_safe : forall outer opened_item opened_state prior after_state
  item state body elem acc row cost values seed sigma,
  openc item outer opened_item ->
  openc state opened_item opened_state ->
  closec state prior after_state ->
  closec item after_state outer ->
  bty item = elem ->
  bty state = acc ->
  (forall input,
    env_ok opened_state input ->
    exists out next,
      evalR input body out next /\
      env_ok prior next /\
      hasv (rv out) acc /\
      within (rp out) row /\
      rle (used out) cost) ->
  Forall (fun value => hasv value elem) values ->
  hasv seed acc ->
  env_ok outer sigma ->
  exists out next,
    foldR sigma item state body values seed out next /\
    env_ok outer next /\
    hasv (rv out) acc /\
    within (rp out) row /\
    rle (used out) (rscale (length values) (rsucc cost)).
Proof.
  intros outer opened_item opened_state prior after_state
    item state body elem acc row cost values.
  induction values as [|first rest repeat]; intros seed sigma
    item_open state_open state_close item_close item_ty state_ty body_safe
    values_ok seed_has sigma_ok.
  - exists (Run seed [] [] 0 0), sigma.
    split.
    + constructor.
    + repeat split; try assumption.
      * constructor.
      * rlia.
  - inversion values_ok as [|head tail first_has rest_has].
    assert (first_bind : hasv first (bty item)) by (rewrite item_ty; exact first_has).
    assert (seed_bind : hasv seed (bty state)) by (rewrite state_ty; exact seed_has).
    destruct (open_ok item outer opened_item first sigma item_open first_bind sigma_ok)
      as [item_env [item_run item_ok]].
    destruct (open_ok state opened_item opened_state seed item_env state_open seed_bind item_ok)
      as [state_env [state_run state_ok]].
    destruct (body_safe state_env state_ok)
      as [head_out [prior_env [head_run [prior_ok [head_has [head_eff head_cost]]]]]].
    destruct (close_ok state prior after_state prior_env state_close prior_ok)
      as [state_out [state_done state_out_ok]].
    destruct (close_ok item after_state outer state_out item_close state_out_ok)
      as [outer_env [item_done outer_ok]].
    destruct (repeat (rv head_out) outer_env item_open state_open state_close item_close
      item_ty state_ty body_safe rest_has head_has outer_ok)
      as [tail_out [next [tail_run [next_ok [tail_has [tail_eff tail_cost]]]]]].
    exists (Run (rv tail_out) (rp head_out ++ rp tail_out)
      (ra head_out ++ ra tail_out)
      (S (rs head_out + rs tail_out))
      (S (rw head_out + rw tail_out))), next.
    split.
    + eapply FRCons; eauto.
    + repeat split; try assumption.
      * apply within_app.
        -- exact head_eff.
        -- exact tail_eff.
      * rnia.
Qed.

Definition answer_ok (next : ctx) (typ : ty) (row : list atom) (cost : res)
    (answer : ans) : Prop :=
  match answer with
  | Done out final =>
      env_ok next final /\
      hasv (rv out) typ /\
      within (rp out) row /\
      rle (used out) cost
  | Rejected _ => True
  | OutOfFuel => False
  | Stuck => False
  end.

Lemma fold_answer : forall outer opened_item opened_state prior after_state
  item state body elem acc row cost values seed sigma,
  openc item outer opened_item ->
  openc state opened_item opened_state ->
  closec state prior after_state ->
  closec item after_state outer ->
  bty item = elem ->
  bty state = acc ->
  (forall input fuel,
    env_ok opened_state input ->
    rsteps cost <= fuel ->
    answer_ok prior acc row cost (run_fuel fuel input body)) ->
  Forall (fun value => hasv value elem) values ->
  hasv seed acc ->
  env_ok outer sigma ->
  forall fuel,
  rsteps (rscale (length values) (rsucc cost)) <= fuel ->
  answer_ok outer acc row (rscale (length values) (rsucc cost))
    (fold_fuel fuel sigma item state body values seed).
Proof.
  intros outer opened_item opened_state prior after_state
    item state body elem acc row cost values.
  induction values as [|first rest repeat]; intros seed sigma
    item_open state_open state_close item_close item_ty state_ty body_safe
    values_ok seed_has sigma_ok fuel enough.
  - destruct fuel; cbn [fold_fuel] in *.
    + repeat split; try assumption.
      * constructor.
      * rlia.
    + repeat split; try assumption.
      * constructor.
      * rlia.
  - inversion values_ok as [|head tail first_has rest_has].
    destruct fuel as [|fuel]; [simpl in enough; nia |].
    cbn [fold_fuel].
    assert (first_bind : hasv first (bty item)) by
      (rewrite item_ty; exact first_has).
    assert (seed_bind : hasv seed (bty state)) by
      (rewrite state_ty; exact seed_has).
    destruct (open_ok item outer opened_item first sigma item_open
      first_bind sigma_ok) as [item_env [item_run item_ok]].
    rewrite (openf_run _ _ _ _ item_run).
    destruct (open_ok state opened_item opened_state seed item_env state_open
      seed_bind item_ok) as [state_env [state_run state_ok]].
    rewrite (openf_run _ _ _ _ state_run).
    pose proof (body_safe state_env fuel state_ok ltac:(rnia)) as body_answer.
    destruct (run_fuel fuel state_env body) as
      [head_out prior_env|reason| |] eqn:body_run.
    + cbn in body_answer.
      destruct body_answer as [prior_ok [head_has [head_eff head_cost]]].
      destruct (close_ok state prior after_state prior_env state_close prior_ok)
        as [state_out [state_done state_out_ok]].
      rewrite (closef_run _ _ _ state_done).
      destruct (close_ok item after_state outer state_out item_close state_out_ok)
        as [outer_env [item_done outer_ok]].
      rewrite (closef_run _ _ _ item_done).
      pose proof (repeat (rv head_out) outer_env item_open state_open
        state_close item_close item_ty state_ty body_safe rest_has head_has
        outer_ok fuel ltac:(rnia)) as tail_answer.
      destruct (fold_fuel fuel outer_env item state body rest (rv head_out)) as
        [tail_out next|tail_reason| |] eqn:tail_run.
      * cbn in tail_answer.
        destruct tail_answer as [next_ok [tail_has [tail_eff tail_cost]]].
        rewrite keep_run by rnia.
        repeat split; try assumption.
        -- apply within_app; assumption.
        -- rnia.
      * exact I.
      * contradiction.
      * contradiction.
    + exact I.
    + contradiction.
    + contradiction.
Qed.

Ltac inspect_answer safe out final matched typed effects spent :=
  lazymatch type of safe with
  | answer_ok _ _ _ _ ?answer =>
      let ran := fresh "answer_run" in
      destruct answer as [out final|reason| |] eqn:ran;
      [ cbn [answer_ok] in safe;
        destruct safe as [matched [typed [effects spent]]]
      | exact I
      | contradiction
      | contradiction ]
  end.

Theorem sound_fuel : forall gamma term typ row cost next,
  check gamma term typ row cost next ->
  forall sigma fuel,
  env_ok gamma sigma ->
  rsteps cost <= fuel ->
  answer_ok next typ row cost (run_fuel fuel sigma term).
Proof.
  intros gamma term typ row cost next checked.
  induction checked; intros sigma fuel sigma_ok enough;
    destruct fuel as [|fuel].
  all: try (unfold rone, rscan, reffort, radd, rsucc, rmax, rscale in enough;
    simpl in enough; lia).
  all: cbn [run_fuel].
  - rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
    + rlia.
  - rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
      assumption.
    + constructor.
    + rlia.
  - rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
      constructor.
    + constructor.
    + rlia.
  - destruct (take_ok id gamma typ next sigma H sigma_ok)
      as [value [out [read [typed matched]]]].
    rewrite (takef_run _ _ _ _ read).
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
    + rlia.
  - inversion H; inversion H0; subst.
    pose proof (IHchecked2 sigma fuel sigma_ok ltac:(rlia)) as body_safe.
    inspect_answer body_safe body_out final final_ok body_has body_eff body_used.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as value_safe.
    inspect_answer value_safe value_out mid_env mid_ok value_has value_eff value_used.
    destruct (open_ok (Bind id M1 typ) mid opened (rv value_out) mid_env H
      value_has mid_ok) as [opened_env [open_run opened_ok]].
    rewrite (openf_run _ _ _ _ open_run).
    pose proof (IHchecked2 opened_env fuel opened_ok ltac:(rlia)) as body_safe.
    inspect_answer body_safe body_out prior_env prior_ok body_has body_eff body_used.
    destruct (close_ok (Bind id M1 typ) prior next prior_env H0 prior_ok)
      as [final [close_run final_ok]].
    rewrite (closef_run _ _ _ close_run).
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + apply within_app.
      * apply within_left.
        exact value_eff.
      * apply within_right.
        exact body_eff.
    + rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as value_safe.
    inspect_answer value_safe value_out mid_env mid_ok value_has value_eff value_used.
    destruct (open_ok (Bind id MM typ) mid opened (rv value_out) mid_env H
      value_has mid_ok) as [opened_env [open_run opened_ok]].
    rewrite (openf_run _ _ _ _ open_run).
    pose proof (IHchecked2 opened_env fuel opened_ok ltac:(rlia)) as body_safe.
    inspect_answer body_safe body_out prior_env prior_ok body_has body_eff body_used.
    destruct (close_ok (Bind id MM typ) prior next prior_env H0 prior_ok)
      as [final [close_run final_ok]].
    rewrite (closef_run _ _ _ close_run).
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + apply within_app.
      * apply within_left.
        exact value_eff.
      * apply within_right.
        exact body_eff.
    + rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as guard_safe.
    inspect_answer guard_safe guard_out mid_env mid_ok guard_has guard_eff guard_used.
    inversion guard_has; subst.
    destruct flag.
    + pose proof (IHchecked2 mid_env fuel mid_ok ltac:(rlia)) as body_safe.
      inspect_answer body_safe body_out final final_ok body_has body_eff body_used.
      rewrite keep_run by rlia.
      repeat split; try assumption.
      * apply within_app.
        -- apply within_left.
           exact guard_eff.
        -- apply within_right.
           apply within_left.
           exact body_eff.
      * pose proof (rmax_l costy costn).
        rlia.
    + pose proof (IHchecked3 mid_env fuel mid_ok ltac:(rlia)) as body_safe.
      inspect_answer body_safe body_out final final_ok body_has body_eff body_used.
      rewrite keep_run by rlia.
      repeat split; try assumption.
      * apply within_app.
        -- apply within_left.
           exact guard_eff.
        -- apply within_right.
           apply within_right.
           exact body_eff.
      * pose proof (rmax_r costy costn).
        rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as left_safe.
    inspect_answer left_safe left_out mid_env mid_ok left_has left_eff left_used.
    pose proof (IHchecked2 mid_env fuel mid_ok ltac:(rlia)) as right_safe.
    inspect_answer right_safe right_out final final_ok right_has right_eff right_used.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor; assumption.
    + apply within_app.
      * apply within_left.
        exact left_eff.
      * apply within_right.
        exact right_eff.
    + rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as pair_safe.
    inspect_answer pair_safe pair_out mid_env mid_ok pair_has pair_eff pair_used.
    inversion pair_has; subst.
    destruct (open_ok left mid first left0 mid_env ltac:(assumption)
      ltac:(assumption) mid_ok) as [left_env [left_open left_ok]].
    rewrite (openf_run _ _ _ _ left_open).
    destruct (open_ok right first second right0 left_env ltac:(assumption)
      ltac:(assumption) left_ok) as [right_env [right_open right_ok]].
    rewrite (openf_run _ _ _ _ right_open).
    pose proof (IHchecked2 right_env fuel right_ok ltac:(rlia)) as body_safe.
    inspect_answer body_safe body_out prior_env prior_ok body_has body_eff body_used.
    destruct (close_ok right prior last prior_env ltac:(assumption) prior_ok)
      as [right_done [right_close right_done_ok]].
    rewrite (closef_run _ _ _ right_close).
    destruct (close_ok left last next right_done ltac:(assumption) right_done_ok)
      as [final [left_close final_ok]].
    rewrite (closef_run _ _ _ left_close).
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + apply within_app.
      * apply within_left.
        exact pair_eff.
      * apply within_right.
        exact body_eff.
    + rlia.
  - pose proof (IHchecked sigma fuel sigma_ok ltac:(rlia)) as pair_safe.
    inspect_answer pair_safe pair_out final final_ok pair_has pair_eff pair_used.
    inversion pair_has; subst.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    rlia.
  - pose proof (IHchecked sigma fuel sigma_ok ltac:(rlia)) as pair_safe.
    inspect_answer pair_safe pair_out final final_ok pair_has pair_eff pair_used.
    inversion pair_has; subst.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    rlia.
  - pose proof (IHchecked sigma fuel sigma_ok ltac:(rlia)) as value_safe.
    inspect_answer value_safe out final final_ok typed eff cost_ok.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
      exact typed.
    + rlia.
  - pose proof (IHchecked sigma fuel sigma_ok ltac:(rlia)) as value_safe.
    inspect_answer value_safe out final final_ok typed eff cost_ok.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
      exact typed.
    + rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as value_safe.
    inspect_answer value_safe value_out mid_env mid_ok value_has value_eff value_used.
    inversion value_has; subst.
    + destruct (open_ok left mid ly value1 mid_env ltac:(assumption)
        ltac:(assumption) mid_ok) as [opened [open_run opened_ok]].
      rewrite (openf_run _ _ _ _ open_run).
      pose proof (IHchecked2 opened fuel opened_ok ltac:(rlia)) as body_safe.
      inspect_answer body_safe body_out prior_env prior_ok body_has body_eff body_used.
      destruct (close_ok left py next prior_env ltac:(assumption) prior_ok)
        as [final [close_run final_ok]].
      rewrite (closef_run _ _ _ close_run).
      rewrite keep_run by rlia.
      repeat split; try assumption.
      * apply within_app.
        -- apply within_left.
           exact value_eff.
        -- apply within_right.
           apply within_left.
           exact body_eff.
      * pose proof (rmax_l costy costn).
        rlia.
    + destruct (open_ok right mid ln value1 mid_env ltac:(assumption)
        ltac:(assumption) mid_ok) as [opened [open_run opened_ok]].
      rewrite (openf_run _ _ _ _ open_run).
      pose proof (IHchecked3 opened fuel opened_ok ltac:(rlia)) as body_safe.
      inspect_answer body_safe body_out prior_env prior_ok body_has body_eff body_used.
      destruct (close_ok right pn next prior_env ltac:(assumption) prior_ok)
        as [final [close_run final_ok]].
      rewrite (closef_run _ _ _ close_run).
      rewrite keep_run by rlia.
      repeat split; try assumption.
      * apply within_app.
        -- apply within_left.
           exact value_eff.
        -- apply within_right.
           apply within_right.
           exact body_eff.
      * pose proof (rmax_r costy costn).
        rlia.
  - pose proof (IHchecked sigma fuel sigma_ok ltac:(rlia)) as body_safe.
    inspect_answer body_safe out final final_ok typed eff cost_ok.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + unfold within in *.
      constructor.
      * left.
        reflexivity.
      * apply Forall_impl with (P := fun item => In item row).
        -- intros item present.
           right.
           exact present.
        -- exact eff.
    + rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as left_safe.
    inspect_answer left_safe left_out mid_env mid_ok left_has left_eff left_used.
    pose proof (IHchecked2 mid_env fuel mid_ok ltac:(rlia)) as right_safe.
    inspect_answer right_safe right_out final final_ok right_has right_eff right_used.
    inversion left_has; inversion right_has; subst.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
    + apply within_app.
      * apply within_left; exact left_eff.
      * apply within_right; exact right_eff.
    + rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as left_safe.
    inspect_answer left_safe left_out mid_env mid_ok left_has left_eff left_used.
    pose proof (IHchecked2 mid_env fuel mid_ok ltac:(rlia)) as right_safe.
    inspect_answer right_safe right_out final final_ok right_has right_eff right_used.
    inversion left_has; inversion right_has; subst.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
    + apply within_app.
      * apply within_left; exact left_eff.
      * apply within_right; exact right_eff.
    + rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as left_safe.
    inspect_answer left_safe left_out mid_env mid_ok left_has left_eff left_used.
    pose proof (IHchecked2 mid_env fuel mid_ok ltac:(rlia)) as right_safe.
    inspect_answer right_safe right_out final final_ok right_has right_eff right_used.
    inversion left_has; inversion right_has; subst.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
    + apply within_app.
      * apply within_left; exact left_eff.
      * apply within_right; exact right_eff.
    + rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as left_safe.
    inspect_answer left_safe left_out mid_env mid_ok left_has left_eff left_used.
    pose proof (IHchecked2 mid_env fuel mid_ok ltac:(rlia)) as right_safe.
    inspect_answer right_safe right_out final final_ok right_has right_eff right_used.
    inversion left_has; inversion right_has; subst.
    destruct (Z.eqb number0 0) eqn:zero.
    + exact I.
    + rewrite keep_run by rlia.
      repeat split; try assumption.
      * constructor.
      * apply within_app.
        -- apply within_left; exact left_eff.
        -- apply within_right; exact right_eff.
      * rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as left_safe.
    inspect_answer left_safe left_out mid_env mid_ok left_has left_eff left_used.
    pose proof (IHchecked2 mid_env fuel mid_ok ltac:(rlia)) as right_safe.
    inspect_answer right_safe right_out final final_ok right_has right_eff right_used.
    inversion left_has; inversion right_has; subst.
    destruct (Z.eqb number0 0) eqn:zero.
    + exact I.
    + rewrite keep_run by rlia.
      repeat split; try assumption.
      * constructor.
      * apply within_app.
        -- apply within_left; exact left_eff.
        -- apply within_right; exact right_eff.
      * rlia.
  - pose proof (IHchecked sigma fuel sigma_ok ltac:(rlia)) as value_safe.
    inspect_answer value_safe out final final_ok typed eff cost_ok.
    inversion typed; subst.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
    + rlia.
  - pose proof (IHchecked sigma fuel sigma_ok ltac:(rlia)) as value_safe.
    inspect_answer value_safe out final final_ok typed eff cost_ok.
    inversion typed; subst.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
    + rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as left_safe.
    inspect_answer left_safe left_out mid_env mid_ok left_has left_eff left_used.
    pose proof (IHchecked2 mid_env fuel mid_ok ltac:(rlia)) as right_safe.
    inspect_answer right_safe right_out final final_ok right_has right_eff right_used.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
    + apply within_app.
      * apply within_left; exact left_eff.
      * apply within_right; exact right_eff.
    + pose proof (cmpw_limit typ (rv left_out) (rv right_out) left_has right_has).
      rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as left_safe.
    inspect_answer left_safe left_out mid_env mid_ok left_has left_eff left_used.
    pose proof (IHchecked2 mid_env fuel mid_ok ltac:(rlia)) as right_safe.
    inspect_answer right_safe right_out final final_ok right_has right_eff right_used.
    inversion left_has; inversion right_has; subst.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
    + apply within_app.
      * apply within_left; exact left_eff.
      * apply within_right; exact right_eff.
    + rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as left_safe.
    inspect_answer left_safe left_out mid_env mid_ok left_has left_eff left_used.
    pose proof (IHchecked2 mid_env fuel mid_ok ltac:(rlia)) as right_safe.
    inspect_answer right_safe right_out final final_ok right_has right_eff right_used.
    inversion left_has; inversion right_has; subst.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + replace (length bytes + length bytes0) with (length (bytes ++ bytes0))
        by apply length_app.
      constructor.
      apply Forall_app.
      split; assumption.
    + apply within_app.
      * apply within_left; exact left_eff.
      * apply within_right; exact right_eff.
    + rlia.
  - pose proof (IHchecked sigma fuel sigma_ok ltac:(rlia)) as value_safe.
    inspect_answer value_safe out final final_ok typed eff cost_ok.
    inversion typed; subst.
    rewrite (proj2 (Nat.leb_le len (length bytes)) ltac:(assumption)).
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + change (hasv (VBytes (firstn len bytes)) (TBytes len)).
      replace (TBytes len) with (TBytes (length (firstn len bytes))).
      * constructor.
        apply bytes_first.
        assumption.
      * f_equal.
        rewrite length_firstn, Nat.min_l by assumption.
        reflexivity.
    + rlia.
  - pose proof (IHchecked sigma fuel sigma_ok ltac:(rlia)) as value_safe.
    inspect_answer value_safe out final final_ok typed eff cost_ok.
    inversion typed; subst.
    rewrite (proj2 (Nat.leb_le len (length bytes)) ltac:(assumption)).
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + change (hasv (VBytes (skipn len bytes)) (TBytes (length bytes - len))).
      replace (TBytes (length bytes - len))
        with (TBytes (length (skipn len bytes))).
      * constructor.
        apply bytes_skip.
        assumption.
      * f_equal.
        rewrite length_skipn.
        reflexivity.
    + rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as first_safe.
    inspect_answer first_safe first_out mid_env mid_ok first_has first_eff first_used.
    pose proof (IHchecked2 mid_env fuel mid_ok ltac:(rlia)) as rest_safe.
    inspect_answer rest_safe rest_out final final_ok rest_has rest_eff rest_used.
    inversion rest_has; subst.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
      constructor; assumption.
    + apply within_app.
      * apply within_left; exact first_eff.
      * apply within_right; exact rest_eff.
    + rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as left_safe.
    inspect_answer left_safe left_out mid_env mid_ok left_has left_eff left_used.
    pose proof (IHchecked2 mid_env fuel mid_ok ltac:(rlia)) as right_safe.
    inspect_answer right_safe right_out final final_ok right_has right_eff right_used.
    inversion left_has; inversion right_has; subst.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + change (hasv (VVec (values ++ values0))
        (TVec (length values + length values0) elem)).
      replace (TVec (length values + length values0) elem)
        with (TVec (length (values ++ values0)) elem).
      * constructor.
        apply Forall_app.
        split; assumption.
      * f_equal.
        apply length_app.
    + apply within_app.
      * apply within_left; exact left_eff.
      * apply within_right; exact right_eff.
    + rlia.
  - pose proof (IHchecked sigma fuel sigma_ok ltac:(rlia)) as value_safe.
    inspect_answer value_safe out final final_ok typed eff cost_ok.
    inversion typed; subst.
    destruct (nth_error values index) eqn:found.
    + rewrite keep_run by rlia.
      repeat split; try assumption.
      * eapply nth_has; eauto.
      * rlia.
    + apply nth_error_None in found.
      lia.
  - pose proof (IHchecked sigma fuel sigma_ok ltac:(rlia)) as value_safe.
    inspect_answer value_safe out final final_ok typed eff cost_ok.
    inversion typed; subst.
    destruct values as [|first rest].
    + discriminate.
    + rewrite keep_run by rlia.
      match goal with
      | accepted : Forall _ (first :: rest) |- _ =>
          inversion accepted; subst
      end.
      repeat split; try assumption.
      * constructor.
        -- assumption.
        -- change (hasv (VVec rest) (TVec len elem)).
           replace (TVec len elem) with (TVec (length rest) elem).
           ++ constructor.
              assumption.
           ++ f_equal.
              simpl in H0.
              lia.
      * rlia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as vector_safe.
    inspect_answer vector_safe vector_out mid_env mid_ok vector_has vector_eff vector_used.
    inversion vector_has; subst.
    rewrite Nat.eqb_refl.
    pose proof (IHchecked2 mid_env fuel mid_ok ltac:(rlia)) as seed_safe.
    inspect_answer seed_safe seed_out outer_env outer_ok seed_has seed_eff seed_used.
    pose proof (fold_answer outer opened_item opened_state prior after_state
      item state body _ _ rowb costb values (rv seed_out) outer_env
      ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)
      ltac:(reflexivity) ltac:(reflexivity) IHchecked3 ltac:(assumption)
      seed_has outer_ok fuel ltac:(rnia)) as folded_safe.
    inspect_answer folded_safe fold_out final final_ok fold_has fold_eff fold_used.
    rewrite keep_run by rnia.
    repeat split; try assumption.
    + apply within_app.
      * apply within_left.
        exact vector_eff.
      * apply within_app.
        -- apply within_right.
           apply within_left.
           exact seed_eff.
        -- apply within_right.
           apply within_right.
           exact fold_eff.
    + rnia.
  - pose proof (IHchecked1 sigma fuel sigma_ok ltac:(rlia)) as cap_safe.
    inspect_answer cap_safe cap_out mid_env mid_ok cap_has cap_eff cap_used.
    pose proof (IHchecked2 mid_env fuel mid_ok ltac:(rlia)) as value_safe.
    inspect_answer value_safe value_out final final_ok value_has value_eff value_used.
    inversion cap_has; subst.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + eapply HVPair.
      * apply HVCap.
      * exact value_has.
    + apply within_app.
      * apply within_left.
        exact cap_eff.
      * apply within_app.
        -- apply within_right.
           apply within_left.
           exact value_eff.
        -- apply within_right.
           apply within_right.
           apply within_one.
           simpl.
           auto.
    + rlia.
  - pose proof (IHchecked sigma fuel sigma_ok ltac:(rlia)) as cap_safe.
    inspect_answer cap_safe cap_out final final_ok cap_has cap_eff cap_used.
    inversion cap_has; subst.
    rewrite keep_run by rlia.
    repeat split; try assumption.
    + constructor.
    + apply within_app.
      * apply within_left.
        exact cap_eff.
      * apply within_right.
        apply within_one.
        simpl.
        auto.
    + rlia.
Qed.

Corollary sound : forall gamma term typ row cost next sigma,
  check gamma term typ row cost next ->
  env_ok gamma sigma ->
  answer_ok next typ row cost (run_fuel (rsteps cost) sigma term).
Proof.
  intros gamma term typ row cost next sigma checked matched.
  eapply sound_fuel; eauto.
Qed.

Corollary linear_once : forall gamma id typ opened body out row cost prior next value sigma,
  openc (Bind id M1 typ) gamma opened ->
  check opened body out row cost prior ->
  closec (Bind id M1 typ) prior next ->
  hasv value typ ->
  env_ok gamma sigma ->
  exists start,
    openv (Bind id M1 typ) value sigma start /\
    match run_fuel (rsteps cost) start body with
    | Done result final =>
        exists closed,
          closev (Bind id M1 typ) final closed /\
          env_ok next closed /\
          spentv id final
    | Rejected _ => True
    | OutOfFuel => False
    | Stuck => False
    end.
Proof.
  intros gamma id typ opened body out row cost prior next value sigma
    opened_ok checked closed_ok value_ok sigma_ok.
  destruct (open_ok (Bind id M1 typ) gamma opened value sigma
    opened_ok value_ok sigma_ok) as [start [started start_ok]].
  exists start.
  split.
  - exact started.
  - pose proof (sound opened body out row cost prior start checked start_ok)
      as safe.
    destruct (run_fuel (rsteps cost) start body) as
      [result final|reason| |] eqn:ran.
    + cbn [answer_ok] in safe.
      destruct safe as [final_ok _].
      destruct (close_ok (Bind id M1 typ) prior next final closed_ok final_ok)
        as [closed [stopped closed_env_ok]].
      exists closed.
      repeat split; try assumption.
      apply closev_one_spent with (typ := typ) (next := closed).
      exact stopped.
    + exact I.
    + contradiction.
    + contradiction.
Qed.

Corollary terminal : forall gamma term typ row cost next sigma,
  check gamma term typ row cost next ->
  env_ok gamma sigma ->
  (exists out final,
    run_fuel (rsteps cost) sigma term = Done out final) \/
  (exists reason,
    run_fuel (rsteps cost) sigma term = Rejected reason).
Proof.
  intros gamma term typ row cost next sigma checked matched.
  pose proof (sound gamma term typ row cost next sigma checked matched) as safe.
  destruct (run_fuel (rsteps cost) sigma term) as
    [out final|reason| |] eqn:ran.
  - left.
    eauto.
  - right.
    eauto.
  - contradiction.
  - contradiction.
Qed.

Corollary no_stuck : forall gamma term typ row cost next sigma,
  check gamma term typ row cost next ->
  env_ok gamma sigma ->
  run_fuel (rsteps cost) sigma term <> Stuck.
Proof.
  intros gamma term typ row cost next sigma checked matched stuck.
  pose proof (sound gamma term typ row cost next sigma checked matched) as safe.
  rewrite stuck in safe.
  exact safe.
Qed.