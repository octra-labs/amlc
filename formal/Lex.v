(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.

Require Import Rule.
Require Import Prof.
Require Import Text.

Import ListNotations.
Open Scope string_scope.

Inductive pay : Type :=
| PNil
| PName : string -> pay
| PNat : nat -> pay
| PHex : string -> pay.

Record pos : Type := Pos {
  p_off : nat;
  p_line : nat;
  p_col : nat
}.

Record span : Type := Span {
  s_first : pos;
  s_last : pos
}.

Record item : Type := Item {
  i_tok : tok;
  i_pay : pay;
  i_span : span
}.

Inductive cause : Type :=
| LSource : nat -> nat -> cause
| LTokens : nat -> nat -> cause
| LName : nat -> nat -> cause
| LNumber
| LHex
| LNest : nat -> nat -> cause
| LByte : nat -> cause
| LFuel.

Inductive reply : Type :=
| Pass : list item -> reply
| Fail : cause -> span -> reply.

Inductive move : Type :=
| Stay
| Open
| Shut.

Record pcut : Type := Pcut {
  pc_tok : tok;
  pc_raw : string;
  pc_rest : string;
  pc_move : move
}.

Record ncut : Type := Ncut {
  nc_raw : string;
  nc_val : string;
  nc_rest : string;
  nc_digits : nat;
  nc_under : bool
}.

Inductive add : Type :=
| Added : nat -> list item -> add
| Blocked : cause -> span -> add.

Definition zero : pos := Pos 0 1 1.

Definition code (value : ascii) : nat := nat_of_ascii value.

Definition byte (value : ascii) (want : nat) : bool :=
  Nat.eqb (code value) want.

Definition between (low value high : nat) : bool :=
  Nat.leb low value && Nat.leb value high.

Definition space (value : ascii) : bool :=
  byte value 32 || byte value 9 || byte value 13 || byte value 10.

Definition alpha (value : ascii) : bool :=
  let raw := code value in
  between 97 raw 122 || between 65 raw 90 || Nat.eqb raw 95.

Definition digit (value : ascii) : bool :=
  between 48 (code value) 57.

Definition alnum (value : ascii) : bool := alpha value || digit value.

Definition hex (value : ascii) : bool :=
  let raw := code value in
  between 48 raw 57 || between 97 raw 102 || between 65 raw 70.

Definition step (here : pos) (value : ascii) : pos :=
  if byte value 10 then
    Pos (S (p_off here)) (S (p_line here)) 1
  else
    Pos (S (p_off here)) (p_line here) (S (p_col here)).

Fixpoint walk (here : pos) (raw : string) : pos :=
  match raw with
  | EmptyString => here
  | String value rest => walk (step here value) rest
  end.

Fixpoint srev_at (src acc : string) : string :=
  match src with
  | EmptyString => acc
  | String value rest => srev_at rest (String value acc)
  end.

Definition srev (src : string) : string := srev_at src EmptyString.

Fixpoint size_at (src : string) (acc : nat) : nat :=
  match src with
  | EmptyString => acc
  | String _ rest => size_at rest (S acc)
  end.

Definition size (src : string) : nat := size_at src 0.

Fixpoint take_at (pred : ascii -> bool) (src acc : string)
    : string * string :=
  match src with
  | EmptyString => (srev acc, EmptyString)
  | String value rest =>
      if pred value then
        take_at pred rest (String value acc)
      else (srev acc, src)
  end.

Definition take (pred : ascii -> bool) (src : string) : string * string :=
  take_at pred src EmptyString.

Fixpoint ntake_at (src : string) (digits : nat) (under : bool)
    (raw plain : string) : ncut :=
  match src with
  | EmptyString =>
      Ncut (srev raw) (srev plain) EmptyString digits under
  | String value rest =>
      if digit value then
        ntake_at rest (S digits) false
          (String value raw) (String value plain)
      else if byte value 95 && negb (Nat.eqb digits 0) && negb under then
        ntake_at rest digits true (String value raw) plain
      else Ncut (srev raw) (srev plain) src digits under
  end.

Definition ntake (src : string) (digits : nat) (under : bool) : ncut :=
  ntake_at src digits under EmptyString EmptyString.

Definition dec_digit (value : ascii) : nat := code value - 48.

Fixpoint dec_at (acc : nat) (raw : string) : nat :=
  match raw with
  | EmptyString => acc
  | String value rest => dec_at (acc * 10 + dec_digit value) rest
  end.

Definition dec (raw : string) : nat := dec_at 0 raw.

Definition hex_digit (value : ascii) : nat :=
  let raw := code value in
  if between 48 raw 57 then raw - 48
  else if between 97 raw 102 then 10 + raw - 97
  else 10 + raw - 65.

Fixpoint hbytes_at (raw acc : string) : string :=
  match raw with
  | String high (String low rest) =>
      hbytes_at rest
        (String (ascii_of_nat (hex_digit high * 16 + hex_digit low)) acc)
  | _ => srev acc
  end.

Definition hbytes (raw : string) : string := hbytes_at raw EmptyString.

Definition words : list (string * tok) := [
  ("program", TProgram);
  ("size", TSize);
  ("measure", TMeasure);
  ("law", TLaw);
  ("input", TInput);
  ("term", TTerm);
  ("form", TForm);
  ("kind", TKind);
  ("marks", TMarks);
  ("under", TUnder);
  ("steps", TSteps);
  ("depth", TDepth);
  ("work", TWork);
  ("use", TUse);
  ("data", TData);
  ("shape", TShape);
  ("permit", TPermit);
  ("tag", TTag);
  ("make", TMake);
  ("erase", TErase);
  ("once", TOnce);
  ("many", TMany);
  ("unit", TUnit);
  ("bool", TBool);
  ("int", TInt);
  ("bytes", TBytes);
  ("vec", TVec);
  ("cap", TCap);
  ("result", TResult);
  ("res", TRes);
  ("let", TLet);
  ("in", TIn);
  ("split", TSplit);
  ("as", TAs);
  ("if", TIf);
  ("then", TThen);
  ("else", TElse);
  ("true", TTrue);
  ("false", TFalse);
  ("ok", TGood);
  ("err", TBad);
  ("case", TCase);
  ("of", TOf);
  ("fst", TFst);
  ("snd", TSnd);
  ("equal", TEqual);
  ("read", TRead);
  ("write", TWrite);
  ("emit", TEmit);
  ("fail", TFail);
  ("cat", TCat);
  ("take", TTake);
  ("drop", TDrop);
  ("vcat", TVcat);
  ("at", TAt);
  ("uncons", TUncons);
  ("fold", TFold);
  ("every", TEvery);
  ("some", TSome);
  ("count", TCount);
  ("total", TTotal);
  ("weave", TWeave);
  ("braid", TBraid);
  ("loom", TLoom);
  ("orbit", TOrbit);
  ("wake", TWake);
  ("rift", TRift);
  ("from", TFrom);
  ("with", TWith);
  ("step", TStep);
  ("close", TClose);
  ("max", TMax);
  ("abs", TAbs);
  ("recur", THold PRec);
  ("store", THold PStore);
  ("closure", THold PClos);
  ("raise", THold PRaise);
  ("dependent", THold PDep);
  ("polymark", THold PRow)
].

Fixpoint word_find (raw : string) (items : list (string * tok)) : option tok :=
  match items with
  | [] => None
  | (name, value) :: rest =>
      if String.eqb raw name then Some value else word_find raw rest
  end.

Definition keyword (raw : string) : tok :=
  match word_find raw words with
  | Some value => value
  | None => TName
  end.

Definition one (value : ascii) : string := String value EmptyString.

Definition two (first second : ascii) : string :=
  String first (String second EmptyString).

Definition single (value : ascii) (rest : string) (token : tok)
    (shift : move) : option pcut :=
  Some (Pcut token (one value) rest shift).

Definition pair (first second : ascii) (rest : string) (token : tok) :
    option pcut :=
  Some (Pcut token (two first second) rest Stay).

Definition punct (src : string) : option pcut :=
  match src with
  | EmptyString => None
  | String value rest =>
      if byte value 123 then single value rest TLbrace Open
      else if byte value 125 then single value rest TRbrace Shut
      else if byte value 40 then single value rest TLparen Open
      else if byte value 41 then single value rest TRparen Shut
      else if byte value 91 then single value rest TLbrack Open
      else if byte value 93 then single value rest TRbrack Shut
      else if byte value 58 then single value rest TColon Stay
      else if byte value 44 then single value rest TComma Stay
      else if byte value 124 then single value rest TBar Stay
      else if byte value 43 then single value rest TPlus Stay
      else if byte value 42 then single value rest TStar Stay
      else if byte value 47 then single value rest TSlash Stay
      else if byte value 37 then single value rest TPercent Stay
      else if byte value 45 then
        match rest with
        | String next tail =>
            if byte next 62 then pair value next tail TThin
            else single value rest TMinus Stay
        | EmptyString => single value rest TMinus Stay
        end
      else if byte value 60 then
        match rest with
        | String next tail =>
            if byte next 61 then pair value next tail TLe
            else single value rest TLt Stay
        | EmptyString => single value rest TLt Stay
        end
      else if byte value 62 then
        match rest with
        | String next tail =>
            if byte next 61 then pair value next tail TGe
            else single value rest TGt Stay
        | EmptyString => single value rest TGt Stay
        end
      else if byte value 61 then
        match rest with
        | String next tail =>
            if byte next 62 then pair value next tail TArrow
            else single value rest TEq Stay
        | EmptyString => single value rest TEq Stay
        end
      else None
  end.

Definition move_depth (shift : move) (depth : nat) : nat :=
  match shift with
  | Stay => depth
  | Open => S depth
  | Shut => Nat.pred depth
  end.

Definition put (first last : pos) (token : tok) (value : pay)
    (count : nat) (out : list item) : add :=
  let next := S count in
  let place := Span first last in
  if Nat.leb next (rtm_nodes local) then
    Added next (Item token value place :: out)
  else Blocked (LTokens (rtm_nodes local) next) place.

Definition put_reply (value : add) : option (nat * list item) * option reply :=
  match value with
  | Added count out => (Some (count, out), None)
  | Blocked cause place => (None, Some (Fail cause place))
  end.

Definition has_x (src : string) : bool :=
  match src with
  | String zero (String x _) => byte zero 48 && byte x 120
  | _ => false
  end.

Fixpoint loop (fuel : nat) (src : string) (here : pos) (depth count : nat)
    (out : list item) : reply :=
  match fuel with
  | O => Fail LFuel (Span here here)
  | S fuel_left =>
      match src with
      | EmptyString =>
          match put here here TEof PNil count out with
          | Added _ items => Pass (rev items)
          | Blocked cause place => Fail cause place
          end
      | String value _ =>
          if space value then
            let '(raw, rest) := take space src in
            loop fuel_left rest (walk here raw) depth count out
          else if has_x src then
            match src with
            | String zero (String x body) =>
                let '(digits, rest) := take hex body in
                let raw := String zero (String x digits) in
                let stop := walk here raw in
                let len := size digits in
                if Nat.odd len then Fail LHex (Span here stop)
                else
                  match put here stop THex (PHex (hbytes digits)) count out with
                  | Added count items => loop fuel_left rest stop depth count items
                  | Blocked cause place => Fail cause place
                  end
            | _ => Fail LFuel (Span here here)
            end
          else if digit value then
            let found := ntake src 0 false in
            let stop := walk here (nc_raw found) in
            if nc_under found
              || Nat.eqb (nc_digits found) 0
              || Nat.ltb (rtext local) (nc_digits found) then
              Fail LNumber (Span here stop)
            else
              match put here stop TNat (PNat (dec (nc_val found))) count out with
              | Added count items =>
                  loop fuel_left (nc_rest found) stop depth count items
              | Blocked cause place => Fail cause place
              end
          else if alpha value then
            let '(raw, rest) := take alnum src in
            let stop := walk here raw in
            let len := size raw in
            if Nat.ltb (rname local) len then
              Fail (LName (rname local) len) (Span here stop)
            else
              let token := keyword raw in
              let value :=
                match token with
                | TName => PName raw
                | _ => PNil
                end in
              match put here stop token value count out with
              | Added count items => loop fuel_left rest stop depth count items
              | Blocked cause place => Fail cause place
              end
          else
            match punct src with
            | Some found =>
                let stop := walk here (pc_raw found) in
                let next := move_depth (pc_move found) depth in
                if Nat.ltb (rtm_depth local) next then
                  Fail (LNest (rtm_depth local) next) (Span here stop)
                else
                  match put here stop (pc_tok found) PNil count out with
                  | Added count items =>
                      loop fuel_left (pc_rest found) stop next count items
                  | Blocked cause place => Fail cause place
                  end
            | None =>
                let stop := step here value in
                Fail (LByte (code value)) (Span here stop)
            end
      end
  end.

Definition scan (src : string) : reply :=
  let len := size src in
  if Nat.ltb (rstr local) len then
    Fail (LSource (rstr local) len) (Span zero zero)
  else loop (S len) src zero 0 0 [].

Inductive scanned : string -> list item -> Prop :=
| Scanned : forall src items, scan src = Pass items -> scanned src items.

Inductive refused : string -> cause -> span -> Prop :=
| Refused : forall src cause place,
    scan src = Fail cause place -> refused src cause place.

Theorem scan_sound : forall src items,
  scan src = Pass items -> scanned src items.
Proof.
  intros src items accepted. constructor. exact accepted.
Qed.

Theorem scan_complete : forall src items,
  scanned src items -> scan src = Pass items.
Proof.
  intros src items accepted. inversion accepted. assumption.
Qed.

Theorem scan_unique : forall src left right,
  scanned src left -> scanned src right -> left = right.
Proof.
  intros src left right lhs rhs.
  apply scan_complete in lhs. apply scan_complete in rhs.
  rewrite lhs in rhs. inversion rhs. reflexivity.
Qed.

Theorem put_limit : forall first last token value count out next items,
  put first last token value count out = Added next items ->
  next <= rtm_nodes local.
Proof.
  intros first last token value count out next items accepted.
  unfold put in accepted.
  destruct (Nat.leb (S count) (rtm_nodes local)) eqn:within;
    try discriminate.
  inversion accepted. subst.
  apply Nat.leb_le. exact within.
Qed.

Theorem source_refused : forall src,
  rstr local < size src ->
  scan src =
    Fail (LSource (rstr local) (size src)) (Span zero zero).
Proof.
  intros src over.
  unfold scan.
  destruct (Nat.ltb (rstr local) (size src)) eqn:within.
  - reflexivity.
  - apply Nat.ltb_ge in within. lia.
Qed.

Example empty_exact :
  scan EmptyString =
    Pass [Item TEof PNil (Span zero zero)].
Proof. reflexivity. Qed.

Example program_exact :
  scan "program" =
    Pass [
      Item TProgram PNil (Span zero (Pos 7 1 8));
      Item TEof PNil (Span (Pos 7 1 8) (Pos 7 1 8))
    ].
Proof. reflexivity. Qed.

Example name_exact :
  scan "value_7" =
    Pass [
      Item TName (PName "value_7") (Span zero (Pos 7 1 8));
      Item TEof PNil (Span (Pos 7 1 8) (Pos 7 1 8))
    ].
Proof. reflexivity. Qed.

Example number_exact :
  scan "1_024" =
    Pass [
      Item TNat (PNat 1024) (Span zero (Pos 5 1 6));
      Item TEof PNil (Span (Pos 5 1 6) (Pos 5 1 6))
    ].
Proof. reflexivity. Qed.

Example held_exact :
  scan "recur" =
    Pass [
      Item (THold PRec) PNil (Span zero (Pos 5 1 6));
      Item TEof PNil (Span (Pos 5 1 6) (Pos 5 1 6))
    ].
Proof. reflexivity. Qed.