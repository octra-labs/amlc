(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Require Import Uni.

Import ListNotations.

Definition chk := (ty * list atom * res * ctx)%type.

Fixpoint ty_dec (left right : ty) : {left = right} + {left <> right}.
Proof.
  decide equality.
  all: repeat decide equality.
Defined.

Definition ty_eqb (left right : ty) : bool :=
  if ty_dec left right then true else false.

Definition mul_dec (left right : mul) : {left = right} + {left <> right}.
Proof.
  decide equality.
  all: repeat decide equality.
Defined.

Fixpoint data_b (typ : ty) : bool :=
  match typ with
  | TUnit | TBool | TInt | TBytes _ | TEnc _ _ => true
  | TVec 0 _ => true
  | TVec (S _) elem => data_b elem
  | TCap _ => false
  | TPair first second | TSum first second => data_b first && data_b second
  end.

Fixpoint eq_b (typ : ty) : bool :=
  match typ with
  | TUnit | TBool | TInt | TBytes _ => true
  | TVec 0 _ => true
  | TVec (S _) elem => eq_b elem
  | TCap _ | TEnc _ _ => false
  | TPair first second | TSum first second => eq_b first && eq_b second
  end.
Definition cell_dec (left right : cell) : {left = right} + {left <> right}.
Proof.
  decide equality.
  all: try apply ty_dec.
  all: repeat decide equality.
Defined.

Definition ctx_dec (left right : ctx) : {left = right} + {left <> right} :=
  list_eq_dec cell_dec left right.

Definition ctx_eqb (left right : ctx) : bool :=
  if ctx_dec left right then true else false.

Definition fresh_b (id : nat) (gamma : ctx) : bool :=
  negb (existsb (Nat.eqb id) (ids gamma)).

Fixpoint bytes_b (bytes : list nat) : bool :=
  match bytes with
  | [] => true
  | byte :: rest => Nat.ltb byte 256 && bytes_b rest
  end.

Fixpoint takeb (id : nat) (gamma : ctx) : option (ty * ctx) :=
  match gamma with
  | [] => None
  | slot :: rest =>
      if Nat.eqb (cid slot) id then
        match cmul slot, clive slot with
        | M1, true =>
            Some (cty slot,
              Cell (cid slot) M1 (cty slot) false :: rest)
        | MM, live =>
            if data_b (cty slot) then Some (cty slot, slot :: rest)
            else None
        | _, _ => None
        end
      else
        match takeb id rest with
        | Some (typ, next) => Some (typ, slot :: next)
        | None => None
        end
  end.

Definition openb (binder : bind) (gamma : ctx) : option ctx :=
  if fresh_b (bid binder) gamma then
    match bmul binder with
    | M0 => if data_b (bty binder) then Some gamma else None
    | M1 => Some (Cell (bid binder) M1 (bty binder) true :: gamma)
    | MM =>
        if data_b (bty binder) then
          Some (Cell (bid binder) MM (bty binder) true :: gamma)
        else None
    end
  else None.

Definition closeb (binder : bind) (gamma : ctx) : option ctx :=
  match bmul binder with
  | M0 => Some gamma
  | M1 =>
      match gamma with
      | Cell id M1 typ false :: rest =>
          if Nat.eqb id (bid binder) && ty_eqb typ (bty binder) then
            Some rest
          else None
      | _ => None
      end
  | MM =>
      match gamma with
      | Cell id MM typ _ :: rest =>
          if Nat.eqb id (bid binder) && ty_eqb typ (bty binder) then
            Some rest
          else None
      | _ => None
      end
  end.

Definition ktype (value : value) (typ : ty) : bool :=
  match value, typ with
  | VUnit, TUnit => true
  | VBool _, TBool => true
  | VInt _, TInt => true
  | _, _ => false
  end.

Fixpoint checkb (gamma : ctx) (term : tm) : option chk :=
  match term with
  | K value typ =>
      if ktype value typ then Some (typ, [], rone, gamma) else None
  | Bytes bytes =>
      if bytes_b bytes then
        Some (TBytes (length bytes), [], rsucc (rscan (length bytes)), gamma)
      else None
  | Vnil elem => Some (TVec 0 elem, [], rone, gamma)
  | Var id =>
      match takeb id gamma with
      | Some (typ, next) => Some (typ, [], rone, next)
      | None => None
      end
  | Let binder value body =>
      match checkb gamma value with
      | Some (vtyp, vrow, vcost, vnext) =>
          if ty_eqb vtyp (bty binder) then
            match bmul binder with
            | M0 =>
                match vrow with
                | [] =>
                    if ctx_eqb vnext gamma then
                      match openb binder gamma with
                      | Some opened =>
                          match checkb opened body with
                          | Some (typ, row, cost, prior) =>
                              match closeb binder prior with
                              | Some next => Some (typ, row, rsucc cost, next)
                              | None => None
                              end
                          | None => None
                          end
                      | None => None
                      end
                    else None
                | _ => None
                end
            | M1 | MM =>
                match openb binder vnext with
                | Some opened =>
                    match checkb opened body with
                    | Some (typ, row, cost, prior) =>
                        match closeb binder prior with
                        | Some next =>
                            Some (typ, vrow ++ row,
                              rsucc (radd vcost cost), next)
                        | None => None
                        end
                    | None => None
                    end
                | None => None
                end
            end
          else None
      | None => None
      end
  | If guard yes no =>
      match checkb gamma guard with
      | Some (gtyp, grow, gcost, mid) =>
          if ty_eqb gtyp TBool then
            match checkb mid yes, checkb mid no with
            | Some (ytyp, yrow, ycost, ynext),
                Some (ntyp, nrow, ncost, nnext) =>
                if ty_eqb ytyp ntyp && ctx_eqb ynext nnext then
                  Some (ytyp, grow ++ yrow ++ nrow,
                    rsucc (radd gcost (rmax ycost ncost)), ynext)
                else None
            | _, _ => None
            end
          else None
      | None => None
      end
  | Pair ltm rtm =>
      match checkb gamma ltm with
      | Some (ltyp, lrow, lcost, mid) =>
          match checkb mid rtm with
          | Some (rtyp, rrow, rcost, next) =>
              Some (TPair ltyp rtyp, lrow ++ rrow,
                rsucc (radd lcost rcost), next)
          | None => None
          end
      | None => None
      end
  | Unpair src lb rb body =>
      match checkb gamma src with
      | Some (TPair ltyp rtyp, prow, pcost, mid) =>
          if ty_eqb (bty lb) ltyp && ty_eqb (bty rb) rtyp then
            match openb lb mid with
            | Some first =>
                match openb rb first with
                | Some second =>
                    match checkb second body with
                    | Some (typ, row, cost, prior) =>
                        match closeb rb prior with
                        | Some last =>
                            match closeb lb last with
                            | Some next =>
                                Some (typ, prow ++ row,
                                  rsucc (radd pcost cost), next)
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
          else None
      | _ => None
      end
  | Fst src =>
      match checkb gamma src with
      | Some (TPair ltyp rtyp, row, cost, next) =>
          if data_b rtyp then Some (ltyp, row, rsucc cost, next) else None
      | _ => None
      end
  | Snd src =>
      match checkb gamma src with
      | Some (TPair ltyp rtyp, row, cost, next) =>
          if data_b ltyp then Some (rtyp, row, rsucc cost, next) else None
      | _ => None
      end
  | Inl value rtyp =>
      match checkb gamma value with
      | Some (ltyp, row, cost, next) =>
          Some (TSum ltyp rtyp, row, rsucc cost, next)
      | None => None
      end
  | Inr ltyp value =>
      match checkb gamma value with
      | Some (rtyp, row, cost, next) =>
          Some (TSum ltyp rtyp, row, rsucc cost, next)
      | None => None
      end
  | Case value lb yes rb no =>
      match checkb gamma value with
      | Some (TSum ltyp rtyp, vrow, vcost, mid) =>
          if ty_eqb (bty lb) ltyp && ty_eqb (bty rb) rtyp then
            match openb lb mid, openb rb mid with
            | Some ly, Some ln =>
                match checkb ly yes, checkb ln no with
                | Some (ytyp, yrow, ycost, py),
                    Some (ntyp, nrow, ncost, pn) =>
                    match closeb lb py, closeb rb pn with
                    | Some ynext, Some nnext =>
                        if ty_eqb ytyp ntyp && ctx_eqb ynext nnext then
                          Some (ytyp, vrow ++ yrow ++ nrow,
                            rsucc (radd vcost (rmax ycost ncost)), ynext)
                        else None
                    | _, _ => None
                    end
                | _, _ => None
                end
            | _, _ => None
            end
          else None
      | _ => None
      end
  | Act action body =>
      match checkb gamma body with
      | Some (typ, row, cost, next) =>
          Some (typ, action :: row, rsucc cost, next)
      | None => None
      end
  | Add ltm rtm =>
      match checkb gamma ltm with
      | Some (ltyp, lrow, lcost, mid) =>
          if ty_eqb ltyp TInt then
            match checkb mid rtm with
            | Some (rtyp, rrow, rcost, next) =>
                if ty_eqb rtyp TInt then
                  Some (TInt, lrow ++ rrow,
                    rsucc (radd lcost rcost), next)
                else None
            | None => None
            end
          else None
      | None => None
      end
  | Sub ltm rtm =>
      match checkb gamma ltm with
      | Some (ltyp, lrow, lcost, mid) =>
          if ty_eqb ltyp TInt then
            match checkb mid rtm with
            | Some (rtyp, rrow, rcost, next) =>
                if ty_eqb rtyp TInt then
                  Some (TInt, lrow ++ rrow,
                    rsucc (radd lcost rcost), next)
                else None
            | None => None
            end
          else None
      | None => None
      end
  | Mul ltm rtm =>
      match checkb gamma ltm with
      | Some (ltyp, lrow, lcost, mid) =>
          if ty_eqb ltyp TInt then
            match checkb mid rtm with
            | Some (rtyp, rrow, rcost, next) =>
                if ty_eqb rtyp TInt then
                  Some (TInt, lrow ++ rrow,
                    rsucc (radd lcost rcost), next)
                else None
            | None => None
            end
          else None
      | None => None
      end
  | Div ltm rtm =>
      match checkb gamma ltm with
      | Some (ltyp, lrow, lcost, mid) =>
          if ty_eqb ltyp TInt then
            match checkb mid rtm with
            | Some (rtyp, rrow, rcost, next) =>
                if ty_eqb rtyp TInt then
                  Some (TInt, lrow ++ rrow,
                    rsucc (radd lcost rcost), next)
                else None
            | None => None
            end
          else None
      | None => None
      end
  | Mod ltm rtm =>
      match checkb gamma ltm with
      | Some (ltyp, lrow, lcost, mid) =>
          if ty_eqb ltyp TInt then
            match checkb mid rtm with
            | Some (rtyp, rrow, rcost, next) =>
                if ty_eqb rtyp TInt then
                  Some (TInt, lrow ++ rrow,
                    rsucc (radd lcost rcost), next)
                else None
            | None => None
            end
          else None
      | None => None
      end
  | Neg value | Abs value =>
      match checkb gamma value with
      | Some (typ, row, cost, next) =>
          if ty_eqb typ TInt then Some (TInt, row, rsucc cost, next)
          else None
      | None => None
      end
  | Eq expected ltm rtm =>
      match checkb gamma ltm with
      | Some (typ, lrow, lcost, mid) =>
          if ty_eqb expected typ && eq_b typ then
            match checkb mid rtm with
            | Some (rtyp, rrow, rcost, next) =>
                if ty_eqb typ rtyp then
                  Some (TBool, lrow ++ rrow,
                    radd (rsucc (radd lcost rcost)) (reffort (eqw typ)), next)
                else None
            | None => None
            end
          else None
      | None => None
      end
  | Cmp kind ltm rtm =>
      match checkb gamma ltm with
      | Some (ltyp, lrow, lcost, mid) =>
          if ty_eqb ltyp TInt then
            match checkb mid rtm with
            | Some (rtyp, rrow, rcost, next) =>
                if ty_eqb rtyp TInt then
                  Some (TBool, lrow ++ rrow,
                    rsucc (radd lcost rcost), next)
                else None
            | None => None
            end
          else None
      | None => None
      end
  | Cat ltm rtm =>
      match checkb gamma ltm with
      | Some (TBytes llen, lrow, lcost, mid) =>
          match checkb mid rtm with
          | Some (TBytes rlen, rrow, rcost, next) =>
              Some (TBytes (llen + rlen), lrow ++ rrow,
                rsucc (radd (radd lcost rcost) (rscan (llen + rlen))), next)
          | _ => None
          end
      | _ => None
      end
  | Take len value =>
      match checkb gamma value with
      | Some (TBytes total, row, cost, next) =>
          if Nat.leb len total then
            Some (TBytes len, row, rsucc (radd cost (rscan len)), next)
          else None
      | _ => None
      end
  | Drop len value =>
      match checkb gamma value with
      | Some (TBytes total, row, cost, next) =>
          if Nat.leb len total then
            Some (TBytes (total - len), row,
              rsucc (radd cost (rscan (total - len))), next)
          else None
      | _ => None
      end
  | Vcons first rest =>
      match checkb gamma first with
      | Some (elem, frow, fcost, mid) =>
          match checkb mid rest with
          | Some (TVec len relem, rrow, rcost, next) =>
              if ty_eqb elem relem then
                Some (TVec (S len) elem, frow ++ rrow,
                  rsucc (radd fcost rcost), next)
              else None
          | _ => None
          end
      | None => None
      end
  | Vcat ltm rtm =>
      match checkb gamma ltm with
      | Some (TVec llen elem, lrow, lcost, mid) =>
          match checkb mid rtm with
          | Some (TVec rlen relem, rrow, rcost, next) =>
              if ty_eqb elem relem then
                Some (TVec (llen + rlen) elem, lrow ++ rrow,
                  rsucc (radd (radd lcost rcost) (rscan (llen + rlen))), next)
              else None
          | _ => None
          end
      | _ => None
      end
  | At index value =>
      match checkb gamma value with
      | Some (TVec len elem, row, cost, next) =>
          if Nat.ltb index len && data_b elem then
            Some (elem, row, rsucc cost, next)
          else None
      | _ => None
      end
  | Uncons value =>
      match checkb gamma value with
      | Some (TVec (S len) elem, row, cost, next) =>
          Some (TPair elem (TVec len elem), row,
            rsucc (radd cost (rscan len)), next)
      | _ => None
      end
  | Fold n vector seed item state body =>
      match checkb gamma vector with
      | Some (TVec len elem, vrow, vcost, mid) =>
          if Nat.eqb n len && ty_eqb (bty item) elem then
            match checkb mid seed with
            | Some (acc, srow, scost, outer) =>
                if ty_eqb (bty state) acc then
                  match openb item outer with
                  | Some opened_item =>
                      match openb state opened_item with
                      | Some opened_state =>
                          match checkb opened_state body with
                          | Some (btyp, brow, bcost, prior) =>
                              if ty_eqb btyp acc then
                                match closeb state prior with
                                | Some after_state =>
                                    match closeb item after_state with
                                    | Some final =>
                                        if ctx_eqb final outer then
                                          Some (acc, vrow ++ srow ++ brow,
                                            rsucc (radd vcost
                                              (radd scost
                                                (rscale n (rsucc bcost)))), outer)
                                        else None
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
                else None
            | None => None
            end
          else None
      | _ => None
      end
  | Step cap value =>
      match checkb gamma cap with
      | Some (TCap kind, crow, ccost, mid) =>
          match checkb mid value with
          | Some (typ, vrow, vcost, next) =>
              Some (TPair (TCap kind) typ, crow ++ vrow ++ [AWrite kind],
                rsucc (radd ccost vcost), next)
          | None => None
          end
      | _ => None
      end
  | Close cap =>
      match checkb gamma cap with
      | Some (TCap kind, row, cost, next) =>
          Some (TUnit, row ++ [AClose kind], rsucc cost, next)
      | _ => None
      end
  end.