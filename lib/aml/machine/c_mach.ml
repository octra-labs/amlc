(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type shape =
  | SUnit
  | SAtom
  | SPair of shape * shape
  | SVec of C_nat.t * shape

type code =
  | Done
  | Push of C_emit.lit * code
  | Void of code
  | Get of C_term.id * shape * code
  | Plus of code
  | Minus of code
  | Times of code
  | Quot of code
  | Rem of code
  | Negate of code
  | Absolute of code
  | Same of code
  | Join of code
  | Clip of C_nat.t * code
  | Skip of C_nat.t * code
  | Duo of code
  | First of code
  | Second of code
  | Empty of shape * code
  | Cons of code
  | Append of code
  | Pick of C_nat.t * code
  | Unhead of code
  | Effect of C_eff.atom * code
  | Scope of C_term.bind * code * code
  | Scope2 of C_term.bind * C_term.bind * code * code
  | Fork of shape * code * code * code

type loc =
  | LDone
  | LPush of C_lex.span * loc
  | LVoid of C_lex.span * loc
  | LGet of C_lex.span * loc
  | LPlus of C_lex.span * loc
  | LMinus of C_lex.span * loc
  | LTimes of C_lex.span * loc
  | LQuot of C_lex.span * loc
  | LRem of C_lex.span * loc
  | LNegate of C_lex.span * loc
  | LAbsolute of C_lex.span * loc
  | LSame of C_lex.span * loc
  | LJoin of C_lex.span * loc
  | LClip of C_nat.t * C_lex.span * loc
  | LSkip of C_nat.t * C_lex.span * loc
  | LDuo of C_lex.span * loc
  | LFirst of C_lex.span * loc
  | LSecond of C_lex.span * loc
  | LEmpty of C_lex.span * loc
  | LCons of C_lex.span * loc
  | LAppend of C_lex.span * loc
  | LPick of C_nat.t * C_lex.span * loc
  | LUnhead of C_lex.span * loc
  | LEffect of C_lex.span * loc
  | LScope of C_lex.span * loc * loc
  | LScope2 of C_lex.span * loc * loc
  | LFork of C_lex.span * C_lex.span * C_lex.span * loc * loc * loc

type t = {
  code : code;
  loc : loc;
  result : C_emit.lit;
  span : C_lex.span;
}

type error =
  | Source of C_parse.error
  | Feed of C_feed.error
  | Inputs of int
  | Effects of C_eff.atom list
  | Term
  | Run of C_eval.error
  | Plan of C_eff.atom list
  | Value of C_type.t * C_eval.value
  | Replay
  | Map

type tree = {
  at : C_lex.span;
  sub : tree list;
}

let ( let* ) value next =
  match value with
  | Ok value -> next value
  | Error error -> Error error

let equal left right =
  match left, right with
  | C_emit.Bool lhs, C_emit.Bool rhs -> Bool.equal lhs rhs
  | C_emit.Int lhs, C_emit.Int rhs -> Z.equal lhs rhs
  | C_emit.Bytes lhs, C_emit.Bytes rhs -> String.equal lhs rhs
  | C_emit.Data lhs, C_emit.Data rhs -> C_rval.equal lhs rhs
  | _ -> false

let atom_equal left right =
  match left, right with
  | C_eff.Read lhs, C_eff.Read rhs
  | C_eff.Write lhs, C_eff.Write rhs
  | C_eff.Emit lhs, C_eff.Emit rhs
  | C_eff.Fail lhs, C_eff.Fail rhs
  | C_eff.Close lhs, C_eff.Close rhs -> C_nat.equal lhs rhs
  | _ -> false

let rec plan_equal left right =
  match left, right with
  | [], [] -> true
  | lhs :: lrest, rhs :: rrest ->
    atom_equal lhs rhs && plan_equal lrest rrest
  | _ -> false

let literal typ value =
  match typ, value with
  | C_type.Bool, C_eval.Bool value -> Some (C_emit.Bool value)
  | C_type.Int, C_eval.Int value -> Some (C_emit.Int value)
  | C_type.Bytes size, C_eval.Bytes value
      when Z.equal (C_nat.to_z size) (Z.of_int (String.length value)) ->
      Some (C_emit.Bytes value)
  | _ ->
    begin
      match C_rval.make typ value with
      | Ok item -> Some (C_emit.Data item)
      | Error _ -> None
    end

let rec same_shape left right =
  match left, right with
  | SUnit, SUnit | SAtom, SAtom -> true
  | SPair (ll, lr), SPair (rl, rr) ->
    same_shape ll rl && same_shape lr rr
  | SVec (ln, le), SVec (rn, re) ->
    C_nat.equal ln rn && same_shape le re
  | _ -> false

let rec shape_of = function
  | C_type.Unit -> Some SUnit
  | C_type.Bool | C_type.Int | C_type.Bytes _ -> Some SAtom
  | C_type.Vec (len, elem) ->
    Option.map (fun item -> SVec (len, item)) (shape_of elem)
  | C_type.Pair (lhs, rhs) ->
    Option.bind (shape_of lhs) (fun lshape ->
      Option.map (fun rshape -> SPair (lshape, rshape)) (shape_of rhs))
  | C_type.Cap _ | C_type.Enc _ | C_type.Sum _ -> None

let rec shape_width = function
  | SUnit -> Z.zero
  | SAtom -> Z.one
  | SPair (lhs, rhs) -> Z.add (shape_width lhs) (shape_width rhs)
  | SVec (len, elem) -> Z.mul (C_nat.to_z len) (shape_width elem)

let rec same_shapes left right =
  match left, right with
  | [], [] -> true
  | lhs :: lrest, rhs :: rrest ->
    same_shape lhs rhs && same_shapes lrest rrest
  | _ -> false

let keep_shape tail = function
  | value :: rest when same_shapes rest tail -> Some value
  | _ -> None

let rec flow code stack =
  match code with
  | Done -> Some stack
  | Push (_, rest) -> flow rest (SAtom :: stack)
  | Void rest -> flow rest (SUnit :: stack)
  | Get (_, form, rest) -> flow rest (form :: stack)
  | Plus rest | Minus rest | Times rest | Quot rest | Rem rest
  | Same rest | Join rest ->
    begin
      match stack with
      | SAtom :: SAtom :: tail -> flow rest (SAtom :: tail)
      | _ -> None
    end
  | Negate rest | Absolute rest ->
    begin
      match stack with
      | SAtom :: tail -> flow rest (SAtom :: tail)
      | _ -> None
    end
  | Clip (_, rest) | Skip (_, rest) ->
    begin
      match stack with
      | SAtom :: tail -> flow rest (SAtom :: tail)
      | _ -> None
    end
  | Duo rest ->
    begin
      match stack with
      | rhs :: lhs :: tail -> flow rest (SPair (lhs, rhs) :: tail)
      | _ -> None
    end
  | First rest ->
    begin
      match stack with
      | SPair (lhs, _) :: tail -> flow rest (lhs :: tail)
      | _ -> None
    end
  | Second rest ->
    begin
      match stack with
      | SPair (_, rhs) :: tail -> flow rest (rhs :: tail)
      | _ -> None
    end
  | Empty (elem, rest) -> flow rest (SVec (C_nat.zero, elem) :: stack)
  | Cons rest ->
    begin
      match stack with
      | SVec (len, elem) :: item :: tail when same_shape item elem ->
        Option.bind (C_nat.add len C_nat.one) (fun next ->
          flow rest (SVec (next, elem) :: tail))
      | _ -> None
    end
  | Append rest ->
    begin
      match stack with
      | SVec (rn, re) :: SVec (ln, le) :: tail when same_shape le re ->
        Option.bind (C_nat.add ln rn) (fun len ->
          flow rest (SVec (len, le) :: tail))
      | _ -> None
    end
  | Pick (index, rest) ->
    begin
      match stack with
      | SVec (len, elem) :: tail when C_nat.lt index len ->
        flow rest (elem :: tail)
      | _ -> None
    end
  | Unhead rest ->
    begin
      match stack with
      | SVec (len, elem) :: tail ->
        Option.bind (C_nat.sub len C_nat.one) (fun next ->
          flow rest (SPair (elem, SVec (next, elem)) :: tail))
      | _ -> None
    end
  | Effect (_, rest) -> flow rest stack
  | Scope (_, body, rest) ->
    begin
      match stack with
      | _ :: tail ->
        Option.bind (flow body tail) (fun after ->
          Option.bind (keep_shape tail after) (fun out ->
            flow rest (out :: tail)))
      | [] -> None
    end
  | Scope2 (_, _, body, rest) ->
    begin
      match stack with
      | SPair _ :: tail ->
        Option.bind (flow body tail) (fun after ->
          Option.bind (keep_shape tail after) (fun out ->
            flow rest (out :: tail)))
      | _ -> None
    end
  | Fork (form, yes, no, rest) ->
    begin
      match stack with
      | SAtom :: tail ->
        Option.bind (flow yes tail) (fun yafter ->
          Option.bind (flow no tail) (fun nafter ->
            Option.bind (keep_shape tail yafter) (fun yout ->
              Option.bind (keep_shape tail nafter) (fun nout ->
                if same_shape form yout && same_shape form nout then
                  flow rest (form :: tail)
                else None))))
      | _ -> None
    end

let one_shape code =
  match flow code [] with
  | Some [value] -> Some value
  | _ -> None

let rec find_bind id = function
  | [] -> None
  | item :: _ when C_nat.equal id item.C_term.id -> Some item
  | _ :: rest -> find_bind id rest

let rec build env term rest =
  match term with
  | C_term.Unit -> Some (Void rest)
  | C_term.Bool value -> Some (Push (C_emit.Bool value, rest))
  | C_term.Int value -> Some (Push (C_emit.Int value, rest))
  | C_term.Bytes value -> Some (Push (C_emit.Bytes value, rest))
  | C_term.Vec (elem, values) ->
    Option.bind (shape_of elem) (fun form ->
      build_vec env form values rest)
  | C_term.Var id ->
    Option.bind (find_bind id env) (fun item ->
      Option.map (fun form -> Get (id, form, rest)) (shape_of item.typ))
  | C_term.Let (item, value, body) ->
    begin
      match item.mul with
      | C_type.Zero -> build (item :: env) body rest
      | C_type.One | C_type.Many ->
        Option.bind (build (item :: env) body Done) (fun body_code ->
          build env value (Scope (item, body_code, rest)))
    end
  | C_term.If (guard, yes, no) ->
    Option.bind (build env yes Done) (fun yes_code ->
      Option.bind (build env no Done) (fun no_code ->
        Option.bind (one_shape yes_code) (fun yes_shape ->
          Option.bind (one_shape no_code) (fun no_shape ->
            if same_shape yes_shape no_shape then
              build env guard (Fork (yes_shape, yes_code, no_code, rest))
            else None))))
  | C_term.Pair (lhs, rhs) ->
    Option.bind (build env rhs (Duo rest)) (fun rhs_code ->
      build env lhs rhs_code)
  | C_term.Unpair (value, lhs, rhs, body) ->
    Option.bind (build (rhs :: lhs :: env) body Done) (fun body_code ->
      build env value (Scope2 (lhs, rhs, body_code, rest)))
  | C_term.Fst value -> build env value (First rest)
  | C_term.Snd value -> build env value (Second rest)
  | C_term.Add (lhs, rhs) ->
    Option.bind (build env rhs (Plus rest)) (fun rhs_code ->
      build env lhs rhs_code)
  | C_term.Sub (lhs, rhs) ->
    Option.bind (build env rhs (Minus rest)) (fun rhs_code ->
      build env lhs rhs_code)
  | C_term.Mul (lhs, rhs) ->
    Option.bind (build env rhs (Times rest)) (fun rhs_code ->
      build env lhs rhs_code)
  | C_term.Div (lhs, rhs) ->
    Option.bind (build env rhs (Quot rest)) (fun rhs_code ->
      build env lhs rhs_code)
  | C_term.Mod (lhs, rhs) ->
    Option.bind (build env rhs (Rem rest)) (fun rhs_code ->
      build env lhs rhs_code)
  | C_term.Neg value -> build env value (Negate rest)
  | C_term.Abs value -> build env value (Absolute rest)
  | C_term.Eq (typ, lhs, rhs) ->
    begin
      match shape_of typ with
      | Some SAtom ->
        Option.bind (build env rhs (Same rest)) (fun rhs_code ->
          build env lhs rhs_code)
      | _ -> None
    end
  | C_term.Cat (lhs, rhs) ->
    Option.bind (build env rhs (Join rest)) (fun rhs_code ->
      build env lhs rhs_code)
  | C_term.Take (len, value) -> build env value (Clip (len, rest))
  | C_term.Drop (len, value) -> build env value (Skip (len, rest))
  | C_term.Vcat (lhs, rhs) ->
    Option.bind (build env rhs (Append rest)) (fun rhs_code ->
      build env lhs rhs_code)
  | C_term.At (index, value) -> build env value (Pick (index, rest))
  | C_term.Uncons value -> build env value (Unhead rest)
  | C_term.Act (atom, body) ->
    Option.map (fun code -> Effect (atom, code)) (build env body rest)
  | C_term.Inl _ | C_term.Inr _ | C_term.Case _
  | C_term.Vfold _ | C_term.Step _ | C_term.Close _ -> None

and build_vec env elem values rest =
  match values with
  | [] -> Some (Empty (elem, rest))
  | first :: tail ->
    Option.bind (build_vec env elem tail (Cons rest)) (fun tail_code ->
      build env first tail_code)

let lower term = build [] term Done

let root sub = function
  | Some at :: rest -> Ok ({ at; sub }, rest)
  | None :: _ | [] -> Error Map

let rec tree term marks =
  match term with
  | C_term.Unit | C_term.Bool _ | C_term.Int _ | C_term.Bytes _
  | C_term.Var _ ->
      root [] marks
  | C_term.Vec (_, values) ->
    let* values, marks = trees values marks in
    root values marks
  | C_term.Let (_, value, body) ->
      let* value, marks = tree value marks in
      let* body, marks = tree body marks in
      root [value; body] marks
  | C_term.If (guard, yes, no) ->
      let* guard, marks = tree guard marks in
      let* yes, marks = tree yes marks in
      let* no, marks = tree no marks in
      root [guard; yes; no] marks
  | C_term.Add (left, right) | C_term.Sub (left, right)
  | C_term.Mul (left, right) | C_term.Div (left, right)
  | C_term.Mod (left, right) | C_term.Eq (_, left, right)
  | C_term.Cat (left, right) | C_term.Pair (left, right)
  | C_term.Vcat (left, right) ->
      let* left, marks = tree left marks in
      let* right, marks = tree right marks in
      root [left; right] marks
  | C_term.Unpair (value, _, _, body) ->
    let* value, marks = tree value marks in
    let* body, marks = tree body marks in
    root [value; body] marks
  | C_term.Fst value | C_term.Snd value | C_term.Neg value
  | C_term.Abs value | C_term.Take (_, value)
  | C_term.Drop (_, value) | C_term.At (_, value) | C_term.Uncons value ->
      let* value, marks = tree value marks in
      root [value] marks
  | C_term.Act (_, body) ->
      let* body, marks = tree body marks in
      root [body] marks
  | C_term.Inl _ | C_term.Inr _ | C_term.Case _
  | C_term.Vfold _ | C_term.Step _ | C_term.Close _ -> Error Map

and trees terms marks =
  match terms with
  | [] -> Ok ([], marks)
  | first :: rest ->
    let* first, marks = tree first marks in
    let* rest, marks = trees rest marks in
    Ok (first :: rest, marks)

let rec spread at = function
  | C_term.Unit | C_term.Bool _ | C_term.Int _ | C_term.Bytes _
  | C_term.Var _ -> { at; sub = [] }
  | C_term.Vec (_, values) -> { at; sub = List.map (spread at) values }
  | C_term.Let (_, value, body) ->
    { at; sub = [spread at value; spread at body] }
  | C_term.If (guard, yes, no) ->
    { at; sub = [spread at guard; spread at yes; spread at no] }
  | C_term.Pair (left, right) | C_term.Add (left, right)
  | C_term.Sub (left, right) | C_term.Mul (left, right)
  | C_term.Div (left, right) | C_term.Mod (left, right)
  | C_term.Eq (_, left, right) | C_term.Cat (left, right)
  | C_term.Vcat (left, right) ->
    { at; sub = [spread at left; spread at right] }
  | C_term.Unpair (value, _, _, body) ->
    { at; sub = [spread at value; spread at body] }
  | C_term.Fst value | C_term.Snd value | C_term.Neg value
  | C_term.Abs value | C_term.Take (_, value)
  | C_term.Drop (_, value) | C_term.At (_, value) | C_term.Uncons value
  | C_term.Inl (value, _) | C_term.Inr (_, value) | C_term.Close value ->
    { at; sub = [spread at value] }
  | C_term.Case (value, _, yes, _, no) ->
    { at; sub = [spread at value; spread at yes; spread at no] }
  | C_term.Act (_, body) -> { at; sub = [spread at body] }
  | C_term.Vfold (vector, seed, fold) ->
    { at; sub = [spread at vector; spread at seed; spread at fold.body] }
  | C_term.Step (cap, value) ->
    { at; sub = [spread at cap; spread at value] }

let rec retree source target mark =
  let node sub = Some { at = mark.at; sub } in
  match source, target, mark.sub with
  | C_term.Var _, _, [] -> Some (spread mark.at target)
  | C_term.Unit, C_term.Unit, []
  | C_term.Bool _, C_term.Bool _, []
  | C_term.Int _, C_term.Int _, []
  | C_term.Bytes _, C_term.Bytes _, [] -> Some mark
  | C_term.Vec (_, left), C_term.Vec (_, right), marks ->
    Option.bind (retrees left right marks) node
  | C_term.Let (_, left_value, left_body),
      C_term.Let (_, right_value, right_body), [value_mark; body_mark] ->
    Option.bind (retree left_value right_value value_mark) (fun value ->
      Option.bind (retree left_body right_body body_mark) (fun body ->
        node [value; body]))
  | C_term.If (left_guard, left_yes, left_no),
      C_term.If (right_guard, right_yes, right_no),
      [guard_mark; yes_mark; no_mark] ->
    Option.bind (retree left_guard right_guard guard_mark) (fun guard ->
      Option.bind (retree left_yes right_yes yes_mark) (fun yes ->
        Option.bind (retree left_no right_no no_mark) (fun no ->
          node [guard; yes; no])))
  | C_term.Pair (left_first, left_second),
      C_term.Pair (right_first, right_second), [first_mark; second_mark]
  | C_term.Add (left_first, left_second),
      C_term.Add (right_first, right_second), [first_mark; second_mark]
  | C_term.Sub (left_first, left_second),
      C_term.Sub (right_first, right_second), [first_mark; second_mark]
  | C_term.Mul (left_first, left_second),
      C_term.Mul (right_first, right_second), [first_mark; second_mark]
  | C_term.Div (left_first, left_second),
      C_term.Div (right_first, right_second), [first_mark; second_mark]
  | C_term.Mod (left_first, left_second),
      C_term.Mod (right_first, right_second), [first_mark; second_mark]
  | C_term.Eq (_, left_first, left_second),
      C_term.Eq (_, right_first, right_second), [first_mark; second_mark]
  | C_term.Cat (left_first, left_second),
      C_term.Cat (right_first, right_second), [first_mark; second_mark]
  | C_term.Vcat (left_first, left_second),
      C_term.Vcat (right_first, right_second), [first_mark; second_mark] ->
    Option.bind (retree left_first right_first first_mark) (fun first ->
      Option.bind (retree left_second right_second second_mark) (fun second ->
        node [first; second]))
  | C_term.Unpair (left_value, _, _, left_body),
      C_term.Unpair (right_value, _, _, right_body), [value_mark; body_mark] ->
    Option.bind (retree left_value right_value value_mark) (fun value ->
      Option.bind (retree left_body right_body body_mark) (fun body ->
        node [value; body]))
  | C_term.Fst left, C_term.Fst right, [child]
  | C_term.Snd left, C_term.Snd right, [child]
  | C_term.Neg left, C_term.Neg right, [child]
  | C_term.Abs left, C_term.Abs right, [child]
  | C_term.Take (_, left), C_term.Take (_, right), [child]
  | C_term.Drop (_, left), C_term.Drop (_, right), [child]
  | C_term.At (_, left), C_term.At (_, right), [child]
  | C_term.Uncons left, C_term.Uncons right, [child] ->
    Option.bind (retree left right child) (fun value -> node [value])
  | C_term.Act (left_atom, left), C_term.Act (right_atom, right), [child]
      when left_atom = right_atom ->
    Option.bind (retree left right child) (fun body -> node [body])
  | _ -> None

and retrees sources targets marks =
  match sources, targets, marks with
  | [], [], [] -> Some []
  | source :: sources, target :: targets, mark :: marks ->
    Option.bind (retree source target mark) (fun first ->
      Option.map (fun rest -> first :: rest) (retrees sources targets marks))
  | _ -> None

let rec into_loc term mark rest =
  match term, mark.sub with
  | C_term.Unit, [] -> Some (LVoid (mark.at, rest))
  | (C_term.Bool _ | C_term.Int _ | C_term.Bytes _), [] ->
      Some (LPush (mark.at, rest))
  | C_term.Vec (_, values), marks -> loc_vec values marks mark.at rest
  | C_term.Var _, [] -> Some (LGet (mark.at, rest))
  | C_term.Let (item, value, body), [value_mark; body_mark] ->
      begin
        match into_loc body body_mark LDone with
        | None -> None
        | Some body_loc ->
          begin
            match item.mul with
            | C_type.Zero -> into_loc body body_mark rest
            | C_type.One | C_type.Many ->
              into_loc value value_mark (LScope (mark.at, body_loc, rest))
          end
      end
  | C_term.If (guard, yes, no), [guard_mark; yes_mark; no_mark] ->
      begin
        match into_loc yes yes_mark LDone, into_loc no no_mark LDone with
        | Some yes_loc, Some no_loc ->
          into_loc guard guard_mark
            (LFork (mark.at, yes_mark.at, no_mark.at,
              yes_loc, no_loc, rest))
        | _ -> None
      end
  | C_term.Pair (left, right), [left_mark; right_mark] ->
    begin
      match into_loc right right_mark (LDuo (mark.at, rest)) with
      | Some right_loc -> into_loc left left_mark right_loc
      | None -> None
    end
  | C_term.Unpair (value, _, _, body), [value_mark; body_mark] ->
    begin
      match into_loc body body_mark LDone with
      | Some body_loc ->
        into_loc value value_mark (LScope2 (mark.at, body_loc, rest))
      | None -> None
    end
  | C_term.Fst value, [value_mark] ->
    into_loc value value_mark (LFirst (mark.at, rest))
  | C_term.Snd value, [value_mark] ->
    into_loc value value_mark (LSecond (mark.at, rest))
  | C_term.Add (left, right), [left_mark; right_mark] ->
      begin
        match into_loc right right_mark (LPlus (mark.at, rest)) with
        | Some right_loc -> into_loc left left_mark right_loc
        | None -> None
      end
  | C_term.Sub (left, right), [left_mark; right_mark] ->
      begin
        match into_loc right right_mark (LMinus (mark.at, rest)) with
        | Some right_loc -> into_loc left left_mark right_loc
        | None -> None
      end
  | C_term.Mul (left, right), [left_mark; right_mark] ->
      begin
        match into_loc right right_mark (LTimes (mark.at, rest)) with
        | Some right_loc -> into_loc left left_mark right_loc
        | None -> None
      end
  | C_term.Div (left, right), [left_mark; right_mark] ->
      begin
        match into_loc right right_mark (LQuot (mark.at, rest)) with
        | Some right_loc -> into_loc left left_mark right_loc
        | None -> None
      end
  | C_term.Mod (left, right), [left_mark; right_mark] ->
      begin
        match into_loc right right_mark (LRem (mark.at, rest)) with
        | Some right_loc -> into_loc left left_mark right_loc
        | None -> None
      end
  | C_term.Neg value, [value_mark] ->
      into_loc value value_mark (LNegate (mark.at, rest))
  | C_term.Abs value, [value_mark] ->
      into_loc value value_mark (LAbsolute (mark.at, rest))
  | C_term.Eq (_, left, right), [left_mark; right_mark] ->
    begin
      match into_loc right right_mark (LSame (mark.at, rest)) with
      | Some right_loc -> into_loc left left_mark right_loc
      | None -> None
    end
  | C_term.Cat (left, right), [left_mark; right_mark] ->
    begin
      match into_loc right right_mark (LJoin (mark.at, rest)) with
      | Some right_loc -> into_loc left left_mark right_loc
      | None -> None
    end
  | C_term.Take (len, value), [value_mark] ->
      into_loc value value_mark (LClip (len, mark.at, rest))
  | C_term.Drop (len, value), [value_mark] ->
      into_loc value value_mark (LSkip (len, mark.at, rest))
  | C_term.Vcat (left, right), [left_mark; right_mark] ->
    begin
      match into_loc right right_mark (LAppend (mark.at, rest)) with
      | Some right_loc -> into_loc left left_mark right_loc
      | None -> None
    end
  | C_term.At (index, value), [value_mark] ->
    into_loc value value_mark (LPick (index, mark.at, rest))
  | C_term.Uncons value, [value_mark] ->
    into_loc value value_mark (LUnhead (mark.at, rest))
  | C_term.Act (_, body), [body_mark] ->
    Option.map
      (fun body_loc -> LEffect (mark.at, body_loc))
      (into_loc body body_mark rest)
  | _ -> None

and loc_vec values marks at rest =
  match values, marks with
  | [], [] -> Some (LEmpty (at, rest))
  | first :: tail, first_mark :: tail_marks ->
    Option.bind (loc_vec tail tail_marks at (LCons (at, rest)))
      (fun tail_loc -> into_loc first first_mark tail_loc)
  | _ -> None

let rec same_loc code loc =
  match code, loc with
  | Done, LDone -> true
  | Push (_, rest), LPush (_, lrest)
  | Void rest, LVoid (_, lrest)
  | Plus rest, LPlus (_, lrest)
  | Minus rest, LMinus (_, lrest)
  | Times rest, LTimes (_, lrest)
  | Quot rest, LQuot (_, lrest)
  | Rem rest, LRem (_, lrest)
  | Negate rest, LNegate (_, lrest)
  | Absolute rest, LAbsolute (_, lrest)
  | Same rest, LSame (_, lrest)
  | Join rest, LJoin (_, lrest)
  | Duo rest, LDuo (_, lrest)
  | First rest, LFirst (_, lrest)
  | Second rest, LSecond (_, lrest)
  | Cons rest, LCons (_, lrest)
  | Append rest, LAppend (_, lrest)
  | Unhead rest, LUnhead (_, lrest)
  | Effect (_, rest), LEffect (_, lrest) -> same_loc rest lrest
  | Get (_, _, rest), LGet (_, lrest)
  | Empty (_, rest), LEmpty (_, lrest) -> same_loc rest lrest
  | Clip (len, rest), LClip (found, _, lrest)
      when C_nat.equal len found ->
    same_loc rest lrest
  | Skip (len, rest), LSkip (found, _, lrest)
      when C_nat.equal len found ->
    same_loc rest lrest
  | Pick (index, rest), LPick (found, _, lrest)
      when C_nat.equal index found ->
    same_loc rest lrest
  | Scope (_, body, rest), LScope (_, lbody, lrest) ->
      same_loc body lbody && same_loc rest lrest
  | Scope2 (_, _, body, rest), LScope2 (_, lbody, lrest) ->
    same_loc body lbody && same_loc rest lrest
  | Fork (_, yes, no, rest), LFork (_, _, _, lyes, lno, lrest) ->
      same_loc yes lyes && same_loc no lno && same_loc rest lrest
  | _ -> false

type mvalue =
  | VUnit
  | VAtom of C_emit.lit
  | VPair of mvalue * mvalue
  | VVec of shape * mvalue list

let rec value_shape = function
  | VUnit -> SUnit
  | VAtom _ -> SAtom
  | VPair (lhs, rhs) -> SPair (value_shape lhs, value_shape rhs)
  | VVec (elem, values) ->
    begin
      match C_nat.of_int (List.length values) with
      | Some len -> SVec (len, elem)
      | None -> SVec (C_nat.zero, elem)
    end

type slot = {
  bind : C_term.bind;
  value : mvalue;
  live : bool;
}

let rec take id left = function
  | [] -> None
  | slot :: right when C_nat.equal id slot.bind.id ->
    begin
      match slot.bind.mul, slot.live with
      | C_type.One, true ->
        let next = { slot with live = false } in
        Some (slot.value, List.rev_append left (next :: right))
      | C_type.Many, _ ->
        Some (slot.value, List.rev_append left (slot :: right))
      | C_type.Zero, _ | C_type.One, false -> None
    end
  | slot :: right -> take id (slot :: left) right

let open_slot bind value env =
  match shape_of bind.C_term.typ with
  | Some form when same_shape form (value_shape value) ->
    begin
      match bind.mul with
      | C_type.One | C_type.Many -> Some ({ bind; value; live = true } :: env)
      | C_type.Zero -> None
    end
  | _ -> None

let close_slot bind = function
  | slot :: rest when C_nat.equal bind.C_term.id slot.bind.id ->
    begin
      match bind.mul, slot.bind.mul, slot.live with
      | C_type.One, C_type.One, false -> Some rest
      | C_type.Many, C_type.Many, _ -> Some rest
      | _ -> None
    end
  | [] | _ :: _ -> None

let rec size = function
  | Done -> 1
  | Push (_, rest) | Void rest | Get (_, _, rest) | Plus rest | Minus rest
  | Times rest | Quot rest | Rem rest | Negate rest | Absolute rest | Same rest
  | Join rest | Clip (_, rest) | Skip (_, rest) | Duo rest | First rest
  | Second rest | Empty (_, rest) | Cons rest | Append rest
  | Pick (_, rest) | Unhead rest | Effect (_, rest) -> 1 + size rest
  | Scope (_, body, rest) -> 1 + size body + size rest
  | Scope2 (_, _, body, rest) -> 1 + size body + size rest
  | Fork (_, yes, no, rest) -> 1 + size yes + size no + size rest

let rec collect_effects row = function
  | Done -> row
  | Push (_, rest)
  | Void rest
  | Get (_, _, rest)
  | Plus rest
  | Minus rest
  | Times rest
  | Quot rest
  | Rem rest
  | Negate rest
  | Absolute rest
  | Same rest
  | Join rest
  | Clip (_, rest)
  | Skip (_, rest)
  | Duo rest
  | First rest
  | Second rest
  | Empty (_, rest)
  | Cons rest
  | Append rest
  | Pick (_, rest)
  | Unhead rest -> collect_effects row rest
  | Effect (action, rest) -> collect_effects (C_eff.add action row) rest
  | Scope (_, body, rest) ->
    collect_effects (collect_effects row body) rest
  | Scope2 (_, _, body, rest) ->
    collect_effects (collect_effects row body) rest
  | Fork (_, yes, no, rest) ->
    collect_effects
      (collect_effects (collect_effects row yes) no)
      rest

let effects code = C_eff.to_list (collect_effects C_eff.empty code)

let rec exec fuel code env stack plan =
  if fuel = 0 then None
  else
    let left = fuel - 1 in
    match code with
    | Done -> Some (stack, env, plan)
    | Push (value, rest) -> exec left rest env (VAtom value :: stack) plan
    | Void rest -> exec left rest env (VUnit :: stack) plan
    | Get (id, form, rest) ->
      Option.bind (take id [] env) (fun (value, next) ->
        if same_shape form (value_shape value) then
          exec left rest next (value :: stack) plan
        else None)
    | Plus rest ->
      begin
        match stack with
        | VAtom (C_emit.Int rhs) :: VAtom (C_emit.Int lhs) :: tail ->
          exec left rest env (VAtom (C_emit.Int (Z.add lhs rhs)) :: tail) plan
        | _ -> None
      end
    | Minus rest ->
      begin
        match stack with
        | VAtom (C_emit.Int rhs) :: VAtom (C_emit.Int lhs) :: tail ->
          exec left rest env (VAtom (C_emit.Int (Z.sub lhs rhs)) :: tail) plan
        | _ -> None
      end
    | Times rest ->
      begin
        match stack with
        | VAtom (C_emit.Int rhs) :: VAtom (C_emit.Int lhs) :: tail ->
          exec left rest env (VAtom (C_emit.Int (Z.mul lhs rhs)) :: tail) plan
        | _ -> None
      end
    | Quot rest ->
      begin
        match stack with
        | VAtom (C_emit.Int rhs) :: VAtom (C_emit.Int lhs) :: tail
            when not (Z.equal rhs Z.zero) ->
          exec left rest env (VAtom (C_emit.Int (Z.div lhs rhs)) :: tail) plan
        | _ -> None
      end
    | Rem rest ->
      begin
        match stack with
        | VAtom (C_emit.Int rhs) :: VAtom (C_emit.Int lhs) :: tail
            when not (Z.equal rhs Z.zero) ->
          exec left rest env (VAtom (C_emit.Int (Z.rem lhs rhs)) :: tail) plan
        | _ -> None
      end
    | Negate rest ->
      begin
        match stack with
        | VAtom (C_emit.Int value) :: tail ->
          exec left rest env (VAtom (C_emit.Int (Z.neg value)) :: tail) plan
        | _ -> None
      end
    | Absolute rest ->
      begin
        match stack with
        | VAtom (C_emit.Int value) :: tail ->
          exec left rest env (VAtom (C_emit.Int (Z.abs value)) :: tail) plan
        | _ -> None
      end
    | Same rest ->
      begin
        match stack with
        | VAtom rhs :: VAtom lhs :: tail ->
          exec left rest env (VAtom (C_emit.Bool (equal lhs rhs)) :: tail) plan
        | _ -> None
      end
    | Join rest ->
      begin
        match stack with
        | VAtom (C_emit.Bytes rhs) :: VAtom (C_emit.Bytes lhs) :: tail ->
          exec left rest env (VAtom (C_emit.Bytes (lhs ^ rhs)) :: tail) plan
        | _ -> None
      end
    | Clip (len, rest) ->
      begin
        match stack with
        | VAtom (C_emit.Bytes value) :: tail ->
          let count = C_nat.to_int len in
          if count <= String.length value then
            exec left rest env
              (VAtom (C_emit.Bytes (String.sub value 0 count)) :: tail) plan
          else None
        | _ -> None
      end
    | Skip (len, rest) ->
      begin
        match stack with
        | VAtom (C_emit.Bytes value) :: tail ->
          let first = C_nat.to_int len in
          let count = String.length value - first in
          if count >= 0 then
            exec left rest env
              (VAtom (C_emit.Bytes (String.sub value first count)) :: tail) plan
          else None
        | _ -> None
      end
    | Duo rest ->
      begin
        match stack with
        | rhs :: lhs :: tail ->
          exec left rest env (VPair (lhs, rhs) :: tail) plan
        | _ -> None
      end
    | First rest ->
      begin
        match stack with
        | VPair (lhs, _) :: tail -> exec left rest env (lhs :: tail) plan
        | _ -> None
      end
    | Second rest ->
      begin
        match stack with
        | VPair (_, rhs) :: tail -> exec left rest env (rhs :: tail) plan
        | _ -> None
      end
    | Empty (elem, rest) ->
      exec left rest env (VVec (elem, []) :: stack) plan
    | Cons rest ->
      begin
        match stack with
        | VVec (elem, values) :: item :: tail
            when same_shape elem (value_shape item) ->
          exec left rest env (VVec (elem, item :: values) :: tail) plan
        | _ -> None
      end
    | Append rest ->
      begin
        match stack with
        | VVec (re, rhs) :: VVec (le, lhs) :: tail when same_shape le re ->
          exec left rest env (VVec (le, lhs @ rhs) :: tail) plan
        | _ -> None
      end
    | Pick (index, rest) ->
      begin
        match stack with
        | VVec (_, values) :: tail ->
          Option.bind (List.nth_opt values (C_nat.to_int index)) (fun item ->
            exec left rest env (item :: tail) plan)
        | _ -> None
      end
    | Unhead rest ->
      begin
        match stack with
        | VVec (elem, first :: values) :: tail ->
          exec left rest env
            (VPair (first, VVec (elem, values)) :: tail) plan
        | _ -> None
      end
    | Scope (bind, body, rest) ->
      begin
        match stack with
        | value :: tail ->
          Option.bind
            (open_slot bind value env)
            (fun opened ->
              Option.bind
                (exec left body opened tail plan)
                (fun (stack, prior, next_plan) ->
                  Option.bind (close_slot bind prior) (fun next ->
                    exec left rest next stack next_plan)))
        | _ -> None
      end
    | Scope2 (lhs_bind, rhs_bind, body, rest) ->
      begin
        match stack with
        | VPair (lhs, rhs) :: tail ->
          Option.bind (open_slot lhs_bind lhs env) (fun first ->
            Option.bind (open_slot rhs_bind rhs first) (fun second ->
              Option.bind (exec left body second tail plan)
                (fun (stack, prior, next_plan) ->
                Option.bind (close_slot rhs_bind prior) (fun last ->
                  Option.bind (close_slot lhs_bind last) (fun next ->
                    exec left rest next stack next_plan)))))
        | _ -> None
      end
    | Fork (form, yes, no, rest) ->
      begin
        match stack with
        | VAtom (C_emit.Bool value) :: tail ->
          let branch = if value then yes else no in
          Option.bind (exec left branch env tail plan)
            (fun (after, next, next_plan) ->
            match after with
            | item :: _ when same_shape form (value_shape item) ->
              exec left rest next after next_plan
            | _ -> None)
        | _ -> None
      end
    | Effect (atom, rest) -> exec left rest env stack (atom :: plan)

let replay_plan code =
  match exec (1 + size code) code [] [] [] with
  | Some ([VAtom value], [], plan) -> Some ([value], List.rev plan)
  | Some _ | None -> None

let replay code = Option.map fst (replay_plan code)

let source source =
  let* parsed =
    match C_parse.parse source with
    | Ok value -> Ok value
    | Error error -> Error (Source error)
  in
  let* lowered, info =
    match C_parse.compile parsed with
    | Ok value -> Ok value
    | Error error -> Error (Source error)
  in
  Ok (parsed, lowered, info)

let source_tree parsed term =
  match tree term (C_parse.body_marks parsed) with
  | Ok (value, []) -> Ok value
  | Ok (_, _ :: _) | Error _ -> Error Map

let closed result span = {
  code = Push (result, Done);
  loc = LPush (span, LDone);
  result;
  span;
}

let finish ?marks parsed term (info : C_check.info) (out : C_eval.out) =
  let* result =
    match literal info.C_check.typ out.value with
    | Some value -> Ok value
    | None -> Error (Value (info.typ, out.value))
  in
  match lower term with
  | None ->
    if out.C_eval.plan = [] then Ok (closed result (C_parse.body_span parsed))
    else Error (Plan out.plan)
  | Some code ->
    begin
      match one_shape code with
      | Some SAtom ->
        let* mark =
          match marks with
          | Some value -> value ()
          | None -> source_tree parsed term
        in
        let* loc =
          match into_loc term mark LDone with
          | Some value when same_loc code value -> Ok value
          | Some _ | None -> Error Map
        in
        begin
          match replay_plan code with
          | Some ([actual], plan)
              when equal actual result && plan_equal plan out.plan ->
            Ok { code; loc; result; span = C_parse.body_span parsed }
          | _ -> Error Replay
        end
      | Some _ ->
        if out.plan = [] then Ok (closed result (C_parse.body_span parsed))
        else Error (Plan out.plan)
      | None -> Error Term
    end

let compile source_text =
  let* parsed, lowered, info = source source_text in
  let count = List.length lowered.C_low.inputs in
  if count <> 0 then Error (Inputs count)
  else
    let* out =
      match C_eval.run lowered.term with
      | Ok value -> Ok value
      | Error error -> Error (Run error)
    in
    finish parsed lowered.term info out

let compile_feed source_text feed =
  let* parsed, lowered, info = source source_text in
  let* pairs =
    match C_feed.attach lowered.C_low.inputs feed with
    | Ok value -> Ok value
    | Error error -> Error (Feed error)
  in
  let* term =
    match C_feed.close lowered.inputs feed lowered.term with
    | Ok value -> Ok value
    | Error error -> Error (Feed error)
  in
  let marks () =
    let* source_mark = source_tree parsed lowered.term in
    match retree lowered.term term source_mark with
    | Some value -> Ok value
    | None -> Error Map
  in
  let* out =
    match C_eval.run_in pairs lowered.term with
    | Ok value -> Ok value
    | Error error -> Error (Run error)
  in
  finish ~marks parsed term info out

let text = function
  | Source error -> C_parse.text error
  | Feed error -> C_feed.text error
  | Inputs count -> Printf.sprintf "machine input count = %d expected = 0" count
  | Effects effects ->
      "machine effects are not representable effects = "
      ^ C_eff.text (C_eff.of_list effects)
  | Term -> "machine term is outside the runtime scalar profile"
  | Run error -> C_eval.text error
  | Plan effects ->
      "machine execution plan is not empty effects = "
      ^ C_eff.text (C_eff.of_list effects)
  | Value (typ, value) ->
      "machine value is not representable type = " ^ C_type.text typ
      ^ " value = " ^ C_eval.value_text value
  | Replay -> "machine replay differs from checked evaluation"
  | Map -> "machine source position map differs from lowered term"