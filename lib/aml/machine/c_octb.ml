(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type op =
  | Load of int * C_emit.lit
  | Move of int * int
  | Plus of int * int * int
  | Times of int * int * int
  | Quotient of int * int * int
  | Remainder of int * int * int
  | Negate of int * int
  | Absolute of int * int
  | Same of int * int * int
  | Less of int * int * int
  | Greater of int * int * int
  | Join of int * int * int
  | Minus of int * int * int
  | Size of int * int
  | Slice of int * int * int * int
  | Jump of int
  | Jump_if of int * int
  | Mark of int
  | Noop
  | Stop

type effect_layout = {
  index : int;
  atom : C_eff.atom;
  payload : int list;
  scratch : int list;
}

type t = {
  inputs : C_term.bind list;
  plan : C_mach.code;
  code : op array;
  octb : string;
  typ : C_type.t;
  result : C_emit.lit option;
  emission : C_mach.emission;
  veils : int;
  veil_depth : C_nat.t;
  map : C_smap.t;
  live : C_live.t;
}

type decode_error =
  | Input_size of int
  | Header
  | Magic
  | Version of int
  | Constant_count of int
  | Instruction_count of int64
  | Constant_header of int
  | Constant_size of int * int
  | Constant_data of int
  | Constant_tag of int * int
  | Constant_value of int
  | Instruction_data of int
  | Constant_ref of int * int
  | Opcode of int * int
  | Register_ref of int * int
  | Jump_value of int * int64
  | Jump_ref of int * int
  | Jump_mark of int
  | Trailing_data of int
  | Empty_code
  | Result_header
  | Emission_invalid
  | Emission_repeated
  | Veil_invalid
  | Veil_repeated
  | Exact_image

type error =
  | Mach of C_mach.error
  | Stack
  | Register
  | Label
  | Constants of int
  | Map
  | Smap of C_smap.error
  | Slot
  | Lmap of C_live.error
  | Effect_map
  | Output of decode_error
  | Output_code

type constant =
  | CInt of string
  | CBool of bool
  | CText of string
  | CData of C_rval.t
  | CBytes of string

type const_row = {
  id : int;
  at : int;
  size : int;
  value : constant;
}

type code_cell = {
  pc : int;
  at : int;
  size : int;
}

type image = {
  inputs : C_type.t array;
  output : C_type.t option;
  emission : C_mach.emission option;
  veil : (int * C_nat.t) option;
  consts : const_row array;
  cells : code_cell array;
  text_at : int;
  code : op array;
}

let wire_emission = function
  | C_mach.Lowered -> Bytecode.Lowered
  | C_mach.Specialized -> Bytecode.Specialized

let local_emission = function
  | Bytecode.Lowered -> C_mach.Lowered
  | Bytecode.Specialized -> C_mach.Specialized

let image_emission image =
  Option.fold ~none:"opaque" ~some:C_mach.emission_text image.emission

let veil_text count = if count = 0 then "none" else "static"

let image_veil image =
  Option.fold ~none:"unknown" ~some:(fun (count, _) -> veil_text count)
    image.veil

let image_veils image =
  Option.fold ~none:"unknown" ~some:(fun (count, _) -> string_of_int count)
    image.veil

let image_veil_depth image =
  Option.fold ~none:"unknown" ~some:(fun (_, depth) -> C_nat.text depth)
    image.veil

let wire_veil count depth =
  { Bytecode.count = Z.of_int count; depth = C_nat.to_z depth }

let local_veil value =
  match C_nat.make value.Bytecode.count, C_nat.make value.depth with
  | Some count, Some depth
      when not (C_nat.equal count C_nat.zero)
        || C_nat.equal depth C_nat.zero ->
    Some (C_nat.to_int count, depth)
  | _ -> None

type asm =
  | Op of op
  | Goto of int
  | Branch of int * int
  | Place of int
  | Apply of effect_layout

type marked = {
  asm : asm;
  at : C_lex.span;
  live : C_live.slot list;
}

type seq = marked list -> marked list

type gen = {
  next : int;
  free : int list;
  label : int;
}

type layout =
  | Unit
  | Atom of int
  | Pair of layout * layout
  | Vec of C_mach.shape * layout list
  | Sum of int * layout

type cell = {
  bind : C_term.bind;
  layout : layout;
  live : bool;
}

type low = {
  gen : gen;
  stack : layout list;
  env : cell list;
  seq : seq;
}

let ( let* ) value next =
  match value with
  | Ok value -> next value
  | Error error -> Error error

let empty tail = tail
let view env =
  List.map
    (fun item -> C_live.slot item.bind.C_term.id item.bind.mul item.live)
    env

let one env at asm tail = { asm; at; live = view env } :: tail
let cat left right tail = left (right tail)

let order env at rel left right =
  let op value = one env at (Op value) in
  match rel with
  | C_term.Lt -> op (Less (left, left, right))
  | C_term.Gt -> op (Greater (left, left, right))
  | C_term.Le ->
    cat (op (Greater (left, left, right)))
      (cat (op (Load (right, C_emit.Bool false)))
        (op (Same (left, left, right))))
  | C_term.Ge ->
    cat (op (Less (left, left, right)))
      (cat (op (Load (right, C_emit.Bool false)))
        (op (Same (left, left, right))))

let input_limit = Contract_vm.input_limit

let fresh_reg state =
  match state.free with
  | reg :: free -> Ok (reg, { state with free })
  | [] when state.next >= 64 -> Error Register
  | [] -> Ok (state.next, { state with next = state.next + 1 })

let scratch_count = function
  | C_eff.Read _ | C_eff.Fail _ -> 2
  | C_eff.Write _ | C_eff.Emit _ | C_eff.Close _ -> 0

let scratch atom state =
  let rec walk count state out =
    if count = 0 then Ok (List.rev out)
    else
      let* reg, state = fresh_reg state in
      walk (count - 1) state (reg :: out)
  in
  walk (scratch_count atom) state []

let release reg state =
  if reg = 0 then state else { state with free = reg :: state.free }

let rec release_layout value state =
  match value with
  | Unit -> state
  | Atom reg -> release reg state
  | Pair (lhs, rhs) ->
    release_layout lhs (release_layout rhs state)
  | Vec (_, values) -> List.fold_right release_layout values state
  | Sum (tag, payload) -> release tag (release_layout payload state)

let rec layout_regs value out =
  match value with
  | Unit -> out
  | Atom reg -> reg :: out
  | Pair (lhs, rhs) -> layout_regs lhs (layout_regs rhs out)
  | Vec (_, values) -> List.fold_right layout_regs values out
  | Sum (tag, payload) -> tag :: layout_regs payload out

let rec same_layout left right =
  match left, right with
  | Unit, Unit -> true
  | Atom lhs, Atom rhs -> lhs = rhs
  | Pair (ll, lr), Pair (rl, rr) ->
    same_layout ll rl && same_layout lr rr
  | Vec (le, lhs), Vec (re, rhs) ->
    C_mach.same_shape le re && same_layouts lhs rhs
  | Sum (lt, lhs), Sum (rt, rhs) -> lt = rt && same_layout lhs rhs
  | _ -> false

and same_layouts left right =
  match left, right with
  | [], [] -> true
  | lhs :: lrest, rhs :: rrest ->
    same_layout lhs rhs && same_layouts lrest rrest
  | _ -> false

let rec fits form value =
  match form, value with
  | C_mach.SUnit, Unit | C_mach.SAtom, Atom _ -> true
  | C_mach.SPair (lf, rf), Pair (lhs, rhs) ->
    fits lf lhs && fits rf rhs
  | C_mach.SVec (len, elem), Vec (found, values) ->
    C_mach.same_shape elem found
    && C_nat.to_int len = List.length values
    && List.for_all (fits elem) values
  | C_mach.SSum form, Sum (_, payload) -> fits form payload
  | _ -> false

let rec alloc form state =
  match form with
  | C_mach.SUnit -> Ok (Unit, state)
  | C_mach.SAtom ->
    let* reg, state = fresh_reg state in
    Ok (Atom reg, state)
  | C_mach.SPair (lhs, rhs) ->
    let* left, state = alloc lhs state in
    let* right, state = alloc rhs state in
    Ok (Pair (left, right), state)
  | C_mach.SVec (len, elem) ->
    let* values, state = alloc_vec (C_nat.to_int len) elem state in
    Ok (Vec (elem, values), state)
  | C_mach.SSum form ->
    let* tag, state = fresh_reg state in
    let* payload, state = alloc form state in
    Ok (Sum (tag, payload), state)

and alloc_vec count elem state =
  if count = 0 then Ok ([], state)
  else
    let* first, state = alloc elem state in
    let* rest, state = alloc_vec (count - 1) elem state in
    Ok (first :: rest, state)

let rec clone env at value state =
  match value with
  | Unit -> Ok (Unit, state, empty)
  | Atom src ->
    let* dst, state = fresh_reg state in
    Ok (Atom dst, state, one env at (Op (Move (dst, src))))
  | Pair (lhs, rhs) ->
    let* left, state, left_seq = clone env at lhs state in
    let* right, state, right_seq = clone env at rhs state in
    Ok (Pair (left, right), state, cat left_seq right_seq)
  | Vec (elem, values) ->
    let* next, state, seq = clone_vec env at values state in
    Ok (Vec (elem, next), state, seq)
  | Sum (tag, payload) ->
    let* next_tag, state = fresh_reg state in
    let* next_payload, state, payload_seq = clone env at payload state in
    let tag_seq = one env at (Op (Move (next_tag, tag))) in
    Ok (Sum (next_tag, next_payload), state, cat tag_seq payload_seq)

and clone_vec env at values state =
  match values with
  | [] -> Ok ([], state, empty)
  | first :: rest ->
    let* head, state, head_seq = clone env at first state in
    let* tail, state, tail_seq = clone_vec env at rest state in
    Ok (head :: tail, state, cat head_seq tail_seq)

let rec copy env at src dst =
  match src, dst with
  | Unit, Unit -> Some empty
  | Atom source, Atom target -> Some (one env at (Op (Move (target, source))))
  | Pair (sl, sr), Pair (dl, dr) ->
    Option.bind (copy env at sl dl) (fun left ->
      Option.map (fun right -> cat left right) (copy env at sr dr))
  | Vec (se, source), Vec (de, target) when C_mach.same_shape se de ->
    copy_vec env at source target
  | Sum (source_tag, source), Sum (target_tag, target) ->
    Option.map
      (fun payload ->
        cat (one env at (Op (Move (target_tag, source_tag)))) payload)
      (copy env at source target)
  | _ -> None

and copy_vec env at source target =
  match source, target with
  | [], [] -> Some empty
  | src :: srest, dst :: drest ->
    Option.bind (copy env at src dst) (fun head ->
      Option.map (fun tail -> cat head tail) (copy_vec env at srest drest))
  | _ -> None

let release_all values state =
  List.fold_right release_layout values state

let rec pick_layout index values state =
  match values with
  | [] -> None
  | value :: rest when index = 0 -> Some (value, release_all rest state)
  | value :: rest ->
    pick_layout (index - 1) rest (release_layout value state)

let avail next live =
  let rec walk reg out =
    if reg >= next then out
    else if List.mem reg live then walk (reg + 1) out
    else walk (reg + 1) (reg :: out)
  in
  walk 1 []

let fresh_label state =
  let value = state.label in
  value, { state with label = value + 1 }

let rec has id = function
  | [] -> false
  | item :: rest -> C_nat.equal id item.bind.C_term.id || has id rest

let rec take id left = function
  | [] -> None
  | item :: right when C_nat.equal id item.bind.C_term.id ->
    begin
      match item.bind.mul, item.live with
      | C_type.One, true ->
        let next = { item with live = false } in
        Some (item.layout, List.rev_append left (next :: right))
      | C_type.Many, _ ->
        Some (item.layout, List.rev_append left (item :: right))
      | C_type.Zero, _ | C_type.One, false -> None
    end
  | item :: right -> take id (item :: left) right

let open_cell bind layout env =
  if has bind.C_term.id env then None
  else
    match C_mach.shape_of bind.typ with
    | Some form when fits form layout ->
      begin
        match bind.mul with
        | C_type.One | C_type.Many ->
          Some ({ bind; layout; live = true } :: env)
        | C_type.Zero -> None
      end
    | _ -> None

let close_cell bind = function
  | item :: rest when C_nat.equal bind.C_term.id item.bind.id ->
    begin
      match bind.mul, item.bind.mul, item.live with
      | C_type.One, C_type.One, false -> Some rest
      | C_type.Many, C_type.Many, _ -> Some rest
      | _ -> None
    end
  | [] | _ :: _ -> None

let same_cell left right =
  C_nat.equal left.bind.C_term.id right.bind.id
  && left.bind.mul = right.bind.mul
  && C_type.equal left.bind.typ right.bind.typ
  && same_layout left.layout right.layout
  && Bool.equal left.live right.live

let rec same_env left right =
  match left, right with
  | [], [] -> true
  | lhead :: ltail, rhead :: rtail ->
    same_cell lhead rhead && same_env ltail rtail
  | _ -> false

let regs env =
  List.fold_right (fun item out -> layout_regs item.layout out) env []

let exact tail = function
  | value :: rest when rest = tail -> Some value
  | _ -> None

let rec lower env state stack code loc =
  match code, loc with
  | C_mach.Done, C_mach.LDone ->
    Ok { gen = state; stack; env; seq = empty }
  | C_mach.Push (value, rest), C_mach.LPush (at, lrest) ->
    let* dst, state = fresh_reg state in
    let* next = lower env state (Atom dst :: stack) rest lrest in
    Ok { next with
      seq = cat (one env at (Op (Load (dst, value)))) next.seq }
  | C_mach.Void rest, C_mach.LVoid (_, lrest) ->
    lower env state (Unit :: stack) rest lrest
  | C_mach.Effect (index, atom, body, rest), C_mach.LEffect (at, lbody, lrest) ->
    let* body = lower env state stack body lbody in
    begin
      match body.stack with
      | payload :: _ ->
        let* scratch = scratch atom body.gen in
        let layout = {
          index;
          atom;
          payload = layout_regs payload [];
          scratch;
        }
        in
        let* next = lower body.env body.gen body.stack rest lrest in
        Ok { next with
          seq = cat body.seq (cat (one body.env at (Apply layout)) next.seq) }
      | [] -> Error Stack
    end
  | C_mach.Get (id, form, rest), C_mach.LGet (at, lrest) ->
    begin
      match take id [] env with
      | None -> Error Slot
      | Some (src, used) when fits form src ->
        let* dst, state, moves = clone used at src state in
        let* next = lower used state (dst :: stack) rest lrest in
        Ok { next with
          seq = cat moves next.seq }
      | Some _ -> Error Stack
    end
  | C_mach.Plus rest, C_mach.LPlus (at, lrest) ->
    begin
      match stack with
      | Atom right :: Atom left :: tail ->
        let state = release right state in
        let* next = lower env state (Atom left :: tail) rest lrest in
        Ok { next with
          seq = cat (one env at (Op (Plus (left, left, right)))) next.seq }
      | _ -> Error Stack
    end
  | C_mach.Minus rest, C_mach.LMinus (at, lrest) ->
    begin
      match stack with
      | Atom right :: Atom left :: tail ->
        let state = release right state in
        let* next = lower env state (Atom left :: tail) rest lrest in
        Ok { next with
          seq = cat (one env at (Op (Minus (left, left, right)))) next.seq }
      | _ -> Error Stack
    end
  | C_mach.Times rest, C_mach.LTimes (at, lrest) ->
    begin
      match stack with
      | Atom right :: Atom left :: tail ->
        let state = release right state in
        let* next = lower env state (Atom left :: tail) rest lrest in
        Ok { next with
          seq = cat (one env at (Op (Times (left, left, right)))) next.seq }
      | _ -> Error Stack
    end
  | C_mach.Quot rest, C_mach.LQuot (at, lrest) ->
    begin
      match stack with
      | Atom right :: Atom left :: tail ->
        let state = release right state in
        let* next = lower env state (Atom left :: tail) rest lrest in
        Ok { next with
          seq = cat (one env at (Op (Quotient (left, left, right)))) next.seq }
      | _ -> Error Stack
    end
  | C_mach.Rem rest, C_mach.LRem (at, lrest) ->
    begin
      match stack with
      | Atom right :: Atom left :: tail ->
        let state = release right state in
        let* next = lower env state (Atom left :: tail) rest lrest in
        Ok { next with
          seq = cat (one env at (Op (Remainder (left, left, right)))) next.seq }
      | _ -> Error Stack
    end
  | C_mach.Negate rest, C_mach.LNegate (at, lrest) ->
    begin
      match stack with
      | Atom value :: tail ->
        let* next = lower env state (Atom value :: tail) rest lrest in
        Ok { next with
          seq = cat (one env at (Op (Negate (value, value)))) next.seq }
      | _ -> Error Stack
    end
  | C_mach.Absolute rest, C_mach.LAbsolute (at, lrest) ->
    begin
      match stack with
      | Atom value :: tail ->
        let* next = lower env state (Atom value :: tail) rest lrest in
        Ok { next with
          seq = cat (one env at (Op (Absolute (value, value)))) next.seq }
      | _ -> Error Stack
    end
  | C_mach.Same rest, C_mach.LSame (at, lrest) ->
    begin
      match stack with
      | Atom right :: Atom left :: tail ->
        let state = release right state in
        let* next = lower env state (Atom left :: tail) rest lrest in
        Ok { next with
          seq = cat (one env at (Op (Same (left, left, right)))) next.seq }
      | _ -> Error Stack
    end
  | C_mach.Order (rel, rest), C_mach.LOrder (found, at, lrest)
      when rel = found ->
    begin
      match stack with
      | Atom right :: Atom left :: tail ->
        let state = release right state in
        let* next = lower env state (Atom left :: tail) rest lrest in
        Ok { next with seq = cat (order env at rel left right) next.seq }
      | _ -> Error Stack
    end
  | C_mach.Join rest, C_mach.LJoin (at, lrest) ->
    begin
      match stack with
      | Atom right :: Atom left :: tail ->
        let state = release right state in
        let* next = lower env state (Atom left :: tail) rest lrest in
        Ok { next with
          seq = cat (one env at (Op (Join (left, left, right)))) next.seq }
      | _ -> Error Stack
    end
  | C_mach.Clip (len, rest), C_mach.LClip (found, at, lrest)
      when C_nat.equal len found ->
    begin
      match stack with
      | Atom src :: _ ->
        let* first, state = fresh_reg state in
        let* count, state = fresh_reg state in
        let state = release count (release first state) in
        let* next = lower env state stack rest lrest in
        let prefix =
          cat (one env at (Op (Load (first, C_emit.Int Z.zero))))
            (cat (one env at
                (Op (Load (count, C_emit.Int (C_nat.to_z len)))))
              (one env at (Op (Slice (src, src, first, count)))))
        in
        Ok { next with seq = cat prefix next.seq }
      | _ -> Error Stack
    end
  | C_mach.Skip (len, rest), C_mach.LSkip (found, at, lrest)
      when C_nat.equal len found ->
    begin
      match stack with
      | Atom src :: _ ->
        let* first, state = fresh_reg state in
        let* count, state = fresh_reg state in
        let state = release count (release first state) in
        let* next = lower env state stack rest lrest in
        let prefix =
          cat (one env at
              (Op (Load (first, C_emit.Int (C_nat.to_z len)))))
            (cat (one env at (Op (Size (count, src))))
              (cat (one env at (Op (Minus (count, count, first))))
                (one env at (Op (Slice (src, src, first, count))))))
        in
        Ok { next with seq = cat prefix next.seq }
      | _ -> Error Stack
    end
  | C_mach.Duo rest, C_mach.LDuo (_, lrest) ->
    begin
      match stack with
      | right :: left :: tail ->
        lower env state (Pair (left, right) :: tail) rest lrest
      | _ -> Error Stack
    end
  | C_mach.First rest, C_mach.LFirst (_, lrest) ->
    begin
      match stack with
      | Pair (left, right) :: tail ->
        lower env (release_layout right state) (left :: tail) rest lrest
      | _ -> Error Stack
    end
  | C_mach.Second rest, C_mach.LSecond (_, lrest) ->
    begin
      match stack with
      | Pair (left, right) :: tail ->
        lower env (release_layout left state) (right :: tail) rest lrest
      | _ -> Error Stack
    end
  | C_mach.Empty (elem, rest), C_mach.LEmpty (_, lrest) ->
    lower env state (Vec (elem, []) :: stack) rest lrest
  | C_mach.Cons rest, C_mach.LCons (_, lrest) ->
    begin
      match stack with
      | Vec (elem, values) :: first :: tail when fits elem first ->
        lower env state (Vec (elem, first :: values) :: tail) rest lrest
      | _ -> Error Stack
    end
  | C_mach.Append rest, C_mach.LAppend (_, lrest) ->
    begin
      match stack with
      | Vec (right_elem, right) :: Vec (left_elem, left) :: tail
          when C_mach.same_shape left_elem right_elem ->
        lower env state (Vec (left_elem, left @ right) :: tail) rest lrest
      | _ -> Error Stack
    end
  | C_mach.Pick (index, rest), C_mach.LPick (found, _, lrest)
      when C_nat.equal index found ->
    begin
      match stack with
      | Vec (_, values) :: tail ->
        begin
          match pick_layout (C_nat.to_int index) values state with
          | Some (value, state) -> lower env state (value :: tail) rest lrest
          | None -> Error Stack
        end
      | _ -> Error Stack
    end
  | C_mach.Unhead rest, C_mach.LUnhead (_, lrest) ->
    begin
      match stack with
      | Vec (elem, first :: values) :: tail ->
        lower env state
          (Pair (first, Vec (elem, values)) :: tail) rest lrest
      | _ -> Error Stack
    end
  | C_mach.Left rest, C_mach.LLeft (at, lrest) ->
    begin
      match stack with
      | payload :: tail ->
        let* tag, state = fresh_reg state in
        let* next = lower env state (Sum (tag, payload) :: tail) rest lrest in
        Ok { next with
          seq = cat (one env at (Op (Load (tag, C_emit.Bool true)))) next.seq }
      | [] -> Error Stack
    end
  | C_mach.Right rest, C_mach.LRight (at, lrest) ->
    begin
      match stack with
      | payload :: tail ->
        let* tag, state = fresh_reg state in
        let* next = lower env state (Sum (tag, payload) :: tail) rest lrest in
        Ok { next with
          seq = cat (one env at (Op (Load (tag, C_emit.Bool false)))) next.seq }
      | [] -> Error Stack
    end
  | C_mach.Scope (bind, body, rest), C_mach.LScope (_, lbody, lrest) ->
    begin
      match stack with
      | value :: tail ->
        let* opened =
          match open_cell bind value env with
          | Some value -> Ok value
          | None -> Error Slot
        in
        let* body_out = lower opened state tail body lbody in
        begin
          match exact tail body_out.stack with
          | None -> Error Stack
          | Some _ ->
            let* closed =
              match close_cell bind body_out.env with
              | Some value -> Ok value
              | None -> Error Slot
            in
            let state = release_layout value body_out.gen in
            let* next = lower closed state body_out.stack rest lrest in
            Ok { next with seq = cat body_out.seq next.seq }
        end
      | _ -> Error Stack
    end
  | C_mach.Scope2 (left_bind, right_bind, body, rest),
      C_mach.LScope2 (_, lbody, lrest) ->
    begin
      match stack with
      | Pair (left, right) :: tail ->
        let* first =
          match open_cell left_bind left env with
          | Some value -> Ok value
          | None -> Error Slot
        in
        let* opened =
          match open_cell right_bind right first with
          | Some value -> Ok value
          | None -> Error Slot
        in
        let* body_out = lower opened state tail body lbody in
        begin
          match exact tail body_out.stack with
          | None -> Error Stack
          | Some _ ->
            let* last =
              match close_cell right_bind body_out.env with
              | Some value -> Ok value
              | None -> Error Slot
            in
            let* closed =
              match close_cell left_bind last with
              | Some value -> Ok value
              | None -> Error Slot
            in
            let state =
              release_layout left (release_layout right body_out.gen)
            in
            let* next = lower closed state body_out.stack rest lrest in
            Ok { next with seq = cat body_out.seq next.seq }
        end
      | _ -> Error Stack
    end
  | C_mach.Iter (len, item_bind, state_bind, body, rest),
      C_mach.LIter (_, lbody, lrest) ->
    begin
      match item_bind.C_term.mul, state_bind.C_term.mul, stack,
          C_mach.shape_of item_bind.C_term.typ,
          C_mach.shape_of state_bind.C_term.typ with
      | C_type.Zero, _, _, _, _ | _, C_type.Zero, _, _, _ -> Error Slot
      | _, _, state_value :: Vec (elem, values) :: tail, Some item_shape,
          Some state_shape
          when List.length values = C_nat.to_int len
            && C_mach.same_shape item_shape elem
            && fits state_shape state_value
            && List.for_all (fits elem) values ->
        let rec loop env state state_value seq = function
          | [] ->
            let* next = lower env state (state_value :: tail) rest lrest in
            Ok { next with seq = cat seq next.seq }
          | item_value :: values ->
            let* first =
              match open_cell item_bind item_value env with
              | Some value -> Ok value
              | None -> Error Slot
            in
            let* opened =
              match open_cell state_bind state_value first with
              | Some value -> Ok value
              | None -> Error Slot
            in
            let* body_out = lower opened state tail body lbody in
            begin
              match exact tail body_out.stack with
              | None -> Error Stack
              | Some next_state ->
                let* last =
                  match close_cell state_bind body_out.env with
                  | Some value -> Ok value
                  | None -> Error Slot
                in
                let* closed =
                  match close_cell item_bind last with
                  | Some value -> Ok value
                  | None -> Error Slot
                in
                let state =
                  release_layout item_value
                    (release_layout state_value body_out.gen)
                in
                loop closed state next_state (cat seq body_out.seq) values
            end
        in
        loop env state state_value empty values
      | _ -> Error Stack
    end
  | C_mach.Choice (left_bind, yes, right_bind, no, form, rest),
      C_mach.LChoice (at, yes_at, no_at, lyes, lno, lrest) ->
    begin
      match stack with
      | Sum (guard, payload) :: tail ->
        let state = release guard state in
        let* dst, state = alloc form state in
        let yes_label, state = fresh_label state in
        let end_label, state = fresh_label state in
        let* no_env =
          match open_cell right_bind payload env with
          | Some value -> Ok value
          | None -> Error Slot
        in
        let* no_out = lower no_env state tail no lno in
        let* no_closed =
          match close_cell right_bind no_out.env with
          | Some value -> Ok value
          | None -> Error Slot
        in
        let yes_start = { state with label = no_out.gen.label } in
        let* yes_env =
          match open_cell left_bind payload env with
          | Some value -> Ok value
          | None -> Error Slot
        in
        let* yes_out = lower yes_env yes_start tail yes lyes in
        let* yes_closed =
          match close_cell left_bind yes_out.env with
          | Some value -> Ok value
          | None -> Error Slot
        in
        begin
          match exact tail no_out.stack, exact tail yes_out.stack with
          | Some no_value, Some yes_value
              when same_env no_closed yes_closed
                && fits form no_value && fits form yes_value ->
            let* no_move =
              match copy no_closed no_at no_value dst with
              | Some value -> Ok value
              | None -> Error Stack
            in
            let* yes_move =
              match copy yes_closed yes_at yes_value dst with
              | Some value -> Ok value
              | None -> Error Stack
            in
            let next_reg = Int.max no_out.gen.next yes_out.gen.next in
            let live =
              layout_regs dst
                (List.fold_right layout_regs tail (regs no_closed))
            in
            let state = {
              next = next_reg;
              free = avail next_reg live;
              label = yes_out.gen.label;
            } in
            let* next = lower no_closed state (dst :: tail) rest lrest in
            let branch =
              cat (one env at (Branch (guard, yes_label)))
                (cat no_out.seq
                  (cat no_move
                    (cat (one no_closed at (Goto end_label))
                      (cat (one env at (Place yes_label))
                        (cat yes_out.seq
                          (cat yes_move
                            (one no_closed at (Place end_label))))))))
            in
            Ok { next with seq = cat branch next.seq }
          | Some _, Some _ -> Error Slot
          | _ -> Error Stack
        end
      | _ -> Error Stack
    end
  | C_mach.Fork (form, yes, no, rest),
      C_mach.LFork (at, yes_at, no_at, lyes, lno, lrest) ->
    begin
      match stack with
      | Atom guard :: tail ->
        let state = release guard state in
        let* dst, state = alloc form state in
        let yes_label, state = fresh_label state in
        let end_label, state = fresh_label state in
        let* no_out = lower env state tail no lno in
        let yes_start = { state with label = no_out.gen.label } in
        let* yes_out = lower env yes_start tail yes lyes in
        begin
          match exact tail no_out.stack, exact tail yes_out.stack with
          | Some no_value, Some yes_value
              when same_env no_out.env yes_out.env
                && fits form no_value && fits form yes_value ->
            let* no_move =
              match copy no_out.env no_at no_value dst with
              | Some value -> Ok value
              | None -> Error Stack
            in
            let* yes_move =
              match copy yes_out.env yes_at yes_value dst with
              | Some value -> Ok value
              | None -> Error Stack
            in
            let next_reg = Int.max no_out.gen.next yes_out.gen.next in
            let live =
              layout_regs dst
                (List.fold_right layout_regs tail (regs no_out.env))
            in
            let state = {
              next = next_reg;
              free = avail next_reg live;
              label = yes_out.gen.label;
            } in
            let* next =
              lower no_out.env state (dst :: tail) rest lrest
            in
            let branch =
              cat (one env at (Branch (guard, yes_label)))
                (cat no_out.seq
                  (cat no_move
                    (cat (one no_out.env at (Goto end_label))
                      (cat (one env at (Place yes_label))
                        (cat yes_out.seq
                          (cat yes_move
                            (one no_out.env at (Place end_label))))))))
            in
            Ok { next with seq = cat branch next.seq }
          | Some _, Some _ -> Error Slot
          | _ -> Error Stack
        end
      | _ -> Error Stack
    end
  | _ -> Error Map

let rec label id = function
  | [] -> None
  | (key, value) :: _ when key = id -> Some value
  | _ :: rest -> label id rest

let places values =
  let rec walk pc out = function
    | [] -> Ok out
    | { asm = Place id; _ } :: _ when Option.is_some (label id out) ->
        Error Label
    | { asm = Place id; _ } :: rest ->
        walk (pc + 1) ((id, pc) :: out) rest
    | _ :: rest -> walk (pc + 1) out rest
  in
  walk 0 [] values

let resolve values =
  let* labels = places values in
  let one = function
    | Op value -> Ok value
    | Goto id -> Option.fold ~none:(Error Label) ~some:(fun pc -> Ok (Jump pc)) (label id labels)
    | Branch (reg, id) ->
      Option.fold ~none:(Error Label) ~some:(fun pc -> Ok (Jump_if (reg, pc))) (label id labels)
    | Place id -> Option.fold ~none:(Error Label) ~some:(fun pc -> Ok (Mark pc)) (label id labels)
    | Apply _ -> Ok Noop
  in
  let rec walk code map live effects = function
    | [] ->
      Ok (Array.of_list (List.rev code), Array.of_list (List.rev map),
        Array.of_list (List.rev live), List.rev effects)
    | value :: rest ->
      let* op = one value.asm in
      let effects =
        match value.asm with
        | Apply layout -> layout :: effects
        | Op _ | Goto _ | Branch _ | Place _ -> effects
      in
      walk (op :: code) (value.at :: map) (value.live :: live) effects rest
  in
  walk [] [] [] [] values

let final_cell inputs cell =
  match
    List.find_opt
      (fun bind -> C_nat.equal bind.C_term.id cell.bind.C_term.id)
      inputs
  with
  | Some bind ->
    begin
      match bind.mul, cell.bind.mul, cell.live with
      | C_type.One, C_type.One, false -> true
      | C_type.Many, C_type.Many, true -> true
      | _ -> false
    end
  | None -> false

let final_env inputs env =
  let expected =
    List.filter (fun bind -> bind.C_term.mul <> C_type.Zero) inputs
  in
  List.length expected = List.length env
  && List.for_all (final_cell inputs) env

let seed inputs =
  if List.length inputs > input_limit then Error Register
  else
    let rec walk index env free = function
      | [] -> Ok (List.rev env, List.rev free)
      | bind :: rest ->
        let reg = index + 1 in
        begin
          match bind.C_term.mul with
          | C_type.Zero -> walk (index + 1) env (reg :: free) rest
          | C_type.One | C_type.Many ->
            let cell = { bind; layout = Atom reg; live = true } in
            walk (index + 1) (cell :: env) free rest
        end
    in
    walk 0 [] [] inputs

let lower_plan inputs plan loc at =
  let* env, free = seed inputs in
  let state = {
    next = List.length inputs + 1;
    free;
    label = 0;
  }
  in
  let* out = lower env state [] plan loc in
  match out.stack with
  | [Atom result] when final_env inputs out.env ->
    let suffix =
      if result = 0 then one out.env at (Op Stop)
      else
        cat
          (one out.env at (Op (Move (0, result))))
          (one out.env at (Op Stop))
    in
    let* code, map, live, effects = resolve (out.seq (suffix [])) in
    Ok (code, map, live, effects,
      Array.init (List.length inputs) (fun index -> index + 1))
  | [Atom _] -> Error Slot
  | [_] -> Error Stack
  | _ -> Error Stack

let effect_count info =
  let limit = Z.of_int C_check.max_nodes in
  let rec walk total = function
    | [] -> true
    | location :: rest ->
      let total = Z.add total location.C_check.count in
      Z.leq total limit && walk total rest
  in
  walk Z.zero (C_check.locations info)

let effect_plan (program : C_low.prog) =
  let* info =
    match C_check.check_in program.inputs program.term with
    | Ok value -> Ok value
    | Error _ -> Error Effect_map
  in
  if Z.gt info.C_check.res.steps C_eval.max_cost then Error Effect_map
  else if not (effect_count info) then Error Effect_map
  else
  let* plan =
    match C_mach.lower_in program.inputs program.term with
    | Some value -> Ok value
    | None -> Error Effect_map
  in
  Ok (info, plan)

let effect_layouts program =
  let* info, plan = effect_plan program in
  let pos = { C_lex.off = 0; line = 1; col = 1 } in
  let at = { C_lex.first = pos; last = pos } in
  let loc = C_mach.locate at plan in
  let* env, free = seed program.inputs in
  let state = {
    next = List.length program.inputs + 1;
    free;
    label = 0;
  }
  in
  let* out = lower env state [] plan loc in
  let* layouts =
    if List.length out.stack = 1 && final_env program.inputs out.env then
      let* _, _, _, value = resolve (out.seq []) in
      Ok value
    else Error Effect_map
  in
  let layouts = List.sort (fun left right -> Int.compare left.index right.index)
    layouts in
  let locations = C_check.locations info in
  let rec take index atom left out = function
    | rest when left = 0 -> Ok (out, rest)
    | layout :: rest when layout.index = index && layout.atom = atom ->
      take index atom (left - 1) (layout :: out) rest
    | _ -> Error Effect_map
  in
  let rec exact index layouts out = function
    | [] -> if layouts = [] then Ok (List.rev out) else Error Effect_map
    | location :: rest when location.C_check.index = index ->
      if not (Z.fits_int location.count) then Error Effect_map
      else
        let count = Z.to_int location.count in
        let* out, layouts =
          take index location.site.atom count out layouts
        in
        exact (index + 1) layouts out rest
    | _ -> Error Effect_map
  in
  exact 0 layouts [] locations

let const_data = function
  | C_emit.Bool value -> 1, if value then "1" else "0"
  | C_emit.Int value -> 0, Z.to_string value
  | C_emit.Bytes value -> 3, value
  | C_emit.Data value -> 2, C_rval.encode value

module Lit_ord = struct
  type t = int * string

  let compare (left_tag, left_value) (right_tag, right_value) =
    let by_tag = Int.compare left_tag right_tag in
    if by_tag <> 0 then by_tag else String.compare left_value right_value
end

module Lit_map = Map.Make(Lit_ord)

let pool code =
  let add (rev, pos, len) = function
    | Load (_, value) ->
      let key = const_data value in
      if Lit_map.mem key pos then rev, pos, len
      else value :: rev, Lit_map.add key len pos, len + 1
    | _ -> rev, pos, len
  in
  let rev, pos, len =
    Array.fold_left add ([], Lit_map.empty, 0) code
  in
  List.rev rev, pos, len

let vm_lit = function
  | C_emit.Bool value -> Contract_vm.VBool value
  | C_emit.Int value -> Contract_vm.VInt value
  | C_emit.Bytes value -> Contract_vm.VBytes value
  | C_emit.Data value -> Contract_vm.VString (C_rval.encode value)

let vm_op = function
  | Load (dst, value) -> Contract_vm.LDI (dst, vm_lit value)
  | Move (dst, src) -> Contract_vm.MOV (dst, src)
  | Plus (dst, left, right) -> Contract_vm.ADD (dst, left, right)
  | Times (dst, left, right) -> Contract_vm.MUL (dst, left, right)
  | Quotient (dst, left, right) -> Contract_vm.DIV (dst, left, right)
  | Remainder (dst, left, right) -> Contract_vm.MOD (dst, left, right)
  | Negate (dst, src) -> Contract_vm.NEG (dst, src)
  | Absolute (dst, src) -> Contract_vm.ABS (dst, src)
  | Same (dst, left, right) -> Contract_vm.EQ (dst, left, right)
  | Less (dst, left, right) -> Contract_vm.LT (dst, left, right)
  | Greater (dst, left, right) -> Contract_vm.GT (dst, left, right)
  | Join (dst, left, right) -> Contract_vm.CONCAT (dst, left, right)
  | Minus (dst, left, right) -> Contract_vm.SUB (dst, left, right)
  | Size (dst, src) -> Contract_vm.STRLEN (dst, src)
  | Slice (dst, src, first, count) ->
    Contract_vm.SUBSTR (dst, src, first, count)
  | Jump at -> Contract_vm.JMP at
  | Jump_if (reg, at) -> Contract_vm.JIF (reg, at)
  | Mark at -> Contract_vm.JDEST at
  | Noop -> Contract_vm.NOP
  | Stop -> Contract_vm.STOP

type piece =
  | Plain of marked
  | Host of marked * Contract_vm.instr list

let rec compare_regs left right =
  match left, right with
  | [], [] -> 0
  | [], _ -> -1
  | _, [] -> 1
  | lhs :: lrest, rhs :: rrest ->
    let order = Int.compare lhs rhs in
    if order = 0 then compare_regs lrest rrest else order

module Layout_order = struct
  type t = effect_layout

  let compare left right =
    let index = Int.compare left.index right.index in
    if index <> 0 then index
    else
      let atom = C_eff.compare left.atom right.atom in
      if atom <> 0 then atom
      else
        let payload = compare_regs left.payload right.payload in
        if payload <> 0 then payload
        else compare_regs left.scratch right.scratch
end

module Layout_map = Map.Make(Layout_order)

let block_rows blocks =
  let rec collect rows = function
    | [] -> Ok (Layout_map.map List.rev rows)
    | (_, []) :: _ -> Error Effect_map
    | (layout, ops) :: rest ->
      let found = Option.value ~default:[] (Layout_map.find_opt layout rows) in
      collect (Layout_map.add layout (ops :: found) rows) rest
  in
  collect Layout_map.empty blocks

let take_effect layout rows =
  match Layout_map.find_opt layout rows with
  | Some (ops :: rest) ->
    let rows =
      match rest with
      | [] -> Layout_map.remove layout rows
      | _ -> Layout_map.add layout rest rows
    in
    Some (ops, rows)
  | Some [] | None -> None

let attach_effects values blocks =
  let* rows = block_rows blocks in
  let rec walk out rows = function
    | [] ->
      if Layout_map.is_empty rows then Ok (List.rev out)
      else Error Effect_map
    | ({ asm = Apply layout; _ } as value) :: rest ->
      begin
        match take_effect layout rows with
        | Some (ops, rows) -> walk (Host (value, ops) :: out) rows rest
        | None -> Error Effect_map
      end
    | value :: rest -> walk (Plain value :: out) rows rest
  in
  walk [] rows values

let effect_places values =
  let rec walk pc out = function
    | [] -> Ok out
    | Plain { asm = Place id; _ } :: _
        when Option.is_some (label id out) -> Error Label
    | Plain { asm = Place id; _ } :: rest ->
      walk (pc + 1) ((id, pc) :: out) rest
    | Host (_, ops) :: rest -> walk (pc + List.length ops) out rest
    | Plain _ :: rest -> walk (pc + 1) out rest
  in
  walk 0 [] values

let resolve_effects values =
  let* labels = effect_places values in
  let one = function
    | Op value -> Ok (vm_op value)
    | Goto id ->
      Option.fold ~none:(Error Label)
        ~some:(fun pc -> Ok (Contract_vm.JMP pc)) (label id labels)
    | Branch (reg, id) ->
      Option.fold ~none:(Error Label)
        ~some:(fun pc -> Ok (Contract_vm.JIF (reg, pc))) (label id labels)
    | Place id ->
      Option.fold ~none:(Error Label)
        ~some:(fun pc -> Ok (Contract_vm.JDEST pc)) (label id labels)
    | Apply _ -> Error Effect_map
  in
  let rec walk out = function
    | [] -> Ok (Array.of_list (List.rev out))
    | Host (_, ops) :: rest -> walk (List.rev_append ops out) rest
    | Plain value :: rest ->
      let* op = one value.asm in
      walk (op :: out) rest
  in
  walk [] values

let emit_effects program blocks =
  let* _, plan = effect_plan program in
  let pos = { C_lex.off = 0; line = 1; col = 1 } in
  let at = { C_lex.first = pos; last = pos } in
  let loc = C_mach.locate at plan in
  let* env, free = seed program.inputs in
  let state = {
    next = List.length program.inputs + 1;
    free;
    label = 0;
  }
  in
  let* out = lower env state [] plan loc in
  match out.stack with
  | [Atom result] when final_env program.inputs out.env ->
    let suffix =
      if result = 0 then one out.env at (Op Stop)
      else
        cat
          (one out.env at (Op (Move (0, result))))
          (one out.env at (Op Stop))
    in
    let* values = attach_effects (out.seq (suffix [])) blocks in
    let* code = resolve_effects values in
    begin
      match Bytecode.decode_image (Bytecode.encode code) with
      | Ok image when image.code = code -> Ok code
      | Ok _ | Error _ -> Error Output_code
    end
  | [Atom _] -> Error Slot
  | [_] -> Error Stack
  | _ -> Error Stack

let encode_raw ?emission ?veil code =
  let _, _, count = pool code in
  if count > 32768 then Error (Constants count)
  else Ok (Bytecode.encode ?emission ?veil (Array.map vm_op code))

let body_label at = 10_000_000 + at

let open_vm_op = function
  | Jump at -> Contract_vm.JMP (body_label at)
  | Jump_if (reg, at) -> Contract_vm.JIF (reg, body_label at)
  | Mark at -> Contract_vm.JDEST (body_label at)
  | value -> vm_op value

let check_label index = 1000 + index

let input_code index reg typ =
  let load = Contract_vm.MLOAD (reg, 1001 + index) in
  match typ with
  | C_type.Int -> [
      load;
      Contract_vm.LDI (61, Contract_vm.VInt Z.zero);
      Contract_vm.SUB (reg, reg, 61);
    ]
  | C_type.Bool ->
    let label = check_label index in
    [
      load;
      Contract_vm.JIF (reg, label);
      Contract_vm.JMP label;
      Contract_vm.JDEST label;
    ]
  | C_type.Bytes len ->
    let label = check_label index in
    [
      load;
      Contract_vm.LDI (61, Contract_vm.VBytes "");
      Contract_vm.EQ (63, reg, 61);
      Contract_vm.STRLEN (61, reg);
      Contract_vm.LDI (62, Contract_vm.VInt (C_nat.to_z len));
      Contract_vm.EQ (63, 61, 62);
      Contract_vm.JIF (63, label);
      Contract_vm.REVERT;
      Contract_vm.JDEST label;
      Contract_vm.LDI (61, Contract_vm.VInt Z.zero);
      Contract_vm.SUBSTR (reg, reg, 61, 62);
    ]
  | C_type.Unit | C_type.Vec _ | C_type.Cap _ | C_type.Enc _
  | C_type.Pair _ | C_type.Sum _ -> invalid_arg "machine input is not scalar"

let result_code typ code =
  let count = Array.length code in
  if count = 0 || code.(count - 1) <> Stop then None
  else
    let body = Array.sub code 0 (count - 1) in
    let first = Array.length body in
    let tail =
      match typ with
      | C_type.Int -> [|
          Load (61, C_emit.Int Z.zero);
          Minus (0, 0, 61);
          Stop;
        |]
      | C_type.Bool ->
        let mark = first + 2 in
        [|Jump_if (0, mark); Jump mark; Mark mark; Stop|]
      | C_type.Bytes len ->
        let mark = first + 9 in
        [|
          Load (61, C_emit.Bytes "");
          Same (63, 0, 61);
          Size (61, 0);
          Load (62, C_emit.Int (C_nat.to_z len));
          Same (63, 61, 62);
          Jump_if (63, mark);
          Load (61, C_emit.Int Z.one);
          Load (62, C_emit.Int Z.zero);
          Quotient (61, 61, 62);
          Mark mark;
          Stop;
        |]
      | C_type.Unit | C_type.Vec _ | C_type.Cap _ | C_type.Enc _
      | C_type.Pair _ | C_type.Sum _ -> [||]
    in
    if Array.length tail = 0 then None else Some (Array.append body tail)

let encode_open emission veil inputs regs typ code =
  let* code =
    match result_code typ code with
    | Some value -> Ok value
    | None -> Error Output_code
  in
  let _, _, count = pool code in
  if count > 32768 then Error (Constants count)
  else
    let head = [
      Contract_vm.JDEST 100;
      Contract_vm.MLOAD (61, 1000);
      Contract_vm.LDI (62, Contract_vm.VString "main");
      Contract_vm.EQ (63, 61, 62);
      Contract_vm.JIF (63, 200);
      Contract_vm.REVERT;
      Contract_vm.JDEST 200;
    ]
    in
    let args =
      List.mapi
        (fun index bind -> input_code index regs.(index) bind.C_term.typ)
        inputs
      |> List.concat
    in
    let body = Array.to_list (Array.map open_vm_op code) in
    Ok
      (Bytecode.encode ~emission:(wire_emission emission) ~veil
        (Array.of_list (head @ args @ [Contract_vm.NOP] @ body)))

type reader = {
  raw : string;
  size : int;
  mutable at : int;
}

exception Read_error of decode_error

let refuse error = raise (Read_error error)

let require input count error =
  if count < 0 || count > input.size - input.at then refuse error

let read_u8 input error =
  require input 1 error;
  let value = Char.code input.raw.[input.at] in
  input.at <- input.at + 1;
  value

let read_u16 input error =
  let first = read_u8 input error in
  let second = read_u8 input error in
  first lor (second lsl 8)

let read_u32 input error =
  let first = Int64.of_int (read_u8 input error) in
  let second = Int64.shift_left (Int64.of_int (read_u8 input error)) 8 in
  let third = Int64.shift_left (Int64.of_int (read_u8 input error)) 16 in
  let fourth = Int64.shift_left (Int64.of_int (read_u8 input error)) 24 in
  Int64.logor first (Int64.logor second (Int64.logor third fourth))

let read_size input count error =
  require input count error;
  let value = String.sub input.raw input.at count in
  input.at <- input.at + count;
  value

let int64 maximum error value =
  if Int64.compare value (Int64.of_int maximum) > 0 then refuse error;
  Int64.to_int value

let max_consts = 32768
let max_instructions = 1_048_576
let max_constant_bytes = 16_777_216
let max_input_bytes = 67_108_864

let constant input id =
  let at = input.at in
  let header = Constant_header id in
  let tag = read_u8 input header in
  let raw_size = read_u32 input header in
  let size = int64 max_constant_bytes (Constant_size (id, max_constant_bytes)) raw_size in
  let raw = read_size input size (Constant_data id) in
  let value =
    match tag with
    | 0 ->
      begin
        try
          let value = Z.of_string raw in
          if not (String.equal (Z.to_string value) raw) then
            refuse (Constant_value id);
          CInt raw
        with Invalid_argument _ -> refuse (Constant_value id)
      end
    | 1 when String.equal raw "0" -> CBool false
    | 1 when String.equal raw "1" -> CBool true
    | 1 -> refuse (Constant_value id)
    | 2 ->
      begin
        match C_rval.decode raw with
        | Ok value when String.equal (C_rval.encode value) raw -> CData value
        | Ok _ | Error _ -> CText raw
      end
    | 3 -> CBytes raw
    | _ -> refuse (Constant_tag (id, tag))
  in
  { id; at; size = input.at - at; value }

let reg pc value =
  if value >= 64 then refuse (Register_ref (pc, value));
  value

let vm_value pc = function
  | Contract_vm.VInt value -> C_emit.Int value
  | Contract_vm.VBool value -> C_emit.Bool value
  | Contract_vm.VBytes value -> C_emit.Bytes value
  | Contract_vm.VString value ->
    begin
      match C_rval.decode value with
      | Ok data when String.equal (C_rval.encode data) value -> C_emit.Data data
      | Ok _ | Error _ -> refuse (Instruction_data pc)
    end
  | Contract_vm.VBytes32 _
  | Contract_vm.VU64 _
  | Contract_vm.VU128 _
  | Contract_vm.VU256 _
  | Contract_vm.VAddr _
  | Contract_vm.VCipher _
  | Contract_vm.VPubKey _ -> refuse (Instruction_data pc)

let profile_op pc value =
  let r = reg pc in
  match value with
  | Contract_vm.LDI (dst, value) -> Load (r dst, vm_value pc value)
  | Contract_vm.MOV (dst, src) -> Move (r dst, r src)
  | Contract_vm.ADD (dst, left, right) -> Plus (r dst, r left, r right)
  | Contract_vm.SUB (dst, left, right) -> Minus (r dst, r left, r right)
  | Contract_vm.MUL (dst, left, right) -> Times (r dst, r left, r right)
  | Contract_vm.DIV (dst, left, right) ->
    Quotient (r dst, r left, r right)
  | Contract_vm.MOD (dst, left, right) ->
    Remainder (r dst, r left, r right)
  | Contract_vm.NEG (dst, src) -> Negate (r dst, r src)
  | Contract_vm.ABS (dst, src) -> Absolute (r dst, r src)
  | Contract_vm.EQ (dst, left, right) -> Same (r dst, r left, r right)
  | Contract_vm.LT (dst, left, right) -> Less (r dst, r left, r right)
  | Contract_vm.GT (dst, left, right) -> Greater (r dst, r left, r right)
  | Contract_vm.CONCAT (dst, left, right) ->
    Join (r dst, r left, r right)
  | Contract_vm.STRLEN (dst, src) -> Size (r dst, r src)
  | Contract_vm.SUBSTR (dst, src, first, count) ->
    Slice (r dst, r src, r first, r count)
  | Contract_vm.JMP at -> Jump at
  | Contract_vm.JIF (guard, at) -> Jump_if (r guard, at)
  | Contract_vm.JDEST at -> Mark at
  | Contract_vm.NOP -> Noop
  | Contract_vm.STOP -> Stop
  | value -> refuse (Opcode (pc, Bytecode.op_tag value))

let decode_failure reason =
  if String.equal reason "OCTB AML emission is invalid" then Emission_invalid
  else if String.equal reason "OCTB AML emission is repeated" then
    Emission_repeated
  else if String.equal reason "OCTB AML veil is invalid" then Veil_invalid
  else if String.equal reason "OCTB AML veil is repeated" then Veil_repeated
  else
    try
      Scanf.sscanf reason "unsupported OCTB version: %d"
        (fun version -> Version version)
    with _ ->
      try
        Scanf.sscanf reason "unknown opcode 0x%x at pc %d"
          (fun tag pc -> Opcode (pc, tag))
      with _ ->
        try
          Scanf.sscanf reason "truncated instruction at pc %d"
            (fun pc -> Instruction_data pc)
        with _ ->
          try
            Scanf.sscanf reason "constant reference %d at pc %d"
              (fun id pc -> Constant_ref (pc, id))
          with _ ->
            try
              Scanf.sscanf reason "OCTB trailing bytes: %d"
                (fun count -> Trailing_data count)
            with _ -> Instruction_data 0

let claims_aml raw =
  try
    let size = String.length raw in
    if size > max_input_bytes || size < 12 then false
    else
      let input = { raw; size; at = 0 } in
      if not (String.equal (read_size input 4 Header) "OCTB") then false
      else if read_u16 input Header <> 1 then false
      else
        let count = read_u16 input Header in
        if count > max_consts then false
        else begin
          ignore (read_u32 input Header);
          Array.init count (constant input)
          |> Array.exists (fun row ->
            match row.value with
            | CText value ->
              Bytecode.emission_value value || Bytecode.veil_value value
            | _ -> false)
        end
  with Read_error _ -> false

let verify code =
  if Array.length code = 0 then refuse Empty_code;
  Array.iteri
    (fun pc -> function
      | Mark value when value <> pc -> refuse (Jump_mark pc)
      | _ -> ())
    code;
  let jump pc target =
    if target < 0 || target >= Array.length code then
      refuse (Jump_ref (pc, target));
    match code.(target) with
    | Mark value when value = target -> ()
    | _ -> refuse (Jump_ref (pc, target))
  in
  Array.iteri
    (fun pc -> function
      | Jump target | Jump_if (_, target) -> jump pc target
      | _ -> ())
    code

let open_header code =
  Array.length code >= 8
  && match code.(0), code.(1), code.(2), code.(3), code.(4), code.(5),
      code.(6) with
    | Contract_vm.JDEST 100,
        Contract_vm.MLOAD (61, 1000),
        Contract_vm.LDI (62, Contract_vm.VString name),
        Contract_vm.EQ (63, 61, 62),
        Contract_vm.JIF (63, 200),
        Contract_vm.REVERT,
        Contract_vm.JDEST 200 -> String.equal name "main"
    | _ -> false

let claims_open raw =
  try
    let size = String.length raw in
    if size > max_input_bytes || size < 12 then false
    else
      let input = { raw; size; at = 0 } in
      if not (String.equal (read_size input 4 Header) "OCTB") then false
      else if read_u16 input Header <> 1 then false
      else
        let count = read_u16 input Header in
        let instructions = read_u32 input Header in
        if count > max_consts || Int64.compare instructions (Int64.of_int 7) < 0
        then false
        else
          let consts = Array.init count (constant input) in
          let byte wanted = read_u8 input Header = wanted in
          let word wanted = read_u16 input Header = wanted in
          let wide wanted =
            Int64.equal (read_u32 input Header) (Int64.of_int wanted)
          in
          if not (byte 0x16 && wide 100) then false
          else if not (byte 0x12 && byte 61 && word 1000) then false
          else if not (byte 0x0B && byte 62) then false
          else
            let id = read_u16 input Header in
            let main =
              id < Array.length consts
              && match consts.(id).value with
                | CText value -> String.equal value "main"
                | CInt _ | CBool _ | CData _ | CBytes _ -> false
            in
            main
            && byte 0x07 && byte 63 && byte 61 && byte 62
            && byte 0x15 && byte 63 && wide 200
            && byte 0x18
            && byte 0x16 && wide 200
  with Read_error _ -> false

let input_type code pc index =
  let count = Array.length code in
  let reg = index + 1 in
  let address = 1001 + index in
  let label = check_label index in
  if pc + 2 < count then
    match code.(pc), code.(pc + 1), code.(pc + 2) with
    | Contract_vm.MLOAD (dst, at),
        Contract_vm.LDI (61, Contract_vm.VInt zero),
        Contract_vm.SUB (out, source, 61)
        when dst = reg && at = address && out = reg && source = reg
          && Z.equal zero Z.zero -> Some (C_type.Int, pc + 3)
    | _ ->
      if pc + 3 < count then
        match code.(pc), code.(pc + 1), code.(pc + 2), code.(pc + 3) with
        | Contract_vm.MLOAD (dst, at),
            Contract_vm.JIF (guard, yes),
            Contract_vm.JMP no,
            Contract_vm.JDEST mark
            when dst = reg && at = address && guard = reg
              && yes = label && no = label && mark = label ->
          Some (C_type.Bool, pc + 4)
        | _ ->
          if pc + 10 < count then
            match code.(pc), code.(pc + 1), code.(pc + 2), code.(pc + 3),
                code.(pc + 4), code.(pc + 5), code.(pc + 6), code.(pc + 7),
                code.(pc + 8), code.(pc + 9), code.(pc + 10) with
            | Contract_vm.MLOAD (dst, at),
                Contract_vm.LDI (61, Contract_vm.VBytes empty),
                Contract_vm.EQ (kind, left, 61),
                Contract_vm.STRLEN (size, text),
                Contract_vm.LDI (62, Contract_vm.VInt raw_len),
                Contract_vm.EQ (same, found, 62),
                Contract_vm.JIF (guard, yes),
                Contract_vm.REVERT,
                Contract_vm.JDEST mark,
                Contract_vm.LDI (61, Contract_vm.VInt zero),
                Contract_vm.SUBSTR (out, source, first, length)
                when dst = reg && at = address && String.equal empty ""
                  && kind = 63 && left = reg && size = 61 && text = reg
                  && same = 63 && found = 61 && guard = 63
                  && yes = label && mark = label && Z.equal zero Z.zero
                  && out = reg && source = reg && first = 61 && length = 62 ->
              Option.map
                (fun len -> C_type.Bytes len, pc + 11)
                (C_nat.make raw_len)
            | _ -> None
          else None
      else None
  else None

let open_target pc count target =
  let local = target - body_label 0 in
  if local < 0 || local >= count then refuse (Jump_ref (pc, target));
  local

let open_code native at =
  let count = Array.length native - at in
  if count <= 0 then refuse Empty_code;
  let code =
    Array.init count (fun pc ->
      match native.(at + pc) with
      | Contract_vm.JMP target -> Jump (open_target (at + pc) count target)
      | Contract_vm.JIF (guard, target) ->
        Jump_if (reg (at + pc) guard, open_target (at + pc) count target)
      | Contract_vm.JDEST target ->
        if target = body_label pc then Mark pc
        else refuse (Jump_ref (at + pc, target))
      | value -> profile_op (at + pc) value)
  in
  verify code;
  code

let result_type code =
  let count = Array.length code in
  let at size = count - size in
  if count >= 3 then
    match code.(at 3), code.(at 2), code.(at 1) with
    | Load (61, C_emit.Int zero), Minus (0, 0, 61), Stop
        when Z.equal zero Z.zero -> Some (C_type.Int, at 3)
    | _ ->
      if count >= 4 then
        match code.(at 4), code.(at 3), code.(at 2), code.(at 1) with
        | Jump_if (0, yes), Jump no, Mark mark, Stop
            when yes = at 2 && no = at 2 && mark = at 2 ->
          Some (C_type.Bool, at 4)
        | _ ->
          if count >= 11 then
            match code.(at 11), code.(at 10), code.(at 9), code.(at 8),
                code.(at 7), code.(at 6), code.(at 5), code.(at 4),
                code.(at 3), code.(at 2), code.(at 1) with
            | Load (61, C_emit.Bytes empty), Same (63, 0, 61), Size (61, 0),
                Load (62, C_emit.Int raw_len), Same (63, 61, 62),
                Jump_if (63, yes), Load (61, C_emit.Int one),
                Load (62, C_emit.Int zero), Quotient (61, 61, 62),
                Mark mark, Stop
                when String.equal empty "" && Z.equal one Z.one
                  && Z.equal zero Z.zero && yes = at 2 && mark = at 2 ->
              Option.map (fun len -> C_type.Bytes len, at 11)
                (C_nat.make raw_len)
            | _ -> None
          else None
      else None
  else None

let verify_result code first =
  Array.iteri
    (fun pc -> function
      | Stop when pc < first -> refuse Result_header
      | Jump target | Jump_if (_, target)
          when pc < first && target >= first -> refuse Result_header
      | _ -> ())
    code

let open_profile native =
  if not (open_header native) then None
  else
    let rec inputs pc index out =
      if pc >= Array.length native then refuse Empty_code
      else
        match native.(pc) with
        | Contract_vm.NOP ->
          if index = 0 then refuse Empty_code;
          Some (Array.of_list (List.rev out), pc + 1)
        | _ when index >= input_limit ->
          refuse (Register_ref (pc, index + 1))
        | _ ->
          begin
            match input_type native pc index with
            | Some (typ, next) -> inputs next (index + 1) (typ :: out)
            | None -> refuse (Opcode (pc, Bytecode.op_tag native.(pc)))
          end
    in
    match inputs 7 0 [] with
    | Some (types, at) ->
      let code = open_code native at in
      begin
        match result_type code with
        | Some (output, first) ->
          verify_result code first;
          Some (types, output, at, code)
        | None -> refuse Result_header
      end
    | None -> None

let decode raw =
  try
    let size = String.length raw in
    if size > max_input_bytes then refuse (Input_size size);
    if size < 12 then refuse Header;
    let input = { raw; size; at = 0 } in
    if not (String.equal (read_size input 4 Header) "OCTB") then refuse Magic;
    let version = read_u16 input Header in
    if version <> 1 then refuse (Version version);
    let const_count = read_u16 input Header in
    if const_count > max_consts then refuse (Constant_count const_count);
    let raw_count = read_u32 input Header in
    let instruction_count =
      int64 max_instructions (Instruction_count raw_count) raw_count
    in
    let consts = Array.init const_count (constant input) in
    let text_at = input.at in
    let native =
      match Bytecode.decode_image raw with
      | Ok image -> image
      | Error reason -> refuse (decode_failure reason)
    in
    if native.Bytecode.text_at <> text_at then refuse Header;
    if Array.length native.code <> instruction_count then
      refuse (Instruction_count raw_count);
    if not
        (String.equal raw
          (Bytecode.encode ?emission:native.emission ?veil:native.veil native.code))
    then refuse Exact_image;
    let emission = Option.map local_emission native.emission in
    let veil =
      match native.veil with
      | None -> None
      | Some value ->
        begin
          match local_veil value with
          | Some veil -> Some veil
          | None -> refuse Veil_invalid
        end
    in
    let inputs, output, code_at, code =
      match open_profile native.code with
      | Some (inputs, output, at, code) ->
        inputs, Some output, at, code
      | None -> [||], None, 0, Array.mapi profile_op native.code
    in
    let cells =
      Array.init (Array.length code) (fun pc ->
        let cell = native.cells.(code_at + pc) in
        { pc; at = cell.at; size = cell.size })
    in
    verify code;
    Ok { inputs; output; emission; veil; consts; cells; text_at; code }
  with Read_error error -> Error error

let encode code =
  let* raw = encode_raw code in
  match decode raw with
  | Ok image
      when Array.length image.inputs = 0 && Option.is_none image.output
        && image.code = code -> Ok raw
  | Ok _ -> Error Output_code
  | Error error -> Error (Output error)

let lit_text = function
  | C_emit.Bool value -> "bool:" ^ string_of_bool value
  | C_emit.Int value -> "int:" ^ Z.to_string value
  | C_emit.Bytes value -> Printf.sprintf "bytes[%d]" (String.length value)
  | C_emit.Data value -> "data[" ^ C_type.text (C_rval.typ value) ^ "]"

let op_text = function
  | Load (dst, value) -> Printf.sprintf "ldi(r%d,%s)" dst (lit_text value)
  | Move (dst, src) -> Printf.sprintf "mov(r%d,r%d)" dst src
  | Plus (dst, left, right) ->
    Printf.sprintf "add(r%d,r%d,r%d)" dst left right
  | Times (dst, left, right) ->
    Printf.sprintf "mul(r%d,r%d,r%d)" dst left right
  | Quotient (dst, left, right) ->
    Printf.sprintf "div(r%d,r%d,r%d)" dst left right
  | Remainder (dst, left, right) ->
    Printf.sprintf "mod(r%d,r%d,r%d)" dst left right
  | Negate (dst, src) -> Printf.sprintf "neg(r%d,r%d)" dst src
  | Absolute (dst, src) -> Printf.sprintf "abs(r%d,r%d)" dst src
  | Same (dst, left, right) ->
    Printf.sprintf "eq(r%d,r%d,r%d)" dst left right
  | Less (dst, left, right) ->
    Printf.sprintf "lt(r%d,r%d,r%d)" dst left right
  | Greater (dst, left, right) ->
    Printf.sprintf "gt(r%d,r%d,r%d)" dst left right
  | Join (dst, left, right) ->
    Printf.sprintf "concat(r%d,r%d,r%d)" dst left right
  | Minus (dst, left, right) ->
    Printf.sprintf "sub(r%d,r%d,r%d)" dst left right
  | Size (dst, src) -> Printf.sprintf "strlen(r%d,r%d)" dst src
  | Slice (dst, src, first, count) ->
    Printf.sprintf "substr(r%d,r%d,r%d,r%d)" dst src first count
  | Jump at -> Printf.sprintf "jmp(%d)" at
  | Jump_if (reg, at) -> Printf.sprintf "jif(r%d,%d)" reg at
  | Mark at -> Printf.sprintf "jdest(%d)" at
  | Noop -> "nop"
  | Stop -> "stop"

let decode_text = function
  | Input_size value ->
    Printf.sprintf "OCTB input size = %d maximum = %d" value max_input_bytes
  | Header -> "OCTB header is incomplete"
  | Magic -> "OCTB magic is invalid"
  | Version value -> Printf.sprintf "OCTB version = %d expected = 1" value
  | Constant_count value ->
    Printf.sprintf "OCTB constant count = %d maximum = %d" value max_consts
  | Instruction_count value ->
    Printf.sprintf "OCTB instruction count = %Ld maximum = %d"
      value max_instructions
  | Constant_header id ->
    Printf.sprintf "OCTB constant header is incomplete id = %d" id
  | Constant_size (id, maximum) ->
    Printf.sprintf "OCTB constant size exceeds maximum id = %d maximum = %d"
      id maximum
  | Constant_data id ->
    Printf.sprintf "OCTB constant data is incomplete id = %d" id
  | Constant_tag (id, tag) ->
    Printf.sprintf "OCTB constant tag is invalid id = %d tag = %d" id tag
  | Constant_value id ->
    Printf.sprintf "OCTB constant value is invalid id = %d" id
  | Instruction_data pc ->
    Printf.sprintf "OCTB instruction is incomplete pc = %d" pc
  | Constant_ref (pc, id) ->
    Printf.sprintf "OCTB constant reference is invalid pc = %d id = %d" pc id
  | Opcode (pc, tag) ->
    Printf.sprintf "OCTB opcode is outside AML profile pc = %d tag = %d" pc tag
  | Register_ref (pc, reg) ->
    Printf.sprintf "OCTB register is invalid pc = %d reg = %d" pc reg
  | Jump_value (pc, target) ->
    Printf.sprintf "OCTB jump is invalid pc = %d target = %Ld" pc target
  | Jump_ref (pc, target) ->
    Printf.sprintf "OCTB jump is invalid pc = %d target = %d" pc target
  | Jump_mark pc -> Printf.sprintf "OCTB mark differs from pc = %d" pc
  | Trailing_data value -> Printf.sprintf "OCTB trailing bytes = %d" value
  | Empty_code -> "OCTB instruction stream is empty"
  | Result_header -> "OCTB result header is invalid"
  | Emission_invalid -> "OCTB AML emission is invalid"
  | Emission_repeated -> "OCTB AML emission is repeated"
  | Veil_invalid -> "OCTB AML veil is invalid"
  | Veil_repeated -> "OCTB AML veil is repeated"
  | Exact_image -> "OCTB open image differs from exact encoding"

let finish (image : C_mach.t) =
  let* () =
    match C_mach.effects image.code with
    | [] -> Ok ()
    | effects -> Error (Mach (C_mach.Effects effects))
  in
  let* code, raw_map, raw_live, _, regs =
    lower_plan image.inputs image.code image.loc image.span
  in
  let* map =
    match C_smap.make raw_map with
    | Ok value -> Ok value
    | Error error -> Error (Smap error)
  in
  let* live =
    match C_live.make raw_live with
    | Ok value -> Ok value
    | Error error -> Error (Lmap error)
  in
  let veil = wire_veil image.veils image.veil_depth in
  let* octb =
    match image.inputs with
    | [] -> encode_raw ~emission:(wire_emission image.emission) ~veil code
    | inputs ->
      let* raw = encode_open image.emission veil inputs regs image.typ code in
      let expected = result_code image.typ code in
      begin
        match decode raw with
        | Ok decoded
            when Some decoded.code = expected
              && Array.to_list decoded.inputs
                = List.map (fun bind -> bind.C_term.typ) inputs
              && decoded.output = Some image.typ
              && decoded.emission = Some image.emission
              && decoded.veil = Some (image.veils, image.veil_depth) -> Ok raw
        | Ok _ -> Error Output_code
        | Error error -> Error (Output error)
      end
  in
  Ok {
    inputs = image.inputs;
    plan = image.code;
    code;
    octb;
    typ = image.typ;
    result = image.result;
    emission = image.emission;
    veils = image.veils;
    veil_depth = image.veil_depth;
    map;
    live;
  }

let compile source =
  let* image =
    match C_mach.compile source with
    | Ok value -> Ok value
    | Error error -> Error (Mach error)
  in
  finish image

let compile_feed source feed =
  let* image =
    match C_mach.compile_feed source feed with
    | Ok value -> Ok value
    | Error error -> Error (Mach error)
  in
  finish image

let text = function
  | Mach error -> C_mach.text error
  | Stack -> "OCTB stack shape is invalid"
  | Register -> "OCTB register capacity exceeded"
  | Label -> "OCTB control label is invalid"
  | Constants count -> Printf.sprintf "OCTB constant count = %d maximum = 32768" count
  | Map -> "OCTB source position map differs from machine plan"
  | Smap error -> C_smap.text error
  | Slot -> "OCTB linear slot transition is invalid"
  | Lmap error -> C_live.text error
  | Effect_map -> "OCTB effect register map differs from static sites"
  | Output error -> "OCTB output refusal reason = " ^ decode_text error
  | Output_code -> "OCTB output differs after decoding"