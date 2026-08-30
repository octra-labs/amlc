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
  | Join of int * int * int
  | Minus of int * int * int
  | Size of int * int
  | Slice of int * int * int * int
  | Jump of int
  | Jump_if of int * int
  | Mark of int
  | Noop
  | Stop

type t = {
  plan : C_mach.code;
  code : op array;
  octb : string;
  result : C_emit.lit;
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
  | Output of decode_error
  | Output_code

type constant =
  | CInt of string
  | CBool of bool
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
  consts : const_row array;
  cells : code_cell array;
  text_at : int;
  code : op array;
}

type asm =
  | Op of op
  | Goto of int
  | Branch of int * int
  | Place of int

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

let fresh_reg state =
  match state.free with
  | reg :: free -> Ok (reg, { state with free })
  | [] when state.next >= 64 -> Error Register
  | [] -> Ok (state.next, { state with next = state.next + 1 })

let release reg state =
  if reg = 0 then state else { state with free = reg :: state.free }

let rec release_layout value state =
  match value with
  | Unit -> state
  | Atom reg -> release reg state
  | Pair (lhs, rhs) ->
    release_layout lhs (release_layout rhs state)
  | Vec (_, values) -> List.fold_right release_layout values state

let rec layout_regs value out =
  match value with
  | Unit -> out
  | Atom reg -> reg :: out
  | Pair (lhs, rhs) -> layout_regs lhs (layout_regs rhs out)
  | Vec (_, values) -> List.fold_right layout_regs values out

let rec same_layout left right =
  match left, right with
  | Unit, Unit -> true
  | Atom lhs, Atom rhs -> lhs = rhs
  | Pair (ll, lr), Pair (rl, rr) ->
    same_layout ll rl && same_layout lr rr
  | Vec (le, lhs), Vec (re, rhs) ->
    C_mach.same_shape le re && same_layouts lhs rhs
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
  | C_mach.Effect (_, rest), C_mach.LEffect (at, lrest) ->
    let* next = lower env state stack rest lrest in
    Ok { next with seq = cat (one env at (Op Noop)) next.seq }
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
  in
  let rec walk code map live = function
    | [] ->
      Ok (Array.of_list (List.rev code), Array.of_list (List.rev map),
        Array.of_list (List.rev live))
    | value :: rest ->
      let* op = one value.asm in
      walk (op :: code) (value.at :: map) (value.live :: live) rest
  in
  walk [] [] [] values

let lower_plan plan loc at =
  let* out = lower [] { next = 1; free = []; label = 0 } [] plan loc in
  match out.stack, out.env with
  | [Atom result], [] ->
    let suffix =
      if result = 0 then one [] at (Op Stop)
      else cat (one [] at (Op (Move (0, result)))) (one [] at (Op Stop))
    in
    resolve (out.seq (suffix []))
  | [_], _ :: _ -> Error Slot
  | _ -> Error Stack

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

let encode_raw code =
  let _, _, count = pool code in
  if count > 32768 then Error (Constants count)
  else Ok (Bytecode.encode (Array.map vm_op code))

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
        | Ok _ | Error _ -> refuse (Constant_value id)
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
    let code = Array.mapi profile_op native.code in
    let cells =
      Array.map
        (fun (cell : Bytecode.code_cell) ->
          { pc = cell.pc; at = cell.at; size = cell.size })
        native.cells
    in
    verify code;
    Ok { consts; cells; text_at; code }
  with Read_error error -> Error error

let encode code =
  let* raw = encode_raw code in
  match decode raw with
  | Ok image when image.code = code -> Ok raw
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

let finish (image : C_mach.t) =
  let* () =
    match C_mach.effects image.code with
    | [] -> Ok ()
    | effects -> Error (Mach (C_mach.Effects effects))
  in
  let* code, raw_map, raw_live =
    lower_plan image.code image.loc image.span
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
  let* octb = encode code in
  Ok { plan = image.code; code; octb; result = image.result; map; live }

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
  | Output error -> "OCTB output refusal reason = " ^ decode_text error
  | Output_code -> "OCTB output differs after decoding"