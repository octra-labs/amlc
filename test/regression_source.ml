(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

open Regression_support

let trailing = {|
contract First { pure fn value(): int { return 1 } }
contract Second { pure fn value(): int { return 2 } }
|}

let duplicate_function = {|
contract Duplicate {
  pure fn value(): int { return 1 }
  pure fn value(): int { return 2 }
}
|}

let duplicate_parameter = {|
contract Duplicate {
  pure fn value(number: int, number: int): int { return number }
}
|}

let duplicate_state = {|
contract Duplicate {
  state { value: int value: int }
  pure fn read(): int { return 0 }
}
|}

let duplicate_empty_state = {|
contract Duplicate {
  state { }
  state { }
  pure fn read(): int { return 0 }
}
|}

let duplicate_constructor = {|
contract Duplicate {
  constructor() { }
  constructor() { }
  pure fn read(): int { return 0 }
}
|}

let duplicate_event = {|
program Duplicate {
  event Changed(value: int)
  event Changed(value: bool)
  pure fn read(): int { return 0 }
}
|}

let duplicate_error = {|
program Duplicate {
  error Denied(1, "first")
  error Denied(2, "second")
  pure fn read(): int { return 0 }
}
|}

let duplicate_type = {|
program Duplicate {
  struct Item { value: int }
  enum Item { First }
  pure fn read(): int { return 0 }
}
|}

let duplicate_constant = {|
program Duplicate {
  const value: int = 1
  const value: int = 2
  pure fn read(): int { return value }
}
|}

let duplicate_invariant = {|
program Duplicate {
  invariant valid = true
  invariant valid = false
  pure fn read(): int { return 0 }
}
|}

let duplicate_interface = {|
interface Store { fn read(): int }
interface Store { fn write(value: int) }
|}

let duplicate_interface_method = {|
interface Store {
  fn read(): int
  fn read(value: int): int
}
|}

let duplicate_import = {|
import Store from "store.aml"
import Store from "store.aml"
program Main implements Store {
  pure fn read(): int { return 0 }
}
|}

let imported_interface = {|
interface Store { fn read(): int }
|}

let private_namespace = {|
contract PrivateNamespace {
  state { @aml: int }
  pure fn read(): int { return 0 }
}
|}

let wide_refinement = {|
program WideRefinement {
  pure fn value(input: int where input > 1073741824): int { return input }
}
|}

let foreign_refinement = {|
program ForeignRefinement {
  pure fn value(input: int where other > 0): int { return input }
}
|}

let bool_refinement = {|
program BoolRefinement {
  pure fn value(input: bool where input > 0): bool { return input }
}
|}

let wide_error = {|
program WideError {
  error TooWide(1073741824, "outside portable range")
  pure fn value(): int { return 0 }
}
|}

let core_form_position = {|
program Position {
  form broken [] (many value: int) ->[many] int marks {} =
    value + true
  term
    0
}
|}

let core_linearity_position = {|
program Position {
  term
    let many a: int = 1 in
    let once unused: int = 2 in
    a
}
|}

let core_vec_index =
  "program Position { term at[5](vec[int](1,2,3)) }"

let established_program = {|
program Store {
  state { value: string }
  public fn permit(input: string): string { return input }
}
|}

let direct_form = {|
program Direct {
  form add [many left: int] (many right: int) ->[many] int marks {} =
    left + right
  term add(20, 22)
}
|}

let used_form = {|
program Direct {
  form add [many left: int] (many right: int) ->[many] int marks {} =
    left + right
  term use add[20](22) as many value: int in value
}
|}

let let_use = {|
program LetUse {
  form keep [] (once value: int) ->[many] int marks {} = value
  term
    let once item: int = 42 in
    use keep[](item) as many value: int in
    value
}
|}

let let_use_twice = {|
program LetUseTwice {
  form keep [] (once value: int) ->[many] int marks {} = value
  term
    let once item: int = 21 in
    use keep[](item) as many value: int in
    item + value
}
|}

let nested_form = {|
program Direct {
  form add [many left: int] (many right: int) ->[many] int marks {} =
    left + right
  form triple [] (many value: int) ->[many] int marks {} =
    add(value, value) + value
  term triple(7)
}
|}

let order = {|
program Order {
  term
    if -3 < -2 then
      if -2 <= -2 then
        if 5 > 4 then
          if 5 >= 5 then 42 else 4
        else 3
      else 2
    else 1
}
|}

let order_edges = {|
program OrderEdges {
  term
    if 3 < 3 then 1 else
    if 3 <= 3 then
      if 2 > 3 then 2 else
      if 2 >= 3 then 3 else
      if 1 + 2 < 2 * 2 then 42 else 4
    else 5
}
|}

let order_type = "program BadOrder { term true < 5 }"
let order_chain = "program Chain { term 1 < 2 < 3 }"

let order_auto = "program AutoOrder { term 3 < 5 }"

let order_explicit = {|
program ExplicitOrder {
  term
    let many left: int = 3 in
    let many right: int = 5 in
    let many delta: int = right - left in
    if equal[int](left, right) then false
    else equal[int](abs(delta), delta)
}
|}

let order_left = {|
program LeftOrder {
  input once n: int
  term n < 5
}
|}

let order_right = {|
program RightOrder {
  input once n: int
  term 5 > n
}
|}

let order_form = {|
program FormOrder {
  form less [] (many left: int) ->[many] int marks {} =
    if left < 5 then 42 else 0
  term less(3)
}
|}

let finite_orbit = {|
program FiniteOrbit {
  input once n: int
  term orbit[64, n] from 0 with many state: int => state + 1
}
|}

let finite_orbit_huge = {|
program Huge {
  term orbit[1000000, 1] from 0 with many state: int => state + 1
}
|}

let finite_orbit_order = {|
program FiniteOrder {
  input once n: int
  term orbit[8, n] from 0 with many state: int =>
    if state < 3 then state + 1 else state
}
|}

let finite_orbit_zero = {|
program FiniteZero {
  input once n: int
  term orbit[0, n] from 7 with erase state: int => 8
}
|}

let finite_orbit_type = {|
program FiniteType {
  term orbit[4, true] from 0 with many state: int => state + 1
}
|}

let finite_orbit_body = {|
program FiniteBody {
  term orbit[0, 1] from 0 with erase state: int => true
}
|}

let orbit_seed_type = {|
program OrbitSeedType {
  term orbit[0] from true with erase state: int => 0
}
|}

let finite_orbit_seed_type = {|
program FiniteSeedType {
  term orbit[0, 1] from true with erase state: int => 0
}
|}

let order_matrix () =
  let values = List.init 33 (fun index -> index - 16) in
  let relations = [
    "<", (fun left right -> left < right);
    "<=", (fun left right -> left <= right);
    ">", (fun left right -> left > right);
    ">=", (fun left right -> left >= right);
  ] in
  List.iter
    (fun (symbol, decide) ->
      List.iter
        (fun left ->
          List.iter
            (fun right ->
              let source = Printf.sprintf
                "program Matrix { term %d %s %d }" left symbol right in
              core_result "order matrix"
                (Octra_vm.C_emit.Bool (decide left right)) source)
            values)
        values)
    relations

let order_limit () =
  let values = String.concat ", " (List.init 34000 (fun _ -> "0 < 1")) in
  let source = "program OrderLimit { term vec[bool](" ^ values ^ ") }" in
  core_refuse "order source limit" "token count limit = 100000" source;
  let item = Octra_vm.C_raw.Cmp (Octra_vm.C_syn.Lt,
    Octra_vm.C_raw.KInt Z.zero, Octra_vm.C_raw.KInt Z.one) in
  let term = Octra_vm.C_raw.KVec (Octra_vm.C_decl.Exact Octra_vm.C_syn.TBool,
    List.init 34000 (fun _ -> item)) in
  match Octra_vm.C_raw.elab Octra_vm.C_idx.empty term with
  | Error error ->
      let reason = Octra_vm.C_raw.text error in
      if not (includes reason "raw term nodes limit = 100000") then
        fail "order raw limit" ("unexpected reason = " ^ reason)
  | Ok _ -> fail "order raw limit" "raw term accepted"

let reuse_regs () =
  let expr = String.concat " + " (List.init 80 (fun _ -> "1")) in
  let source = "program Reuse { term " ^ expr ^ " }" in
  core_result "register reuse" (Octra_vm.C_emit.Int (Z.of_int 80)) source

let linear_form = {|
program Direct {
  form consume [] (once value: int) ->[many] int marks {} = value
  term consume(7)
}
|}

let effect_form = {|
program Direct {
  form touch [] (many value: int) ->[many] int marks {write[1]} =
    write[1](value)
  term touch(7)
}
|}

let short_call = {|
program Direct {
  form add [many left: int] (many right: int) ->[many] int marks {} =
    left + right
  term add(1)
}
|}

let wrong_call_type = {|
program Direct {
  form add [many left: int] (many right: int) ->[many] int marks {} =
    left + right
  term add(true, 1)
}
|}

let forward_call = {|
program Direct {
  form first [] (many value: int) ->[many] int marks {} = second(value)
  form second [] (many value: int) ->[many] int marks {} = value + 1
  term first(1)
}
|}

let veil = {|
program Veil {
  size d = 2
  veil Budget key[1] depth[d] under {
    add[1], mul[7], renew[20]
  } {
    param[10] room[1]
    param[20] room[2]
    input x: enc[1,d]
    input y: enc[1,d]
    term renew((x * y) * trim[1](x))
  }
  term 0
}
|}

let plain = "program Plain { term 0 }"

let nul_string =
  "program Nul { public view fn value(): string { return \"x"
  ^ String.make 1 '\000'
  ^ "y\" } }"

let mixed_program limit =
  {|
program Compose {
  state { balance: int }
  private pure fn bump(value: int): int {
    return value + 1
  }
  form total [many base: int] (many value: int) ->[many] int marks {}|}
  ^ limit
  ^ {|
    =
    bump(base) + value
  public fn add(value: int): int {
    self.balance += total(value, value)
    return self.balance
  }
  public view fn read(): int { return self.balance }
}
|}

let mixed =
  mixed_program " under {steps[1000], depth[1000], work[1000]}"

let mixed_plain = mixed_program ""

let mixed_under =
  mixed_program " under {steps[0], depth[0], work[0]}"

let mixed_public = {|
program PublicPure {
  public pure fn bump(value: int): int { return value + 1 }
  form total [] (many value: int) ->[many] int marks {} = bump(value)
  public pure fn run(value: int): int { return total(value) }
}
|}

let mixed_payable = {|
program PayablePure {
  public pure fn bump(value: int): int { return value + 1 }
  form total [] (many value: int) ->[many] int marks {} = bump(value)
  public payable fn pay(value: int): int { return total(value) }
}
|}

let mixed_nested = {|
program Nested {
  form add [many left: int] (many right: int) ->[many] int marks {} =
    left + right
  form twice [] (many value: int) ->[many] int marks {} =
    add(value, value)
  public pure fn run(value: int): int { return twice(value) }
}
|}

let mixed_shadow = {|
program Shadow {
  form abs [] (many value: int) ->[many] int marks {} = value + 10
  public pure fn run(value: int): int { return abs(value) }
}
|}

let mixed_once = {|
program Once {
  form take [] (once value: int) ->[many] int marks {} = value
  public pure fn run(value: int): int { return take(value) }
}
|}

let mixed_once_use = {|
program OnceUse {
  state { total: int }
  form take [] (once value: int) ->[many] int marks {} = value
  public fn run(value: int): int {
    self.total = value
    return use take[](value) as many out: int in out
  }
}
|}

let mixed_once_use_twice = {|
program OnceUseTwice {
  form take [] (once value: int) ->[many] int marks {} = value
  public fn run(value: int): int {
    return use take[](value) as once out: int in out + out
  }
}
|}

let mixed_once_use_type = {|
program OnceUseType {
  form take [] (once value: int) ->[many] int marks {} = value
  public fn run(value: int): int {
    return use take[](value) as many out: bool in value
  }
}
|}

let mixed_once_use_local = {|
program OnceUseLocal {
  form take [] (once value: int) ->[many] int marks {} = value
  public fn run(value: int): int {
    let local = value
    return use take[](local) as many out: int in out
  }
}
|}

let mixed_once_use_state_local = {|
program OnceUseStateLocal {
  state { total: int }
  form take [] (once value: int) ->[many] int marks {} = value
  public fn run(): int {
    let local = self.total
    return use take[](local) as many out: int in out
  }
}
|}

let mixed_once_use_capture = {|
program OnceUseCapture {
  form add [once left: int] (once right: int) ->[once] int marks {} =
    left + right
  public fn run(left: int, right: int): int {
    return use add[left](right) as once out: int in out
  }
}
|}

let mixed_direct_call = {|
program DirectUse {
  form add [many left: int] (many right: int) ->[many] int marks {} =
    left + right
  public pure fn run(left: int, right: int): int { return add(left, right) }
}
|}

let mixed_direct_use = {|
program DirectUse {
  form add [many left: int] (many right: int) ->[many] int marks {} =
    left + right
  public pure fn run(left: int, right: int): int {
    return use add[left](right) as many out: int in out
  }
}
|}

let mixed_use_name = {|
program UseName {
  private pure fn use(value: int): int { return value + 1 }
  public pure fn run(value: int): int {
    let use = value
    return use(use)
  }
}
|}

let mixed_once_use_ctor = {|
program OnceUseCtor {
  state { total: int }
  form take [] (once value: int) ->[many] int marks {} = value
  constructor(value: int) {
    self.total = use take[](value) as once out: int in out + out
  }
  public view fn read(): int { return self.total }
}
|}

let mixed_once_use_ctor_ok = {|
program OnceUseCtorOk {
  state { total: int }
  form take [] (once value: int) ->[many] int marks {} = value
  constructor(value: int) {
    self.total = use take[](value) as many out: int in out
  }
  public view fn read(): int { return self.total }
}
|}

let mixed_once_use_const = {|
program OnceUseConst {
  form take [] (once value: int) ->[many] int marks {} = value
  const total: int = use take[](1) as once out: int in out + out
  public pure fn read(): int { return total }
}
|}

let mixed_once_use_const_ok = {|
program OnceUseConstOk {
  form take [] (once value: int) ->[many] int marks {} = value
  const total: int = use take[](1) as once out: int in out
  public pure fn read(): int { return total }
}
|}

let mixed_marks = {|
program Marks {
  state { total: int }
  form touch [] (many value: int) ->[many] int marks {read[1]:total} = value
  public pure fn run(value: int): int { return touch(value) }
}
|}

let emit_form = {|
program EmitForm {
  event Value(value: int)
  form note [] (many value: int) ->[many] int marks {emit[7]:Value} =
    emit[7](value + 1)
  public fn run(value: int): int {
    return use note[](value) as many out: int in out
  }
}
|}

let emit_pure = {|
program EmitPure {
  event Value(value: int)
  form note [] (many value: int) ->[many] int marks {emit[7]:Value} =
    emit[7](value + 1)
  public pure fn run(value: int): int {
    return use note[](value) as many out: int in out
  }
}
|}

let emit_direct = {|
program EmitDirect {
  event Value(value: int)
  form note [] (many value: int) ->[many] int marks {emit[7]:Value} =
    emit[7](value + 1)
  public fn run(value: int): int { return note(value) }
}
|}

let emit_absent = {|
program EmitAbsent {
  event Value(value: int)
  form note [] (many value: int) ->[many] int marks {emit[7]:Missing} =
    emit[7](value + 1)
  public fn run(value: int): int {
    return use note[](value) as many out: int in out
  }
}
|}

let emit_type = {|
program EmitType {
  event Value(value: bool)
  form note [] (many value: int) ->[many] int marks {emit[7]:Value} =
    emit[7](value + 1)
  public fn run(value: int): int {
    return use note[](value) as many out: int in out
  }
}
|}

let emit_unproved = {|
program EmitUnproved {
  event Value(value: int)
  form note [] (many value: int) ->[many] int marks {emit[8]:Value} =
    emit[7](value + 1)
  public fn run(value: int): int {
    return use note[](value) as many out: int in out
  }
}
|}

let emit_repeated = {|
program EmitRepeated {
  event Value(value: int)
  form note [] (many value: int) ->[many] int
    marks {emit[7]:Value, emit[7]:Value} = emit[7](value)
  public fn run(value: int): int {
    return use note[](value) as many out: int in out
  }
}
|}

let emit_outside = {|
program EmitOutside {
  event Value(value: int)
  public fn run(value: int): int { return emit[7](value) }
}
|}

let emit_bool = {|
program EmitBool {
  event Truth(value: bool)
  form flip [] (many value: bool) ->[many] bool marks {emit[9]:Truth} =
    emit[9](!value)
  public fn run(value: bool): bool {
    return use flip[](value) as many out: bool in out
  }
}
|}

let emit_once = {|
program EmitOnce {
  event Value(value: int)
  form note [] (once value: int) ->[many] int marks {emit[7]:Value} =
    emit[7](value)
  public fn run(value: int): int {
    return use note[](value) as many out: int in out
  }
}
|}

let emit_nested = {|
program EmitNested {
  event Value(value: int)
  form inner [] (many value: int) ->[many] int marks {emit[7]:Value} =
    emit[7](value + 1)
  form outer [] (many value: int) ->[many] int marks {emit[7]:Value} =
    use inner[](value) as many out: int in out + 1
  public fn run(value: int): int {
    return use outer[](value) as many out: int in out
  }
}
|}

let write_int = {|
program WriteInt {
  state { total: int }
  form put [] (many value: int) ->[many] int marks {write[7]:total} =
    write[7](value)
  public fn set(value: int): int {
    return use put[](value) as many out: int in out
  }
  public view fn read(): int { return self.total }
}
|}

let write_bool = {|
program WriteBool {
  state { enabled: bool }
  form put [] (many value: bool) ->[many] bool marks {write[8]:enabled} =
    write[8](!value)
  public fn set(value: bool): bool {
    return use put[](value) as many out: bool in out
  }
  public view fn read(): bool { return self.enabled }
}
|}

let write_bridge = {|
program WriteBridge {
  state { total: int }
  form add [many left: int] (many right: int) ->[many] int marks {} =
    left + right
  form put [] (many value: int) ->[many] int marks {write[7]:total} =
    write[7](value)
  public fn bump(delta: int): int {
    let prior = self.total
    let next = add(prior, delta)
    return use put[](next) as many out: int in out
  }
  public view fn read(): int { return self.total }
}
|}

let write_rollback = {|
program WriteRollback {
  state { total: int }
  form put [] (many value: int) ->[many] int marks {write[7]:total} =
    write[7](value)
  public fn trial(value: int): int {
    checkpoint()
    let saved = use put[](value) as many out: int in out
    rollback()
    return self.total
  }
}
|}

let write_pure = {|
program WritePure {
  state { total: int }
  form put [] (many value: int) ->[many] int marks {write[7]:total} =
    write[7](value)
  public pure fn set(value: int): int {
    return use put[](value) as many out: int in out
  }
}
|}

let write_pure_helper = {|
program WritePureHelper {
  state { total: int }
  form put [] (many value: int) ->[many] int marks {write[7]:total} =
    write[7](value)
  private fn apply(value: int): int {
    return use put[](value) as many out: int in out
  }
  public pure fn set(value: int): int { return apply(value) }
}
|}

let write_view = {|
program WriteView {
  state { total: int }
  form put [] (many value: int) ->[many] int marks {write[7]:total} =
    write[7](value)
  public view fn set(value: int): int {
    return use put[](value) as many out: int in out
  }
}
|}

let write_view_helper = {|
program WriteViewHelper {
  state { total: int }
  form put [] (many value: int) ->[many] int marks {write[7]:total} =
    write[7](value)
  private fn apply(value: int): int {
    return use put[](value) as many out: int in out
  }
  public view fn set(value: int): int { return apply(value) }
}
|}

let write_direct = {|
program WriteDirect {
  state { total: int }
  form put [] (many value: int) ->[many] int marks {write[7]:total} =
    write[7](value)
  public fn set(value: int): int { return put(value) }
}
|}

let write_absent = {|
program WriteAbsent {
  state { total: int }
  form put [] (many value: int) ->[many] int marks {write[7]:missing} =
    write[7](value)
  public fn set(value: int): int {
    return use put[](value) as many out: int in out
  }
}
|}

let write_type = {|
program WriteType {
  state { enabled: bool }
  form put [] (many value: int) ->[many] int marks {write[7]:enabled} =
    write[7](value)
  public fn set(value: int): int {
    return use put[](value) as many out: int in out
  }
}
|}

let write_unproved = {|
program WriteUnproved {
  state { total: int }
  form put [] (many value: int) ->[many] int marks {write[8]:total} =
    write[7](value)
  public fn set(value: int): int {
    return use put[](value) as many out: int in out
  }
}
|}

let write_repeated = {|
program WriteRepeated {
  state { total: int }
  form put [] (many value: int) ->[many] int
    marks {write[7]:total, write[7]:total} = write[7](value)
  public fn set(value: int): int {
    return use put[](value) as many out: int in out
  }
}
|}

let write_outside = {|
program WriteOutside {
  state { total: int }
  public fn set(value: int): int { return write[7](value) }
}
|}

let write_const = {|
program WriteConst {
  state { total: int }
  form put [] (many value: int) ->[many] int marks {write[7]:total} =
    write[7](value)
  const seed: int = use put[](1) as many out: int in out
  public view fn read(): int { return seed }
}
|}

let write_invariant = {|
program WriteInvariant {
  state { total: int }
  form put [] (many value: int) ->[many] int marks {write[7]:total} =
    write[7](value)
  invariant valid = use put[](1) as many out: int in out > 0
  public view fn read(): int { return self.total }
}
|}

let write_name = {|
program WriteName {
  private pure fn write(value: int): int { return value + 1 }
  public pure fn run(value: int): int {
    let write = value
    return write(write)
  }
}
|}

let mixed_effect = {|
program Effect {
  private fn bump(value: int): int { return value + 1 }
  form total [] (many value: int) ->[many] int marks {} = bump(value)
  public pure fn run(value: int): int { return total(value) }
}
|}

let mixed_state = {|
program StateRead {
  state { total: int }
  private pure fn add(value: int): int { return self.total + value }
  form read [] (many value: int) ->[many] int marks {} = add(value)
  public pure fn run(value: int): int { return read(value) }
}
|}

let mixed_nested_fn = {|
program NestedFn {
  private pure fn first(value: int): int { return value + 1 }
  private pure fn second(value: int): int { return first(value) }
  form total [] (many value: int) ->[many] int marks {} = second(value)
  public pure fn run(value: int): int { return total(value) }
}
|}

let mixed_flow = {|
program Flow {
  private pure fn choose(value: int): int {
    let next: int = value + 1
    if next > 5 { return next } else { return 5 }
  }
  form total [] (many value: int) ->[many] int marks {} = choose(value)
  public pure fn run(value: int): int { return total(value) }
}
|}

let mixed_zero = {|
program ZeroArg {
  private pure fn base(): int { return 7 }
  form total [] (many value: int) ->[many] int marks {} = base() + value
  public pure fn run(value: int): int { return total(value) }
}
|}

let mixed_guard = {|
program GuardClause {
  private pure fn magnitude(value: int): int {
    if value < 0 { return -value }
    return value
  }
  form total [] (many value: int) ->[many] int marks {} = magnitude(value)
  public pure fn run(value: int): int { return total(value) }
}
|}

let mixed_pure_view = {|
program PureView {
  private pure view fn increase(value: int): int { return value + 1 }
  form total [] (many value: int) ->[many] int marks {} = increase(value)
  public pure fn run(value: int): int { return total(value) }
}
|}

let mixed_view = {|
program ViewOnly {
  private view fn increase(value: int): int { return value + 1 }
  form total [] (many value: int) ->[many] int marks {} = increase(value)
  public pure fn run(value: int): int { return total(value) }
}
|}

let mixed_collision = {|
program Collision {
  state { total: int }
  private pure fn commit(): bool { return false }
  private pure fn helper(): bool { return commit() }
  form check [] (many value: int) ->[many] bool marks {} = helper()
  public fn run(value: int): bool {
    checkpoint()
    self.total = value
    let result = check(value)
    rollback()
    return result
  }
}
|}

let mixed_open_guard = {|
program OpenGuard {
  private pure fn choose(value: int): int {
    if value < 0 { let positive = -value }
    return value
  }
  form total [] (many value: int) ->[many] int marks {} = choose(value)
  public pure fn run(value: int): int { return total(value) }
}
|}

let mixed_bytes = {|
program FixedBytes {
  private pure fn keep(value: bytes32): bytes32 { return value }
  form pass [] (many value: bytes32) ->[many] bytes32 marks {} = keep(value)
  form same [many left: bytes32] (many right: bytes32)
    ->[many] bool marks {} = left == right
  public pure fn echo(value: bytes32): bytes32 { return pass(value) }
  public pure fn equal(left: bytes32, right: bytes32): bool {
    return same(left, right)
  }
}
|}

let mixed_mutation = {|
program Mutation {
  private pure fn change(value: int): int {
    let next = value
    next += 1
    return next
  }
  form total [] (many value: int) ->[many] int marks {} = change(value)
  public pure fn run(value: int): int { return total(value) }
}
|}

let mixed_recursion = {|
program Recursion {
  form loop [] (many value: int) ->[many] int marks {} = loop(value)
  public pure fn run(value: int): int { return loop(value) }
}
|}

let mixed_type = {|
program TypeError {
  form add [] (many value: int) ->[many] int marks {} = value + true
  public pure fn run(value: int): int { return add(value) }
}
|}

let mixed_duplicate = {|
program Duplicate {
  private pure fn same(value: int): int { return value }
  form same [] (many value: int) ->[many] int marks {} = value
  public pure fn run(value: int): int { return same(value) }
}
|}

let legacy_form = {|
contract Mixed {
  form same [] (many value: int) ->[many] int marks {} = value
  public pure fn run(value: int): int { return same(value) }
}
|}

let mixed_limits () =
  let leaf = String.concat " + " (List.init 100 (fun _ -> "value")) in
  let calls count =
    String.concat " + " (List.init count (fun _ -> "leaf(value)"))
  in
  let expanded =
    "program Expanded { form leaf [] (many value: int) ->[many] int marks {} = "
    ^ leaf
    ^ " form total [] (many value: int) ->[many] int marks {} = "
    ^ calls 600
    ^ " public pure fn run(value: int): int { return total(value) } }"
  in
  refuse "mixed node limit" "direct form node limit = 100000" expanded;
  let used =
    "program UseLimit { form leaf [] (many value: int) ->[many] int marks {} = "
    ^ leaf
    ^ " form first [] (many value: int) ->[many] int marks {} = "
    ^ calls 300
    ^ " form second [] (many value: int) ->[many] int marks {} = "
    ^ calls 250
    ^ " public pure fn run(value: int): int { return use first[](value) "
    ^ "as many out: int in second(out) } }"
  in
  refuse "mixed use node limit" "direct form node limit = 100000" used;
  let forms =
    List.init 257 (fun index ->
      Printf.sprintf
        "form f%d [] (many value: int) ->[many] int marks {} = value"
        index)
    |> String.concat " "
  in
  refuse "mixed function limit" "program function count exceeds capacity"
    ("program FunctionLimit { " ^ forms ^ " }");
  let chain count =
    let forms =
      List.init count (fun index ->
        let body =
          if index + 1 = count then "value"
          else Printf.sprintf "f%d(value)" (index + 1)
        in
        Printf.sprintf
          "form f%d [] (many value: int) ->[many] int marks {} = %s"
          index body)
      |> String.concat " "
    in
    "program Depth { " ^ forms
    ^ " public pure fn run(value: int): int { return f0(value) } }"
  in
  execute_octb ~args:[VM.VInt (Z.of_int 7)] "mixed depth edge" "run"
    (chain 8)
  |> result "mixed depth edge" "int:7";
  refuse "mixed depth limit"
    "direct form call depth max = 8 actual = 9" (chain 9);
  let cached count =
    let forms =
      List.init count (fun index ->
        let body =
          if index + 1 = count then "value"
          else Printf.sprintf "f%d(value)" (index + 1)
        in
        Printf.sprintf
          "form f%d [] (many value: int) ->[many] int marks {} = %s"
          index body)
      |> List.rev
      |> String.concat " "
    in
    "program CachedDepth { " ^ forms
    ^ " public pure fn run(value: int): int { return f0(value) } }"
  in
  execute_octb ~args:[VM.VInt (Z.of_int 7)]
    "mixed cached depth edge" "run" (cached 8)
  |> result "mixed cached depth edge" "int:7";
  refuse "mixed cached depth"
    "direct form call depth max = 8 actual = 9" (cached 9);
  let wrapped count =
    let forms =
      List.init count (fun index ->
        let body =
          if index + 1 = count then "value"
          else Printf.sprintf "f%d(value)" (index + 1)
        in
        Printf.sprintf
          "form f%d [] (many value: int) ->[many] int marks {} = %s"
          index body)
      |> String.concat " "
    in
    "program WrappedDepth { " ^ forms
    ^ " private pure fn wrap(value: int): int { return f0(value) }"
    ^ " public pure fn run(value: int): int { return wrap(value) } }"
  in
  execute_octb ~args:[VM.VInt (Z.of_int 7)]
    "mixed wrapped depth edge" "run" (wrapped 7)
  |> result "mixed wrapped depth edge" "int:7";
  refuse "mixed wrapped depth limit"
    "direct form call depth max = 8 actual = 9" (wrapped 8);
  let fillers =
    List.init 100 (fun index ->
      Printf.sprintf
        "private pure fn spare%d(value: int): int { return value }" index)
    |> String.concat " "
  in
  let labels =
    "program LabelSpace { public pure fn bump(value: int): int { return value + 1 }"
    ^ " form total [] (many value: int) ->[many] int marks {} = bump(value)"
    ^ " public payable fn pay(value: int): int { return total(value) } "
    ^ fillers ^ " }"
  in
  execute_octb ~args:[VM.VInt (Z.of_int 5)] ~value:Z.one
    "mixed label space" "pay" labels
  |> result "mixed label space" "int:6"

let mixed_matrix () =
  let cases = [
    "3 + 5", "int", Octra_vm.C_emit.Int (Z.of_int 8), "int:8";
    "8 - 3", "int", Octra_vm.C_emit.Int (Z.of_int 5), "int:5";
    "3 * 5", "int", Octra_vm.C_emit.Int (Z.of_int 15), "int:15";
    "8 / 3", "int", Octra_vm.C_emit.Int (Z.of_int 2), "int:2";
    "8 % 3", "int", Octra_vm.C_emit.Int (Z.of_int 2), "int:2";
    "-7", "int", Octra_vm.C_emit.Int (Z.of_int (-7)), "int:-7";
    "abs(-7)", "int", Octra_vm.C_emit.Int (Z.of_int 7), "int:7";
    "3 < 5", "bool", Octra_vm.C_emit.Bool true, "bool:true";
    "5 <= 5", "bool", Octra_vm.C_emit.Bool true, "bool:true";
    "3 > 5", "bool", Octra_vm.C_emit.Bool false, "bool:false";
    "5 >= 5", "bool", Octra_vm.C_emit.Bool true, "bool:true";
  ] in
  List.iteri
    (fun index (expression, typ, expected, result_text) ->
      let core = "program Core { term " ^ expression ^ " }" in
      let mixed =
        "program Matrix { form calc [] (many value: int) ->[many] "
        ^ typ
        ^ " marks {} = "
        ^ expression
        ^ " public pure fn run(value: int): "
        ^ typ
        ^ " { return calc(value) } }"
      in
      let name = "mixed matrix " ^ string_of_int index in
      core_result name expected core;
      execute ~args:[VM.VInt Z.zero] name "run" mixed
      |> result name result_text)
    cases

let core_out name source args =
  let artifact =
    match Octra_vm.C_octb.compile source with
    | Ok value -> value
    | Error error ->
      fail name ("core compile reason = " ^ Octra_vm.C_octb.text error)
  in
  let image =
    match Octra_vm.Bytecode.decode_image artifact.octb with
    | Ok value -> value
    | Error reason -> fail name ("core decode reason = " ^ reason)
  in
  let config =
    Local.config ~view:true ~byte_result:VM.Bytes_result
      ~method_name:"main" ~args ()
  in
  match Local.run ~trace:false config image.code with
  | Ok value -> value
  | Error error -> fail name ("core run reason = " ^ Local.error_text error)

let compare_mixed name core mixed arg =
  let left = core_out name core [arg] in
  let right = attempt ~args:[arg] name "run" mixed in
  let detached = attempt_octb ~args:[arg] name "run" mixed in
  if left.stop <> right.stop then fail name "stop differs";
  if left.result <> right.result then fail name "result differs";
  if right.stop <> detached.stop then fail name "detached stop differs";
  if right.result <> detached.result then fail name "detached result differs";
  if right.effort <> detached.effort || right.steps <> detached.steps then
    fail name "detached cost differs";
  if right.storage <> detached.storage || right.events <> detached.events then
    fail name "detached effects differ"

let mixed_pair name arg_typ ret_typ core_expr mixed_expr arg =
  let core =
    "program Core { input many value: " ^ arg_typ ^ " term " ^ core_expr
    ^ " }"
  in
  let mixed =
    "program Mixed { form calc [] (many value: " ^ arg_typ
    ^ ") ->[many] " ^ ret_typ ^ " marks {} = " ^ mixed_expr
    ^ " public pure fn run(value: " ^ arg_typ ^ "): " ^ ret_typ
    ^ " { return calc(value) } }"
  in
  compare_mixed name core mixed arg

type generated = {
  core : string;
  mixed : string;
}

let draw seed cap =
  let next =
    Int64.add (Int64.mul seed 6364136223846793005L) 1442695040888963407L
  in
  next, Int64.to_int (Int64.logand next 0x7fffffffL) mod cap

let binary symbol left right = {
  core = "(" ^ left.core ^ " " ^ symbol ^ " " ^ right.core ^ ")";
  mixed = "(" ^ left.mixed ^ " " ^ symbol ^ " " ^ right.mixed ^ ")";
}

let rec generated_int seed depth =
  let seed, choice = draw seed (if depth = 0 then 3 else 8) in
  if depth = 0 then
    match choice with
    | 0 -> seed, { core = "value"; mixed = "value" }
    | 1 ->
      let seed, value = draw seed 19 in
      let text = string_of_int (value - 9) in
      seed, { core = text; mixed = text }
    | _ -> seed, { core = "-3"; mixed = "-3" }
  else
    match choice with
    | 0 | 1 | 2 as op ->
      let seed, left = generated_int seed (depth - 1) in
      let seed, right = generated_int seed (depth - 1) in
      let symbol = if op = 0 then "+" else if op = 1 then "-" else "*" in
      seed, binary symbol left right
    | 3 ->
      let seed, value = generated_int seed (depth - 1) in
      seed, {
        core = "(-" ^ value.core ^ ")";
        mixed = "(-" ^ value.mixed ^ ")";
      }
    | 4 ->
      let seed, value = generated_int seed (depth - 1) in
      seed, {
        core = "abs(" ^ value.core ^ ")";
        mixed = "abs(" ^ value.mixed ^ ")";
      }
    | 5 ->
      let seed, value = generated_int seed (depth - 1) in
      let seed, divisor = draw seed 9 in
      let divisor = string_of_int (divisor + 1) in
      seed, binary "/" value { core = divisor; mixed = divisor }
    | 6 ->
      let seed, value = generated_int seed (depth - 1) in
      let seed, divisor = draw seed 9 in
      let divisor = string_of_int (divisor + 1) in
      seed, binary "%" value { core = divisor; mixed = divisor }
    | _ ->
      let seed, guard = generated_bool seed (depth - 1) in
      let seed, yes = generated_int seed (depth - 1) in
      let seed, no = generated_int seed (depth - 1) in
      seed, {
        core = "(if " ^ guard.core ^ " then " ^ yes.core ^ " else "
          ^ no.core ^ ")";
        mixed = "(" ^ guard.mixed ^ " ? " ^ yes.mixed ^ " : "
          ^ no.mixed ^ ")";
      }

and generated_bool seed depth =
  let seed, choice = draw seed (if depth = 0 then 2 else 8) in
  if depth = 0 then
    if choice = 0 then seed, { core = "true"; mixed = "true" }
    else seed, { core = "false"; mixed = "false" }
  else
    match choice with
    | 0 | 1 | 2 | 3 as op ->
      let seed, left = generated_int seed (depth - 1) in
      let seed, right = generated_int seed (depth - 1) in
      let symbol =
        if op = 0 then "<" else if op = 1 then "<="
        else if op = 2 then ">" else ">="
      in
      seed, binary symbol left right
    | 4 ->
      let seed, left = generated_int seed (depth - 1) in
      let seed, right = generated_int seed (depth - 1) in
      seed, {
        core = "equal[int](" ^ left.core ^ "," ^ right.core ^ ")";
        mixed = "(" ^ left.mixed ^ " == " ^ right.mixed ^ ")";
      }
    | 5 ->
      let seed, value = generated_bool seed (depth - 1) in
      seed, {
        core = "equal[bool](" ^ value.core ^ ",false)";
        mixed = "(!" ^ value.mixed ^ ")";
      }
    | 6 ->
      let seed, left = generated_bool seed (depth - 1) in
      let seed, right = generated_bool seed (depth - 1) in
      seed, {
        core = "(if " ^ left.core ^ " then " ^ right.core ^ " else false)";
        mixed = "(" ^ left.mixed ^ " && " ^ right.mixed ^ ")";
      }
    | _ ->
      let seed, left = generated_bool seed (depth - 1) in
      let seed, right = generated_bool seed (depth - 1) in
      seed, {
        core = "(if " ^ left.core ^ " then true else " ^ right.core ^ ")";
        mixed = "(" ^ left.mixed ^ " || " ^ right.mixed ^ ")";
      }

let mixed_generated () =
  let rec run index seed =
    if index = 256 then ()
    else
      let seed, kind = draw seed 2 in
      let seed, expression =
        if kind = 0 then generated_int seed 3 else generated_bool seed 3
      in
      let typ = if kind = 0 then "int" else "bool" in
      let seed, raw = draw seed 65 in
      let arg = VM.VInt (Z.of_int (raw - 32)) in
      let core =
        "program Core { input many value: int term " ^ expression.core ^ " }"
      in
      let mixed =
        "program Generated { private pure fn helper(value: int): " ^ typ
        ^ " { return " ^ expression.mixed
        ^ " } form calc [] (many value: int) ->[many] " ^ typ
        ^ " marks {} = helper(value) public pure fn run(value: int): " ^ typ
        ^ " { return calc(value) } }"
      in
      compare_mixed ("mixed generated " ^ string_of_int index) core mixed arg;
      run (index + 1) seed
  in
  run 0 0x5a17c3e29b4d681fL

let mixed_runtime_matrix () =
  let int_cases = [
    "value + 5", "value + 5", "int";
    "value - 5", "value - 5", "int";
    "value * -3", "value * -3", "int";
    "value / 3", "value / 3", "int";
    "value / -3", "value / -3", "int";
    "value % 3", "value % 3", "int";
    "value % -3", "value % -3", "int";
    "-value", "-value", "int";
    "abs(value)", "abs(value)", "int";
    "value < -2", "value < -2", "bool";
    "value <= -2", "value <= -2", "bool";
    "value > -2", "value > -2", "bool";
    "value >= -2", "value >= -2", "bool";
    "equal[int](value, -2)", "value == -2", "bool";
    "equal[bool](equal[int](value, -2), false)", "value != -2", "bool";
    "if value < 0 then -value else value",
      "value < 0 ? -value : value", "int";
  ] in
  let wide = Z.shift_left Z.one 256 in
  let values =
    List.map Z.of_int [-9; -4; -1; 0; 1; 4; 9]
    @ [wide; Z.neg wide]
  in
  List.iteri
    (fun index (core, mixed, typ) ->
      List.iter
        (fun value ->
          let name =
            "mixed runtime int " ^ string_of_int index ^ " "
            ^ Z.to_string value
          in
          mixed_pair name "int" typ core mixed (VM.VInt value))
        values)
    int_cases;
  mixed_pair "mixed runtime bool true" "bool" "bool"
    "if value then false else true" "!value" (VM.VBool true);
  mixed_pair "mixed runtime bool false" "bool" "bool"
    "equal[bool](value, false)" "value == false" (VM.VBool false);
  mixed_pair "mixed runtime and" "int" "bool"
    "if false then equal[int](1 / 0, 0) else false"
    "false && (1 / 0 == 0)" (VM.VInt Z.zero);
  mixed_pair "mixed runtime or" "int" "bool"
    "if true then true else equal[int](1 / 0, 0)"
    "true || (1 / 0 == 0)" (VM.VInt Z.zero);
  mixed_pair "mixed runtime divide zero" "int" "int"
    "value / 0" "value / 0" (VM.VInt Z.one)

let mixed_checks () =
  if Amlc_cli.source_form_raw mixed <> Amlc_cli.Contract_source then
    fail "mixed source" "program not recognized";
  let compiled = compile "mixed compile" mixed in
  let plain = compile "mixed plain" mixed_plain in
  if not (String.equal compiled.octb plain.octb) then
    fail "mixed guarantee" "OCTB differs";
  begin
    match Octra_vm.Bytecode.decode_image compiled.octb with
    | Ok { proof = None; _ } -> ()
    | Ok _ | Error _ -> fail "mixed guarantee" "unexpected proof"
  end;
  if String.length compiled.octb <> 269 then
    fail "mixed bytes" "length differs";
  let sha = Digestif.SHA256.(to_hex (digest_string compiled.octb)) in
  if not
      (String.equal sha
        "67f8f96b0cf244162a8ea152a55cf46f923fd2ee143f2b0f207cddd57d9798a8")
  then fail "mixed bytes" "digest differs";
  let public =
    List.filter
      (fun value -> value.Octra_vm.Oct_lang.fn_vis = Octra_vm.Oct_lang.Public)
      compiled.ast.funcs
  in
  begin
    match List.map (fun value -> value.Octra_vm.Oct_lang.fn_name) public with
    | ["add"; "read"] -> ()
    | _ -> fail "mixed ABI" "public methods differ"
  end;
  let args = [VM.VInt (Z.of_int 5)] in
  let source = execute ~args "mixed source" "add" mixed in
  let octb = execute_octb ~args "mixed OCTB" "add" mixed in
  result "mixed source" "int:11" source;
  result "mixed OCTB" "int:11" octb;
  if source.effort <> 197 || source.steps <> 30 then
    fail "mixed source" "cost differs";
  if octb.effort <> source.effort || octb.steps <> source.steps then
    fail "mixed OCTB" "cost differs";
  if octb.storage <> source.storage || octb.events <> source.events then
    fail "mixed OCTB" "effects differ";
  execute_octb ~storage:octb.storage "mixed state" "read" mixed
  |> result "mixed state" "int:11";
  execute ~args "mixed public fn" "run" mixed_public
  |> result "mixed public fn" "int:6";
  execute ~args ~value:Z.one "mixed payable helper" "pay" mixed_payable
  |> result "mixed payable helper" "int:6";
  execute ~args "mixed external helper" "bump" mixed_payable
  |> result "mixed external helper" "int:6";
  let guarded =
    attempt ~args ~value:Z.one "mixed external guard" "bump" mixed_payable
  in
  if guarded.stop <> Local.Reverted then
    fail "mixed external guard" "value accepted";
  execute ~args "mixed nested form" "run" mixed_nested
  |> result "mixed nested form" "int:10";
  execute ~args "mixed builtin shadow" "run" mixed_shadow
  |> result "mixed builtin shadow" "int:15";
  execute ~args "mixed nested fn" "run" mixed_nested_fn
  |> result "mixed nested fn" "int:6";
  execute ~args "mixed pure flow" "run" mixed_flow
  |> result "mixed pure flow" "int:6";
  execute ~args "mixed zero arg" "run" mixed_zero
  |> result "mixed zero arg" "int:12";
  execute ~args:[VM.VInt (Z.of_int (-7))] "mixed guard negative" "run"
    mixed_guard
  |> result "mixed guard negative" "int:7";
  execute_octb ~args:[VM.VInt (Z.of_int 7)] "mixed guard positive" "run"
    mixed_guard
  |> result "mixed guard positive" "int:7";
  execute_octb ~args "mixed pure view" "run" mixed_pure_view
  |> result "mixed pure view" "int:6";
  let collision = execute ~args "mixed collision source" "run"
    mixed_collision in
  result "mixed collision source" "bool:false" collision;
  storage_count "mixed collision source" 0 collision;
  let collision = execute_octb ~args "mixed collision OCTB" "run"
    mixed_collision in
  result "mixed collision OCTB" "bool:false" collision;
  storage_count "mixed collision OCTB" 0 collision;
  let first = VM.VBytes (String.make 32 '\001') in
  let second = VM.VBytes (String.make 32 '\002') in
  let source = execute ~args:[first] "mixed bytes source" "echo" mixed_bytes in
  let octb = execute_octb ~args:[first] "mixed bytes OCTB" "echo" mixed_bytes in
  result "mixed bytes source" (Local.value_text first) source;
  result "mixed bytes OCTB" (Local.value_text first) octb;
  if source.effort <> octb.effort || source.steps <> octb.steps then
    fail "mixed bytes" "cost differs";
  execute ~args:[first; first] "mixed bytes equal" "equal" mixed_bytes
  |> result "mixed bytes equal" "bool:true";
  execute_octb ~args:[first; second] "mixed bytes differ" "equal" mixed_bytes
  |> result "mixed bytes differ" "bool:false";
  let short = attempt ~args:[VM.VBytes "short"] "mixed bytes length" "echo"
    mixed_bytes in
  if short.stop <> Local.Reverted then
    fail "mixed bytes length" "short value accepted";
  refuse "mixed once" "form requires explicit use = take" mixed_once;
  let once_source =
    execute ~args "mixed once use source" "run" mixed_once_use
  in
  result "mixed once use source" "int:5" once_source;
  storage_count "mixed once use source" 1 once_source;
  let once_octb =
    execute_octb ~args "mixed once use OCTB" "run" mixed_once_use
  in
  result "mixed once use OCTB" "int:5" once_octb;
  storage_count "mixed once use OCTB" 1 once_octb;
  if once_source.effort <> once_octb.effort
      || once_source.steps <> once_octb.steps
      || once_source.storage <> once_octb.storage
  then fail "mixed once use" "detached execution differs";
  refuse "mixed once use linear" "used id =" mixed_once_use_twice;
  refuse "mixed once use type" "use result type differs = take"
    mixed_once_use_type;
  execute ~args "mixed once use local source" "run" mixed_once_use_local
  |> result "mixed once use local source" "int:5";
  execute_octb ~args "mixed once use local OCTB" "run" mixed_once_use_local
  |> result "mixed once use local OCTB" "int:5";
  let state_local_storage = ["total", "5"] in
  let state_local_source =
    execute ~storage:state_local_storage
      "mixed once use state local source" "run" mixed_once_use_state_local
  in
  let state_local_octb =
    execute_octb ~storage:state_local_storage
      "mixed once use state local OCTB" "run" mixed_once_use_state_local
  in
  result "mixed once use state local source" "int:5" state_local_source;
  same_runtime "mixed once use state local" state_local_source state_local_octb;
  let pair_args = [VM.VInt (Z.of_int 20); VM.VInt (Z.of_int 22)] in
  execute ~args:pair_args "mixed once use capture source" "run"
    mixed_once_use_capture
  |> result "mixed once use capture source" "int:42";
  execute_octb ~args:pair_args "mixed once use capture OCTB" "run"
    mixed_once_use_capture
  |> result "mixed once use capture OCTB" "int:42";
  let direct_call = compile "mixed direct call" mixed_direct_call in
  let direct_use = compile "mixed direct use" mixed_direct_use in
  if not (String.equal direct_call.octb direct_use.octb) then
    fail "mixed direct use" "OCTB differs from short call";
  execute_octb
    ~args:[VM.VInt (Z.of_int 20); VM.VInt (Z.of_int 22)]
    "mixed direct use" "run" mixed_direct_use
  |> result "mixed direct use" "int:42";
  execute ~args "mixed use name source" "run" mixed_use_name
  |> result "mixed use name source" "int:6";
  execute_octb ~args "mixed use name OCTB" "run" mixed_use_name
  |> result "mixed use name OCTB" "int:6";
  refuse "mixed once use constructor" "used id =" mixed_once_use_ctor;
  ignore (compile "mixed once use constructor valid" mixed_once_use_ctor_ok);
  refuse "mixed once use constant" "used id =" mixed_once_use_const;
  execute ~args:[] "mixed once use constant source" "read"
    mixed_once_use_const_ok
  |> result "mixed once use constant source" "int:1";
  execute_octb ~args:[] "mixed once use constant OCTB" "read"
    mixed_once_use_const_ok
  |> result "mixed once use constant OCTB" "int:1";
  refuse "mixed marks" "form requires explicit use = touch" mixed_marks;
  let marked = compile "mixed emit compile" emit_form in
  if not
      (Array.exists
        (function VM.EMIT ("Value", [_]) -> true | _ -> false)
        marked.code)
  then fail "mixed emit compile" "event operation is absent";
  let proof, state =
    match Octra_vm.Bytecode.decode_image marked.octb with
    | Ok { proof = Some raw; state; _ } -> raw, state
    | Ok _ | Error _ -> fail "mixed emit compile" "proof is absent"
  in
  let image = Octra_vm.Bytecode.encode ?state marked.code in
  begin
    match Octra_vm.Aml_call.verify ~image marked.code proof with
    | Ok () -> ()
    | Error error ->
      fail "mixed emit compile" (Octra_vm.Aml_call.text error)
  end;
  begin
    match Contract_cli.image_result image with
    | Ok { proof = None; _ } -> ()
    | Ok _ -> fail "mixed emit stripped" "proof remained visible"
    | Error reason -> fail "mixed emit stripped" reason
  end;
  let changed =
    Array.map
      (function
        | VM.EMIT ("Value", regs) -> VM.EMIT ("Changed", regs)
        | op -> op)
      marked.code
  in
  begin
    match Octra_vm.Aml_call.verify ~image changed proof with
    | Error (Octra_vm.Aml_call.Differs _) -> ()
    | Error error -> fail "mixed emit mutation" (Octra_vm.Aml_call.text error)
    | Ok () -> fail "mixed emit mutation" "changed code accepted"
  end;
  let broken = Bytes.of_string proof in
  Bytes.set broken 0 '\255';
  begin
    match
      Octra_vm.Aml_call.verify ~image marked.code (Bytes.to_string broken)
    with
    | Error Octra_vm.Aml_call.Bits -> ()
    | Error error -> fail "mixed emit proof" (Octra_vm.Aml_call.text error)
    | Ok () -> fail "mixed emit proof" "changed proof accepted"
  end;
  let changed_octb = Octra_vm.Bytecode.encode ~proof changed in
  begin
    match Contract_cli.image_result changed_octb with
    | Error reason when includes reason "call evidence code differs" -> ()
    | Error reason -> fail "mixed emit image" reason
    | Ok _ -> fail "mixed emit image" "changed image accepted"
  end;
  let broken_octb =
    Octra_vm.Bytecode.encode ~proof:(Bytes.to_string broken) marked.code
  in
  begin
    match Contract_cli.image_result broken_octb with
    | Error reason when includes reason "call evidence bits are invalid" -> ()
    | Error reason -> fail "mixed emit image proof" reason
    | Ok _ -> fail "mixed emit image proof" "changed image accepted"
  end;
  let call_changed = Array.copy marked.code in
  let rec change_call pc =
    if pc = Array.length call_changed then
      fail "mixed emit call" "call input is absent"
    else
      match call_changed.(pc) with
      | VM.MSTORE (1001, _) -> call_changed.(pc) <- VM.MSTORE (1001, 0)
      | _ -> change_call (pc + 1)
  in
  change_call 0;
  let call_octb =
    Octra_vm.Bytecode.encode ?state ~proof call_changed
  in
  begin
    match Contract_cli.image_result call_octb with
    | Error reason when includes reason "call image differs" -> ()
    | Error reason -> fail "mixed emit call" reason
    | Ok _ -> fail "mixed emit call" "changed call accepted"
  end;
  let state_octb =
    Octra_vm.Bytecode.encode
      ~state:["foreign", VM.StorageBool]
      ~proof
      marked.code
  in
  begin
    match Contract_cli.image_result state_octb with
    | Error reason when includes reason "call image differs" -> ()
    | Error reason -> fail "mixed emit state" reason
    | Ok _ -> fail "mixed emit state" "changed state accepted"
  end;
  let malformed_octb =
    Octra_vm.Bytecode.encode
      [|VM.LDI
          (0, VM.VString (Octra_vm.Bytecode.proof_prefix ^ "*"));
        VM.STOP|]
  in
  begin
    match Contract_cli.image_result malformed_octb with
    | Error reason when includes reason "OCTB AML proof is invalid" -> ()
    | Error reason -> fail "mixed emit image encoding" reason
    | Ok _ -> fail "mixed emit image encoding" "changed image accepted"
  end;
  let repeated_octb =
    Octra_vm.Bytecode.encode
      ~proof
      [|VM.LDI
          (0, VM.VString (Octra_vm.Bytecode.proof_prefix ^ "WA=="));
        VM.STOP|]
  in
  begin
    match Contract_cli.image_result repeated_octb with
    | Error reason when includes reason "OCTB AML proof is repeated" -> ()
    | Error reason -> fail "mixed emit image repeated" reason
    | Ok _ -> fail "mixed emit image repeated" "changed image accepted"
  end;
  let emit_args = [VM.VInt (Z.of_int 41)] in
  let emit_source = execute ~args:emit_args "mixed emit source" "run" emit_form in
  let emit_octb = execute_octb ~args:emit_args "mixed emit OCTB" "run" emit_form in
  result "mixed emit source" "int:42" emit_source;
  result "mixed emit OCTB" "int:42" emit_octb;
  if emit_source.effort <> 74 || emit_source.steps <> 23 then
    fail "mixed emit source" "cost differs";
  begin
    match emit_source.events with
    | [event]
        when String.equal event.VM.event "Value"
          && event.values = [VM.VInt (Z.of_int 42)] -> ()
    | _ -> fail "mixed emit source" "event differs"
  end;
  if emit_octb.events <> emit_source.events
      || emit_octb.effort <> emit_source.effort
      || emit_octb.steps <> emit_source.steps
      || emit_octb.storage <> emit_source.storage
  then fail "mixed emit OCTB" "detached execution differs";
  refuse "mixed emit pure" "pure function form marks are not empty = note"
    emit_pure;
  refuse "mixed emit direct" "form requires explicit use = note" emit_direct;
  refuse "mixed emit absent" "effect target is absent target = event:Missing"
    emit_absent;
  refuse "mixed emit type"
    "effect site type differs atom = emit<7> expected = bool actual = int"
    emit_type;
  refuse "mixed emit unproved" "function marks exceeded" emit_unproved;
  refuse "mixed emit repeated" "effect atom is repeated atom = emit<7>"
    emit_repeated;
  refuse "mixed emit outside" "effect atoms are available only in form bodies"
    emit_outside;
  let bool_args = [VM.VBool true] in
  let bool_source = execute ~args:bool_args "mixed emit bool source" "run"
    emit_bool in
  let bool_octb = execute_octb ~args:bool_args "mixed emit bool OCTB" "run"
    emit_bool in
  result "mixed emit bool source" "bool:false" bool_source;
  result "mixed emit bool OCTB" "bool:false" bool_octb;
  if bool_source.events <> bool_octb.events
      || bool_source.effort <> bool_octb.effort
      || bool_source.steps <> bool_octb.steps then
    fail "mixed emit bool" "detached execution differs";
  let once_source = execute ~args "mixed emit once source" "run" emit_once in
  let once_octb = execute_octb ~args "mixed emit once OCTB" "run" emit_once in
  result "mixed emit once source" "int:5" once_source;
  result "mixed emit once OCTB" "int:5" once_octb;
  if once_source.events <> once_octb.events
      || once_source.effort <> once_octb.effort
      || once_source.steps <> once_octb.steps then
    fail "mixed emit once" "detached execution differs";
  let nested = compile "mixed emit nested compile" emit_nested in
  let nested_proof =
    match Octra_vm.Bytecode.decode_image nested.octb with
    | Ok { proof = Some raw; _ } -> raw
    | Ok _ | Error _ -> fail "mixed emit nested" "proof is absent"
  in
  begin
    match Octra_vm.Aml_call.decode nested_proof with
    | Ok values when List.length values = 2 -> ()
    | Ok _ -> fail "mixed emit nested" "proof count differs"
    | Error error -> fail "mixed emit nested" (Octra_vm.Aml_call.text error)
  end;
  let nested_source = execute ~args "mixed emit nested source" "run"
    emit_nested in
  let nested_octb = execute_octb ~args "mixed emit nested OCTB" "run"
    emit_nested in
  result "mixed emit nested source" "int:7" nested_source;
  result "mixed emit nested OCTB" "int:7" nested_octb;
  if nested_source.events <> nested_octb.events
      || List.length nested_source.events <> 1
      || nested_source.effort <> nested_octb.effort
      || nested_source.steps <> nested_octb.steps then
    fail "mixed emit nested" "detached execution differs";
  let written = compile "mixed write compile" write_int in
  if not
      (Array.exists
        (function VM.SSTORE ("total", _) -> true | _ -> false)
        written.code)
  then fail "mixed write compile" "state operation is absent";
  let write_proof, write_state =
    match Octra_vm.Bytecode.decode_image written.octb with
    | Ok { proof = Some raw; state; _ } -> raw, state
    | Ok _ | Error _ -> fail "mixed write compile" "proof is absent"
  in
  let write_image = Octra_vm.Bytecode.encode ?state:write_state written.code in
  begin
    match Octra_vm.Aml_call.verify ~image:write_image written.code write_proof with
    | Ok () -> ()
    | Error error ->
      fail "mixed write compile" (Octra_vm.Aml_call.text error)
  end;
  let changed_write =
    Array.map
      (function
        | VM.SSTORE ("total", reg) -> VM.SSTORE ("other", reg)
        | op -> op)
      written.code
  in
  begin
    match
      Octra_vm.Aml_call.verify ~image:write_image changed_write write_proof
    with
    | Error (Octra_vm.Aml_call.Differs _) -> ()
    | Error error ->
      fail "mixed write mutation" (Octra_vm.Aml_call.text error)
    | Ok () -> fail "mixed write mutation" "changed state operation accepted"
  end;
  let write_args = [VM.VInt (Z.of_int 9)] in
  let write_storage = ["total", "3"] in
  let write_source =
    execute ~args:write_args ~storage:write_storage
      "mixed write source" "set" write_int
  in
  let write_octb =
    execute_octb ~args:write_args ~storage:write_storage
      "mixed write OCTB" "set" write_int
  in
  result "mixed write source" "int:9" write_source;
  storage_value "mixed write source" "total" "9" write_source;
  same_runtime "mixed write" write_source write_octb;
  let bool_args = [VM.VBool true] in
  let bool_storage = ["enabled", "true"] in
  let bool_source =
    execute ~args:bool_args ~storage:bool_storage
      "mixed write bool source" "set" write_bool
  in
  let bool_octb =
    execute_octb ~args:bool_args ~storage:bool_storage
      "mixed write bool OCTB" "set" write_bool
  in
  result "mixed write bool source" "bool:false" bool_source;
  storage_value "mixed write bool source" "enabled" "false" bool_source;
  same_runtime "mixed write bool" bool_source bool_octb;
  let bridge_args = [VM.VInt (Z.of_int 2)] in
  let bridge_storage = ["total", "40"] in
  let bridge_source =
    execute ~args:bridge_args ~storage:bridge_storage
      "mixed write bridge source" "bump" write_bridge
  in
  let bridge_octb =
    execute_octb ~args:bridge_args ~storage:bridge_storage
      "mixed write bridge OCTB" "bump" write_bridge
  in
  result "mixed write bridge source" "int:42" bridge_source;
  storage_value "mixed write bridge source" "total" "42" bridge_source;
  same_runtime "mixed write bridge" bridge_source bridge_octb;
  let rollback_storage = ["total", "8"] in
  let rollback_args = [VM.VInt (Z.of_int 9)] in
  let rollback_source =
    execute ~args:rollback_args ~storage:rollback_storage
      "mixed write rollback source" "trial" write_rollback
  in
  let rollback_octb =
    execute_octb ~args:rollback_args ~storage:rollback_storage
      "mixed write rollback OCTB" "trial" write_rollback
  in
  result "mixed write rollback source" "int:8" rollback_source;
  storage_value "mixed write rollback source" "total" "8" rollback_source;
  same_runtime "mixed write rollback" rollback_source rollback_octb;
  refuse "mixed write pure"
    "pure function form marks are not empty = put" write_pure;
  refuse "mixed write pure helper"
    "pure function form marks are not empty = put" write_pure_helper;
  refuse "mixed write view"
    "view function form writes storage = put" write_view;
  refuse "mixed write view helper"
    "view function form writes storage = put" write_view_helper;
  refuse "mixed write direct" "form requires explicit use = put" write_direct;
  refuse "mixed write absent"
    "effect target is absent target = state:missing" write_absent;
  refuse "mixed write type"
    "effect site type differs atom = write<7> expected = bool actual = int"
    write_type;
  refuse "mixed write unproved" "function marks exceeded" write_unproved;
  refuse "mixed write repeated"
    "effect atom is repeated atom = write<7>" write_repeated;
  refuse "mixed write outside"
    "effect atoms are available only in form bodies" write_outside;
  refuse "mixed write constant"
    "constant form marks are not empty = put" write_const;
  refuse "mixed write invariant"
    "invariant form marks are not empty = put" write_invariant;
  let name_args = [VM.VInt (Z.of_int 5)] in
  let name_source = execute ~args:name_args "mixed write name source" "run"
    write_name in
  let name_octb = execute_octb ~args:name_args "mixed write name OCTB" "run"
    write_name in
  result "mixed write name source" "int:6" name_source;
  same_runtime "mixed write name" name_source name_octb;
  refuse "mixed effect" "function cannot enter a direct form = bump"
    mixed_effect;
  refuse "mixed view" "function cannot enter a direct form = increase"
    mixed_view;
  refuse "mixed state" "direct form expression is unsupported" mixed_state;
  refuse "mixed open guard"
    "direct pure function body is unsupported = choose" mixed_open_guard;
  refuse "mixed mutation" "direct pure function body is unsupported = change"
    mixed_mutation;
  refuse "mixed recursion" "direct form recursion is forbidden = loop"
    mixed_recursion;
  refuse "mixed type" "direct form addition requires int" mixed_type;
  refuse "mixed duplicate" "callable name is repeated = same" mixed_duplicate;
  refuse "legacy form" "form declarations require Program" legacy_form;
  refuse "mixed under" "function under exceeded name = total" mixed_under;
  mixed_matrix ();
  mixed_runtime_matrix ();
  mixed_generated ();
  mixed_limits ()

let run () =
  refuse "trailing source" "trailing source after declaration" trailing;
  refuse "duplicate function" "duplicate function name" duplicate_function;
  refuse "duplicate parameter" "duplicate parameter name" duplicate_parameter;
  refuse "duplicate state field" "duplicate state field name" duplicate_state;
  refuse "duplicate state block" "duplicate state declaration" duplicate_empty_state;
  refuse "duplicate constructor" "duplicate constructor" duplicate_constructor;
  refuse "duplicate event" "duplicate event name" duplicate_event;
  refuse "duplicate error" "duplicate error name" duplicate_error;
  refuse "duplicate type" "duplicate type name" duplicate_type;
  refuse "duplicate constant" "duplicate constant name" duplicate_constant;
  refuse "duplicate invariant" "duplicate invariant name" duplicate_invariant;
  refuse "duplicate interface" "duplicate interface name" duplicate_interface;
  refuse "duplicate interface method" "duplicate interface method name"
    duplicate_interface_method;
  begin
    let resolve path =
      if String.equal path "main.aml" then Some duplicate_import
      else if String.equal path "store.aml" then Some imported_interface
      else None
    in
    match Source.compile_multi resolve "main.aml" with
    | Error reason when includes reason "duplicate interface name" -> ()
    | Error reason -> fail "duplicate import" ("unexpected reason = " ^ reason)
    | Ok _ -> fail "duplicate import" "source accepted"
  end;
  refuse "private namespace" "unexpected character: @" private_namespace;
  refuse "wide refinement" "integer exceeds portable range" wide_refinement;
  refuse "foreign refinement" "refinement parameter differs" foreign_refinement;
  refuse "bool refinement" "refinement type is not numeric" bool_refinement;
  refuse "wide error" "integer exceeds portable range" wide_error;
  refuse "NUL string" "NUL byte is not allowed in string" nul_string;
  mixed_checks ();
  core_refuse "form position" "line = 4 col = 5" core_form_position;
  core_refuse "linearity position" "line = 5 col = 5" core_linearity_position;
  core_refuse "vector index" "vec index = 5 size = 3" core_vec_index;
  if Amlc_cli.source_form_raw established_program <> Amlc_cli.Contract_source then
    fail "established source" "program not recognized";
  if Amlc_cli.source_form_raw direct_form <> Amlc_cli.Program_source then
    fail "current source" "program not recognized";
  core_result "direct form" (Octra_vm.C_emit.Int (Z.of_int 42)) direct_form;
  core_equal "direct use equality" direct_form used_form;
  core_result "let before use" (Octra_vm.C_emit.Int (Z.of_int 42)) let_use;
  core_refuse "let use linear" "used id =" let_use_twice;
  core_result "nested form" (Octra_vm.C_emit.Int (Z.of_int 21)) nested_form;
  core_result "integer order" (Octra_vm.C_emit.Int (Z.of_int 42)) order;
  core_result "order edges" (Octra_vm.C_emit.Int (Z.of_int 42)) order_edges;
  core_refuse "order type" "type expected = int actual = bool" order_type;
  core_refuse "order chain" "expected = } actual = <" order_chain;
  core_result "order native" (Octra_vm.C_emit.Bool true) order_auto;
  core_result "order explicit" (Octra_vm.C_emit.Bool true) order_explicit;
  core_input "order left once" (Octra_vm.C_eval.Bool true)
    (Octra_vm.C_eval.Int (Z.of_int 3)) order_left;
  core_input "order right once" (Octra_vm.C_eval.Bool true)
    (Octra_vm.C_eval.Int (Z.of_int 3)) order_right;
  core_result "order form" (Octra_vm.C_emit.Int (Z.of_int 42)) order_form;
  order_matrix ();
  order_limit ();
  reuse_regs ();
  core_input "finite orbit input" (Octra_vm.C_eval.Int (Z.of_int 5))
    (Octra_vm.C_eval.Int (Z.of_int 5)) finite_orbit;
  core_input "finite orbit negative" (Octra_vm.C_eval.Int Z.zero)
    (Octra_vm.C_eval.Int (Z.of_int (-3))) finite_orbit;
  core_input "finite orbit cap" (Octra_vm.C_eval.Int (Z.of_int 64))
    (Octra_vm.C_eval.Int (Z.of_int 100)) finite_orbit;
  let wide = Z.shift_left Z.one 256 in
  core_input "finite orbit wide" (Octra_vm.C_eval.Int (Z.of_int 64))
    (Octra_vm.C_eval.Int wide) finite_orbit;
  core_input "finite orbit wide negative" (Octra_vm.C_eval.Int Z.zero)
    (Octra_vm.C_eval.Int (Z.neg wide)) finite_orbit;
  core_refuse "finite orbit profile" "orbit node limit = 100000"
    finite_orbit_huge;
  core_input "finite orbit order" (Octra_vm.C_eval.Int (Z.of_int 3))
    (Octra_vm.C_eval.Int (Z.of_int 8)) finite_orbit_order;
  core_input "finite orbit zero" (Octra_vm.C_eval.Int (Z.of_int 7))
    (Octra_vm.C_eval.Int (Z.of_int 8)) finite_orbit_zero;
  core_refuse "finite orbit type" "type expected = int actual = bool"
    finite_orbit_type;
  core_refuse "finite orbit body" "orbit type expected = int actual = bool"
    finite_orbit_body;
  core_refuse "orbit seed type" "type expected = int actual = bool"
    orbit_seed_type;
  core_refuse "finite orbit seed type" "type expected = int actual = bool"
    finite_orbit_seed_type;
  core_refuse "linear direct form" "function requires explicit use" linear_form;
  core_refuse "effect direct form" "function requires explicit use" effect_form;
  core_refuse "direct arity" "expected = 2 actual = 1" short_call;
  core_refuse "direct type" "type expected = int actual = bool" wrong_call_type;
  core_refuse "direct order" "unknown function = second" forward_call;
  core_veil "veil evidence" veil plain