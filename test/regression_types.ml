(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

open Regression_support

let wrong_return = {|
program WrongReturn {
  pure fn value(): u64 { return "abc" }
}
|}

let missing_return = {|
contract MissingReturn {
  public fn value(): address { let number = 1 }
}
|}

let wrong_local = {|
contract WrongLocal {
  public fn value(): int {
    let enabled: bool = 7
    return 1
  }
}
|}

let wrong_call = {|
contract WrongCall {
  private fn add(value: int): int { return value + 1 }
  public fn value(): int { return add("7") }
}
|}

let wrong_state = {|
contract WrongState {
  state { enabled: bool }
  public fn set(): bool {
    self.enabled = 1
    return self.enabled
  }
}
|}

let cyclic_const = {|
contract CyclicConst {
  const left = right + 1
  const right = left + 1
  pure fn value(): int { return left }
}
|}

let wrong_operator = {|
contract WrongOperator {
  pure fn value(): int { return true - 1 }
}
|}

let opaque_zero = {|
contract OpaqueZero {
  public view fn present(): bool {
    let key = fhe_load_pk(caller)
    return key != 0
  }
}
|}

let run () =
  refuse "return type" "return type differs" wrong_return;
  refuse "missing return" "function return is not total" missing_return;
  refuse "local type" "local initializer type differs" wrong_local;
  refuse "call type" "function argument type differs" wrong_call;
  refuse "state type" "state assignment type differs" wrong_state;
  refuse "cyclic const" "constant dependency is cyclic" cyclic_const;
  refuse "operator type" "arithmetic operand type differs" wrong_operator;
  ignore (compile "opaque zero" opaque_zero)