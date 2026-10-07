(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

module Source = Octra_vm.Aml_source
module Local = Octra_vm.Local_vm

let compile source =
  Source.compile ~syntax:Octra_vm.Oct_gen.Source source

let program ?(pure = true) body = {|
program Loop {
  enum E { A }
  enum F { A, B }
  public |} ^ (if pure then "pure " else "") ^ {|fn run(): int {
    let total = 0
|} ^ body ^ {|
    return total
  }
}
|}

let rejects name body =
  match compile (program body) with
  | Ok _ -> failwith (name ^ " accepted loop index write")
  | Error reason ->
    let part = "pure loop index is immutable" in
    let found = ref false in
    for offset = 0 to String.length reason - String.length part do
      if String.sub reason offset (String.length part) = part then
        found := true
    done;
    if not !found then failwith (name ^ " wrong error = " ^ reason)

let returns ?(pure = true) name expected body =
  let compiled = match compile (program ~pure body) with
    | Ok value -> value
    | Error reason -> failwith (name ^ " compile error = " ^ reason)
  in
  let config = Local.config ~method_name:"run" ~args:[] ~strict_values:true () in
  match Local.run ~trace:false config compiled.code with
  | Ok result when result.stop = Local.Returned
      && Local.value_text result.result = "int:" ^ string_of_int expected -> ()
  | Ok result -> failwith (name ^ " result = " ^ Local.value_text result.result)
  | Error reason -> failwith (name ^ " run error = " ^ Local.error_text reason)

let () =
  returns "range capture" 3 {|
    let stop = 3
    for i in 0..stop {
      stop += 1
      total += 1
    }
|};
  returns "nested ranges" 6 {|
    for i in 0..2 {
      for j in 0..3 {
        total += 1
      }
    }
|};
  rejects "reset" {|
    for i in 0..1 {
      i = 0 - 1
    }
|};
  rejects "compound" {|
    for i in 0..1 {
      i -= 1
    }
|};
  rejects "branch" {|
    for i in 0..1 {
      if true {
        i = 0 - 1
      }
    }
|};
  rejects "outer" {|
    for i in 0..1 {
      for j in 0..1 {
        i = 0 - 1
      }
    }
|};
  rejects "inner" {|
    for i in 0..1 {
      for i in 0..1 {
        i = 0 - 1
      }
    }
|};
  rejects "restored" {|
    for i in 0..1 {
      for j in 0..1 {
        let i = 2
      }
      i = 0 - 1
    }
|};
  returns "match alias" 1 {|
    let k = 0
    match E.A { E.A => { let k = 0 } }
    let pad = 0
    for i in 0..1 {
      k = 0 - 1
      total += 1
    }
|};
  returns "range end alias" 1 {|
    let k = 0
    let z = 0
    match E.A { E.A => { let k = 0 let z = 0 } }
    let pad = 0
    for i in 0..1 {
      z += 1
      total += 1
    }
|};
  returns "match shadow" 10 {|
    let k = 8
    match E.A { E.A => { let k = 2 total += k } }
    total += k
|};
  returns "match nested" 15 {|
    let k = 8
    match E.A {
      E.A => {
        let k = 2
        match E.A { E.A => { let k = 3 total += k } }
        total += k
      }
    }
    total += k
    total += 2
|};
  returns "match arms" 10 {|
    let k = 8
    match F.B {
      F.A => { let k = 1 total += k }
      F.B => { let k = 2 total += k }
    }
    total += k
|};
  returns "if shadow" 8 {|
    let k = 8
    if false { let k = 2 }
    total += k
|};
  returns "else shadow" 10 {|
    let k = 8
    if true { total += k } else { let k = 3 }
    total += 2
|};
  returns "if nested" 13 {|
    let k = 8
    if true {
      let k = 2
      if true { let k = 3 total += k }
      total += k
    }
    total += k
|};
  returns "if outer write" 9 {|
    let k = 8
    if true { k += 1 } else { k += 2 }
    total += k
|};
  returns ~pure:false "while shadow" 8 {|
    let k = 8
    while false { let k = 2 }
    total += k
|};
  returns ~pure:false "while scope" 12 {|
    let k = 8
    let i = 0
    while i < 2 { let k = 2 total += k i += 1 }
    total += k
|};
  List.iter (fun body ->
    match compile (program body) with
    | Error _ -> ()
    | Ok _ -> failwith "branch local escaped")
    ["if false { let lost = 4 } return lost";
     "if true { total += lost } else { let lost = 4 }"];
  begin match compile (program {|
    match F.B {
      F.A => { let lost = 4 }
      F.B => { total += lost }
    }
|}) with
  | Error _ -> ()
  | Ok _ -> failwith "match local crossed arms"
  end;
  begin match compile (program "match E.A { E.A => { let lost = 4 } } return lost") with
  | Error _ -> ()
  | Ok _ -> failwith "match local escaped"
  end;
  returns "sum" 6 {|
    for i in 0..4 {
      total += i
    }
|};
  returns "shadow" 15 {|
    for i in 0..3 {
      let i = 4
      i += 1
      total += i
    }
|};
  returns "nested" 3 {|
    for i in 0..2 {
      for i in 0..2 {
        total += i
      }
      total += i
    }
|};
  returns "outer local" 11 {|
    let i = 8
    for i in 0..3 {
      total += i
    }
    i += 0
    total += i
|};
  returns "empty" 0 {|
    for i in 5..2 {
      total += 1
    }
|};
  Printf.printf "event = pure_loop status = passed\n%!"