(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

let fix code =
  let labels = Hashtbl.create 10 in
  Array.iteri
    (fun pc op ->
      match op with
      | Contract_vm.JDEST label -> Hashtbl.add labels label pc
      | _ -> ())
    code;
  Array.map
    (function
      | Contract_vm.JIF (reg, label) as op ->
        begin
          match Hashtbl.find_opt labels label with
          | Some pc -> Contract_vm.JIF (reg, pc)
          | None -> op
        end
      | Contract_vm.JMP label as op ->
        begin
          match Hashtbl.find_opt labels label with
          | Some pc -> Contract_vm.JMP pc
          | None -> op
        end
      | Contract_vm.CALL_INT (reg, label) as op ->
        begin
          match Hashtbl.find_opt labels label with
          | Some pc -> Contract_vm.CALL_INT (reg, pc)
          | None -> op
        end
      | op -> op)
    code

let entry code =
  let rec find pc =
    if pc >= Array.length code then None
    else
      match code.(pc) with
      | Contract_vm.JDEST 100 -> Some pc
      | _ -> find (pc + 1)
  in
  find 0