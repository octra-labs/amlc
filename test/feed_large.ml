(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

let size = 40_000

let () =
  let raw = String.make size '\000' in
  let value = Octra_vm.C_eval.Bytes raw in
  match Octra_vm.C_feed.make [value] with
  | Error error -> failwith (Octra_vm.C_feed.text error)
  | Ok feed ->
    begin
      match Octra_vm.C_feed.decode (Octra_vm.C_feed.encode feed) with
      | Ok exact
        when String.equal
          (Octra_vm.C_feed.encode exact)
          (Octra_vm.C_feed.encode feed) -> ()
      | Ok _ -> failwith "large feed differs"
      | Error error -> failwith (Octra_vm.C_feed.text error)
    end