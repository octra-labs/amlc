(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

let () =
  Case_storage.run ();
  Case_types.run ();
  Case_source.run ();
  Case_host.run ();
  Case_action.run ();
  Case_effect.run ();
  Case_emission.run ();
  Printf.printf "event = compiler_cases status = pass suites = 7 generated = 256\n"