(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

let () =
  Regression_storage.run ();
  Regression_types.run ();
  Regression_source.run ();
  Regression_host.run ();
  Regression_action.run ();
  Regression_effect.run ();
  Regression_emission.run ();
  Printf.printf "aml_compiler_regression = pass suites = 7 generated = 256\n"