(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

let () =
  Regression_storage.run ();
  Regression_types.run ();
  Regression_source.run ();
  Printf.printf "aml_compiler_regression = pass cases = 82\n"