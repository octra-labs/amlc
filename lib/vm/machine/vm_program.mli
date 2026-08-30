(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

val fix : Contract_vm.instr array -> Contract_vm.instr array
val entry : Contract_vm.instr array -> int option