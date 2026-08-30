(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type format = Text | Events | Dot

val select : string list -> (format, string) result

val write :
  out_channel -> format:format -> digest:string -> string ->
  Octra_vm.C_octb.image -> unit