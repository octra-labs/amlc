(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type reg = int

type ('cipher, 'pubkey) value =
  | VInt of Z.t
  | VBool of bool
  | VString of string
  | VBytes of string
  | VBytes32 of string
  | VU64 of Z.t
  | VU128 of Z.t
  | VU256 of Z.t
  | VAddr of string
  | VCipher of 'cipher
  | VPubKey of 'pubkey

type ('cipher, 'pubkey) op =
  | ADD of reg * reg * reg
  | SUB of reg * reg * reg
  | MUL of reg * reg * reg
  | DIV of reg * reg * reg
  | MOD of reg * reg * reg
  | NEG of reg * reg
  | ABS of reg * reg
  | EQ of reg * reg * reg
  | LT of reg * reg * reg
  | GT of reg * reg * reg
  | NEQ of reg * reg * reg
  | LDI of reg * ('cipher, 'pubkey) value
  | MOV of reg * reg
  | SLOAD of reg * string
  | SSTORE of string * reg
  | SDEL of string
  | SLOADK of reg * reg
  | SSTOREK of reg * reg
  | SDELK of reg
  | MLOAD of reg * int
  | MSTORE of int * reg
  | JMP of int
  | JIF of reg * int
  | JDEST of int
  | STOP
  | REVERT
  | CALLER of reg
  | ORIGIN of reg
  | SELF of reg
  | EPOCH of reg
  | EPOCH_TIME of reg
  | VALUE of reg
  | BALANCE of reg * reg
  | TREEHASH of reg
  | NODEID of reg
  | TXHASH of reg
  | XCALL of reg * reg * reg * reg * int
  | SPAWN of reg * reg
  | SPAWN2 of reg * reg * reg * int
  | TRANSFER of reg * reg * reg
  | CHECKPOINT
  | ROLLBACK
  | COMMIT
  | EMIT of string * reg list
  | CONCAT of reg * reg * reg
  | STRLEN of reg * reg
  | ASSERT of reg
  | EFFORT of reg
  | NOP
  | FHE_LOAD_PK of reg * reg
  | FHE_ADD of reg * reg * reg * reg
  | FHE_SUB of reg * reg * reg * reg
  | FHE_MUL of reg * reg * reg * reg
  | FHE_SCALE of reg * reg * reg * reg
  | FHE_DIV_CONST of reg * reg * reg * reg
  | FHE_ADD_CONST of reg * reg * reg * reg
  | FHE_SUB_CONST of reg * reg * reg * reg
  | FHE_VERIFY_ZERO of reg * reg * reg * reg
  | FHE_VERIFY_RANGE of reg * reg * reg * reg
  | FHE_VERIFY_BOUND of reg * reg * reg * reg * reg
  | GROTH16_VERIFY_BN254 of reg * reg * reg * reg
  | FHE_COMMIT of reg * reg * reg
  | FHE_PEDERSEN of reg * reg * reg
  | FHE_SER of reg * reg
  | FHE_DESER of reg * reg
  | FHE_SER_PK of reg * reg
  | FHE_DESER_PK of reg * reg
  | CALL_INT of reg * int
  | MLOADR of reg * reg
  | MSTORER of reg * reg
  | PARSE_INTS of reg * reg * reg
  | ISADDR of reg * reg
  | ISHEX of reg * reg
  | STATE_PATH_KEY of reg * reg
  | OBJECT_MEMBER_COUNT of reg * reg
  | OBJECT_HAS_MEMBER of reg * reg * reg
  | OBJECT_MEMBER_REF_AT of reg * reg * reg
  | OBJECT_TRANSITION_APPLY of reg * reg * reg * reg * reg * reg * reg * reg * reg * reg * reg
  | ASSERT_ADDR of reg
  | SUBSTR of reg * reg * reg * reg
  | INDEXOF of reg * reg * reg
  | SHA256 of reg * reg
  | KECCAK256 of reg * reg
  | ED25519_OK of reg * reg * reg * reg
  | BITAND of reg * reg * reg
  | BITOR of reg * reg * reg
  | BITXOR of reg * reg * reg
  | BITSHL of reg * reg * reg
  | BITSHR of reg * reg * reg
  | SKEYS of reg * reg * reg
  | SKEYS_PAGE of reg * reg * reg * reg * reg
  | SLOADN of reg * reg * reg
  | SSTOREN of reg * reg * reg
  | FSTORE of reg * reg
  | FLOAD of reg * reg
  | MATMUL of reg * reg * reg * reg * reg * reg
  | VECDOT of reg * reg * reg * reg
  | VECDOT_Q16 of reg * reg * reg * reg
  | EXP_LUT of reg * reg
  | EXP_Q16 of reg * reg
  | SOFTMAX_INPLACE of reg * reg
  | SOFTMAX_Q16_INPLACE of reg * reg
  | LAYERNORM_INPLACE of reg * reg * reg * reg
  | LAYERNORM_Q16_INPLACE of reg * reg * reg * reg
  | RELU_INPLACE of reg * reg
  | RMSNORM_INPLACE of reg * reg * reg
  | RMSNORM_Q16_INPLACE of reg * reg * reg
  | SILU_INPLACE of reg * reg
  | SILU_Q16_INPLACE of reg * reg
  | ELEMWISE_MUL_INPLACE of reg * reg * reg
  | ELEMWISE_MUL_Q16 of reg * reg * reg
  | LOAD_INT8_BYTES_TO_MEM of reg * reg * reg * reg * reg
  | RESIDUAL_ADD of reg * reg * reg
  | RESIDUAL_ADD_Q16 of reg * reg * reg
  | ROPE_APPLY of reg * reg * reg * reg
  | ROPE_APPLY_Q16 of reg * reg * reg * reg
  | LOAD_INT8_B64_TO_MEM of reg * reg * reg * reg * reg
  | LOAD_INT8_Q16 of reg * reg * reg * reg * reg
  | APPEND_VEC_Q16 of reg * reg * reg * reg
  | ARGMAX_Q16 of reg * reg * reg
  | MATMUL_Q16 of reg * reg * reg * reg * reg * reg
  | SHIFT_ROUND_INPLACE of reg * reg * reg
  | MATMUL_FP of reg * reg * reg * reg * reg * reg
  | RMSNORM_FP of reg * reg * reg
  | SILU_FP of reg * reg
  | ELEMWISE_MUL_FP of reg * reg * reg
  | RESIDUAL_ADD_FP of reg * reg * reg
  | ROPE_APPLY_FP of reg * reg * reg * reg
  | LOAD_INT8_FP of reg * reg * reg * reg * reg
  | VECDOT_FP of reg * reg * reg * reg
  | ARGMAX_FP of reg * reg * reg
  | ATTENTION_KV_FP of reg * reg * reg * reg * reg * reg * reg * reg
  | ATTENTION_KV_Q16 of reg * reg * reg * reg * reg * reg * reg * reg
  | APPEND_VEC_FP of reg * reg * reg * reg

let max_u64 = Z.of_string "18446744073709551615"
let max_u128 = Z.sub (Z.shift_left Z.one 128) Z.one
let max_u256 = Z.sub (Z.shift_left Z.one 256) Z.one

module Verifier = struct
  type err =
    | InvalidReg of int * int
    | InvalidRegSpan of int * int * int
    | InvalidJumpDest of int
    | DuplicateJDest of int
    | CodeTooLarge of int
    | EmptyCode
    | ReservedKey of int * string

  let max_size = 33_554_432

  let check_reg pc reg =
    if reg < 0 || reg > 63 then Some (InvalidReg (pc, reg)) else None

  let check_regs pc regs = List.find_map (check_reg pc) regs

  let check_reg_span pc base count =
    if base < 0 || count < 0 || base > 64 || count > 64 - base then
      Some (InvalidRegSpan (pc, base, count))
    else None

  let reserved key = String.length key > 0 && Char.code key.[0] = 0

  let verify (code : ('cipher, 'pubkey) op array) =
    if Array.length code = 0 then Error EmptyCode
    else if Array.length code * 32 > max_size then
      Error (CodeTooLarge (Array.length code))
    else
      let dests = Hashtbl.create 32 in
      let duplicate = ref None in
      Array.iter
        (function
          | JDEST value ->
            if Hashtbl.mem dests value then duplicate := Some value;
            Hashtbl.replace dests value true
          | _ -> ())
        code;
      match !duplicate with
      | Some value -> Error (DuplicateJDest value)
      | None ->
        let rec check pc =
          if pc >= Array.length code then Ok ()
          else
            let error =
              match code.(pc) with
              | ADD (dst, left, right)
              | SUB (dst, left, right)
              | MUL (dst, left, right)
              | DIV (dst, left, right)
              | MOD (dst, left, right)
              | EQ (dst, left, right)
              | LT (dst, left, right)
              | GT (dst, left, right)
              | NEQ (dst, left, right)
              | CONCAT (dst, left, right) ->
                check_regs pc [dst; left; right]
              | NEG (dst, src)
              | ABS (dst, src)
              | MOV (dst, src)
              | BALANCE (dst, src)
              | SLOADK (dst, src)
              | SSTOREK (dst, src)
              | SPAWN (dst, src)
              | STRLEN (dst, src) -> check_regs pc [dst; src]
              | SDELK src -> check_reg pc src
              | LDI (dst, _)
              | SLOAD (dst, _)
              | MLOAD (dst, _)
              | CALLER dst
              | ORIGIN dst
              | SELF dst
              | EPOCH dst
              | EPOCH_TIME dst
              | VALUE dst
              | TREEHASH dst
              | NODEID dst
              | TXHASH dst
              | EFFORT dst -> check_reg pc dst
              | SSTORE (key, src) ->
                if reserved key then Some (ReservedKey (pc, key))
                else check_reg pc src
              | SDEL key ->
                if reserved key then Some (ReservedKey (pc, key)) else None
              | MSTORE (_, src) | ASSERT src -> check_reg pc src
              | TRANSFER (dst, addr, value) ->
                check_regs pc [dst; addr; value]
              | XCALL (dst, target, meth, args, count) ->
                begin
                  match check_regs pc [dst; target; meth] with
                  | Some error -> Some error
                  | None -> check_reg_span pc args count
                end
              | SPAWN2 (dst, src, args, count) ->
                begin
                  match check_regs pc [dst; src] with
                  | Some error -> Some error
                  | None -> check_reg_span pc args count
                end
              | FHE_ADD (dst, pk, left, right)
              | FHE_SUB (dst, pk, left, right)
              | FHE_MUL (dst, pk, left, right)
              | FHE_SCALE (dst, pk, left, right)
              | FHE_DIV_CONST (dst, pk, left, right)
              | FHE_ADD_CONST (dst, pk, left, right)
              | FHE_SUB_CONST (dst, pk, left, right)
              | FHE_VERIFY_ZERO (dst, pk, left, right)
              | FHE_VERIFY_RANGE (dst, pk, left, right) ->
                check_regs pc [dst; pk; left; right]
              | GROTH16_VERIFY_BN254 (dst, key, proof, input) ->
                check_regs pc [dst; key; proof; input]
              | FHE_VERIFY_BOUND (dst, pk, cipher, proof, commit) ->
                check_regs pc [dst; pk; cipher; proof; commit]
              | FHE_COMMIT (dst, pk, cipher)
              | FHE_PEDERSEN (dst, pk, cipher) ->
                check_regs pc [dst; pk; cipher]
              | FHE_LOAD_PK (dst, src)
              | FHE_SER (dst, src)
              | FHE_DESER (dst, src)
              | FHE_SER_PK (dst, src)
              | FHE_DESER_PK (dst, src)
              | MLOADR (dst, src)
              | MSTORER (dst, src) -> check_regs pc [dst; src]
              | PARSE_INTS (dst, left, right) ->
                check_regs pc [dst; left; right]
              | ISADDR (dst, src)
              | ISHEX (dst, src)
              | STATE_PATH_KEY (dst, src)
              | OBJECT_MEMBER_COUNT (dst, src) ->
                check_regs pc [dst; src]
              | OBJECT_HAS_MEMBER (dst, left, right)
              | OBJECT_MEMBER_REF_AT (dst, left, right) ->
                check_regs pc [dst; left; right]
              | OBJECT_TRANSITION_APPLY
                  (dst, a, b, c, d, e, f, g, h, i, j) ->
                check_regs pc [dst; a; b; c; d; e; f; g; h; i; j]
              | ASSERT_ADDR src -> check_reg pc src
              | SUBSTR (dst, src, first, count) ->
                check_regs pc [dst; src; first; count]
              | INDEXOF (dst, src, part) ->
                check_regs pc [dst; src; part]
              | SHA256 (dst, src) | KECCAK256 (dst, src) ->
                check_regs pc [dst; src]
              | ED25519_OK (dst, key, message, signature) ->
                check_regs pc [dst; key; message; signature]
              | BITAND (dst, left, right)
              | BITOR (dst, left, right)
              | BITXOR (dst, left, right)
              | BITSHL (dst, left, right)
              | BITSHR (dst, left, right) ->
                check_regs pc [dst; left; right]
              | SKEYS (dst, prefix, base) ->
                check_regs pc [dst; prefix; base]
              | SKEYS_PAGE (dst, next, prefix, after, base) ->
                check_regs pc [dst; next; prefix; after; base]
              | SLOADN (a, b, c) | SSTOREN (a, b, c) ->
                check_regs pc [a; b; c]
              | FSTORE (dst, src) | FLOAD (dst, src) ->
                check_regs pc [dst; src]
              | MATMUL (dst, left, right, m, k, n)
              | MATMUL_Q16 (dst, left, right, m, k, n)
              | MATMUL_FP (dst, left, right, m, k, n) ->
                check_regs pc [dst; left; right; m; k; n]
              | VECDOT (dst, left, right, size)
              | VECDOT_Q16 (dst, left, right, size)
              | VECDOT_FP (dst, left, right, size) ->
                check_regs pc [dst; left; right; size]
              | EXP_LUT (dst, src) | EXP_Q16 (dst, src) ->
                check_regs pc [dst; src]
              | SOFTMAX_INPLACE (addr, size)
              | SOFTMAX_Q16_INPLACE (addr, size)
              | RELU_INPLACE (addr, size)
              | SILU_INPLACE (addr, size)
              | SILU_Q16_INPLACE (addr, size)
              | SILU_FP (addr, size) ->
                check_regs pc [addr; size]
              | LAYERNORM_INPLACE (addr, size, gain, bias)
              | LAYERNORM_Q16_INPLACE (addr, size, gain, bias) ->
                check_regs pc [addr; size; gain; bias]
              | RMSNORM_INPLACE (addr, size, gain)
              | RMSNORM_Q16_INPLACE (addr, size, gain)
              | RMSNORM_FP (addr, size, gain) ->
                check_regs pc [addr; size; gain]
              | ELEMWISE_MUL_INPLACE (dst, src, size)
              | ELEMWISE_MUL_Q16 (dst, src, size)
              | RESIDUAL_ADD (dst, src, size)
              | RESIDUAL_ADD_Q16 (dst, src, size)
              | SHIFT_ROUND_INPLACE (dst, src, size)
              | ELEMWISE_MUL_FP (dst, src, size)
              | RESIDUAL_ADD_FP (dst, src, size)
              | ARGMAX_Q16 (dst, src, size)
              | ARGMAX_FP (dst, src, size) ->
                check_regs pc [dst; src; size]
              | LOAD_INT8_BYTES_TO_MEM (dst, src, off, size, scale)
              | LOAD_INT8_B64_TO_MEM (dst, src, off, size, scale)
              | LOAD_INT8_Q16 (dst, src, off, size, scale)
              | LOAD_INT8_FP (dst, src, off, size, scale) ->
                check_regs pc [dst; src; off; size; scale]
              | ROPE_APPLY (addr, size, pos, base)
              | ROPE_APPLY_Q16 (addr, size, pos, base)
              | ROPE_APPLY_FP (addr, size, pos, base) ->
                check_regs pc [addr; size; pos; base]
              | APPEND_VEC_Q16 (dst, pos, src, size)
              | APPEND_VEC_FP (dst, pos, src, size) ->
                check_regs pc [dst; pos; src; size]
              | ATTENTION_KV_FP (q, k, v, cache, time, nq, nk, head)
              | ATTENTION_KV_Q16 (q, k, v, cache, time, nq, nk, head) ->
                check_regs pc [q; k; v; cache; time; nq; nk; head]
              | EMIT (_, regs) -> check_regs pc regs
              | JIF (src, dest) ->
                begin
                  match check_reg pc src with
                  | Some error -> Some error
                  | None when not (Hashtbl.mem dests dest) ->
                    Some (InvalidJumpDest dest)
                  | None -> None
                end
              | JMP dest ->
                if Hashtbl.mem dests dest then None
                else Some (InvalidJumpDest dest)
              | CALL_INT (dst, dest) ->
                begin
                  match check_reg pc dst with
                  | Some error -> Some error
                  | None when not (Hashtbl.mem dests dest) ->
                    Some (InvalidJumpDest dest)
                  | None -> None
                end
              | JDEST _
              | STOP
              | REVERT
              | CHECKPOINT
              | ROLLBACK
              | COMMIT
              | NOP -> None
            in
            match error with
            | Some error -> Error error
            | None -> check (pc + 1)
        in
        check 0
end