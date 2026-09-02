(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type error =
  | Method_absent of string
  | Method_private of string
  | Arity of int * int
  | Value of int * string
  | Type of int * string

type core_value = {
  vm : Contract_vm.v;
  lit : C_emit.lit;
  value : C_eval.value;
}

let method_def (ast : Oct_lang.contract) name =
  match
    List.find_opt
      (fun (fn : Oct_lang.func_def) -> String.equal fn.fn_name name)
      ast.funcs
  with
  | None -> Error (Method_absent name)
  | Some fn ->
    begin
      match fn.fn_vis with
      | Oct_lang.Public -> Ok fn
      | Oct_lang.Private | Oct_lang.Internal -> Error (Method_private name)
    end

let nibble = function
  | '0' .. '9' as value -> Some (Char.code value - Char.code '0')
  | 'a' .. 'f' as value -> Some (Char.code value - Char.code 'a' + 10)
  | 'A' .. 'F' as value -> Some (Char.code value - Char.code 'A' + 10)
  | _ -> None

let hex value =
  let size = String.length value in
  if size < 2 || String.sub value 0 2 <> "0x" || (size - 2) mod 2 <> 0 then
    None
  else
    let out = Bytes.create ((size - 2) / 2) in
    let rec read index =
      if index >= Bytes.length out then Some (Bytes.to_string out)
      else
        match nibble value.[2 + (index * 2)], nibble value.[3 + (index * 2)] with
        | Some high, Some low ->
          Bytes.set out index (Char.chr ((high lsl 4) lor low));
          read (index + 1)
        | _ -> None
    in
    read 0

let hex_body value = hex ("0x" ^ value)

let integer value =
  try
    let parsed = Z.of_string value in
    if String.equal value (Z.to_string parsed) then Some parsed else None
  with Invalid_argument _ ->
    None

let natural maximum make value =
  match integer value with
  | Some parsed when Z.sign parsed >= 0 && Z.leq parsed maximum ->
    Some (make parsed)
  | Some _ | None -> None

let tagged value =
  match String.index_opt value ':' with
  | None -> None
  | Some at ->
    let tag = String.sub value 0 at in
    let body = String.sub value (at + 1) (String.length value - at - 1) in
    match tag with
    | "int" -> Option.map (fun value -> Contract_vm.VInt value) (integer body)
    | "bool" when String.equal body "true" -> Some (Contract_vm.VBool true)
    | "bool" when String.equal body "false" -> Some (Contract_vm.VBool false)
    | "text" -> Some (Contract_vm.VString body)
    | "bytes" -> Option.map (fun value -> Contract_vm.VBytes value) (hex_body body)
    | "bytes32" ->
      begin
        match hex_body body with
        | Some value when String.length value = 32 ->
          Some (Contract_vm.VBytes32 value)
        | Some _ | None -> None
      end
    | "u64" -> natural Contract_vm.max_u64 (fun value -> Contract_vm.VU64 value) body
    | "u128" ->
      natural Contract_vm.max_u128 (fun value -> Contract_vm.VU128 value) body
    | "u256" ->
      natural Contract_vm.max_u256 (fun value -> Contract_vm.VU256 value) body
    | "addr" -> Some (Contract_vm.VAddr body)
    | _ -> None

let core_value index typ vm =
  let bad () = Error (Value (index, C_type.text typ)) in
  match typ, vm with
  | C_type.Int, Contract_vm.VInt value ->
    Ok { vm; lit = C_emit.Int value; value = C_eval.Int value }
  | C_type.Bool, Contract_vm.VBool value ->
    Ok { vm; lit = C_emit.Bool value; value = C_eval.Bool value }
  | C_type.Bytes len, Contract_vm.VBytes value
      when C_nat.to_int len = String.length value ->
    Ok { vm; lit = C_emit.Bytes value; value = C_eval.Bytes value }
  | (C_type.Int | C_type.Bool | C_type.Bytes _), _ -> bad ()
  | (C_type.Unit | C_type.Vec _ | C_type.Cap _ | C_type.Enc _
    | C_type.Pair _ | C_type.Sum _), _ ->
    Error (Type (index, C_type.text typ))

let core_source index typ raw =
  let vm =
    match typ with
    | C_type.Int -> Option.map (fun value -> Contract_vm.VInt value) (integer raw)
    | C_type.Bool when String.equal raw "true" -> Some (Contract_vm.VBool true)
    | C_type.Bool when String.equal raw "false" -> Some (Contract_vm.VBool false)
    | C_type.Bytes _ -> Option.map (fun value -> Contract_vm.VBytes value) (hex raw)
    | C_type.Unit | C_type.Bool | C_type.Vec _ | C_type.Cap _ | C_type.Enc _
    | C_type.Pair _ | C_type.Sum _ -> None
  in
  match vm with
  | Some value -> core_value index typ value
  | None -> Error (Value (index, C_type.text typ))

let core inputs values =
  let expected = List.length inputs in
  let actual = List.length values in
  if expected <> actual then Error (Arity (expected, actual))
  else
    let rec loop index binds raws out =
      match binds, raws with
      | [], [] -> Ok (List.rev out)
      | bind :: bind_rest, raw :: raw_rest ->
        begin
          match core_source index bind.C_term.typ raw with
          | Ok value -> loop (index + 1) bind_rest raw_rest (value :: out)
          | Error error -> Error error
        end
      | _ -> Error (Arity (expected, actual))
    in
    loop 0 inputs values []

let core_octb types values =
  let expected = Array.length types in
  let actual = List.length values in
  if expected <> actual then Error (Arity (expected, actual))
  else
    let rec loop index raws out =
      match raws with
      | [] -> Ok (List.rev out)
      | raw :: rest ->
        begin
          match tagged raw with
          | Some vm ->
            begin
              match core_value index types.(index) vm with
              | Ok value -> loop (index + 1) rest (value :: out)
              | Error error -> Error error
            end
          | None -> Error (Value (index, C_type.text types.(index)))
        end
    in
    loop 0 values []

let scalar index typ raw =
  let bad () = Error (Value (index, Oct_lang.typ_to_string typ)) in
  match typ with
  | Oct_lang.TInt ->
    begin
      match integer raw with
      | Some value -> Ok (Contract_vm.VInt value)
      | None -> bad ()
    end
  | Oct_lang.TBool ->
    if String.equal raw "true" then Ok (Contract_vm.VBool true)
    else if String.equal raw "false" then Ok (Contract_vm.VBool false)
    else bad ()
  | Oct_lang.TString -> Ok (Contract_vm.VString raw)
  | Oct_lang.TAddress -> Ok (Contract_vm.VAddr raw)
  | Oct_lang.TBytes ->
    begin
      match hex raw with
      | Some value -> Ok (Contract_vm.VBytes value)
      | None -> bad ()
    end
  | Oct_lang.TBytes32 ->
    begin
      match hex raw with
      | Some value when String.length value = 32 ->
        Ok (Contract_vm.VBytes32 value)
      | Some _ | None -> bad ()
    end
  | Oct_lang.TU64 ->
    begin
      match natural Contract_vm.max_u64 (fun value -> Contract_vm.VU64 value) raw with
      | Some value -> Ok value
      | None -> bad ()
    end
  | Oct_lang.TU128 ->
    begin
      match natural Contract_vm.max_u128 (fun value -> Contract_vm.VU128 value) raw with
      | Some value -> Ok value
      | None -> bad ()
    end
  | Oct_lang.TU256 ->
    begin
      match natural Contract_vm.max_u256 (fun value -> Contract_vm.VU256 value) raw with
      | Some value -> Ok value
      | None -> bad ()
    end
  | Oct_lang.TEnum _ ->
    begin
      match integer raw with
      | Some value -> Ok (Contract_vm.VInt value)
      | None -> bad ()
    end
  | Oct_lang.TCipher
  | Oct_lang.TPubKey
  | Oct_lang.TMap _
  | Oct_lang.TList _
  | Oct_lang.TStruct _
  | Oct_lang.TOption _
  | Oct_lang.TTuple _
  | Oct_lang.TVoid -> Error (Type (index, Oct_lang.typ_to_string typ))

let parse ast name values =
  match method_def ast name with
  | Error error -> Error error
  | Ok fn ->
    let expected = List.length fn.fn_params in
    let actual = List.length values in
    if expected <> actual then Error (Arity (expected, actual))
    else
      let rec loop index params values parsed =
        match params, values with
        | [], [] -> Ok (List.rev parsed)
        | param :: param_rest, value :: value_rest ->
          begin
            match scalar index param.Oct_lang.p_typ value with
            | Ok item -> loop (index + 1) param_rest value_rest (item :: parsed)
            | Error error -> Error error
          end
        | _ -> Error (Arity (expected, actual))
      in
      loop 0 fn.fn_params values []

let storage_kind (ast : Oct_lang.contract) = function
  | Oct_lang.TInt -> Some Contract_vm.StorageInt
  | Oct_lang.TBool -> Some Contract_vm.StorageBool
  | Oct_lang.TString -> Some Contract_vm.StorageString
  | Oct_lang.TBytes -> Some Contract_vm.StorageBytes
  | Oct_lang.TBytes32 -> Some Contract_vm.StorageBytes32
  | Oct_lang.TU64 -> Some Contract_vm.StorageU64
  | Oct_lang.TU128 -> Some Contract_vm.StorageU128
  | Oct_lang.TU256 -> Some Contract_vm.StorageU256
  | Oct_lang.TAddress -> Some Contract_vm.StorageAddr
  | Oct_lang.TEnum name ->
    if
      List.exists
        (fun item -> String.equal item.Oct_lang.en_name name)
        ast.enums
    then Some Contract_vm.StorageInt
    else None
  | Oct_lang.TCipher
  | Oct_lang.TPubKey
  | Oct_lang.TMap _
  | Oct_lang.TList _
  | Oct_lang.TStruct _
  | Oct_lang.TOption _
  | Oct_lang.TTuple _
  | Oct_lang.TVoid -> None

let storage_kinds (ast : Oct_lang.contract) =
  match ast.declaration with
  | Oct_lang.ProgramDecl ->
    List.filter_map
      (fun field ->
        Option.map
          (fun kind -> field.Oct_lang.sf_name, kind)
          (storage_kind ast field.sf_typ))
      ast.state
  | Oct_lang.ContractDecl | Oct_lang.InterfaceDecl -> []

let error_text = function
  | Method_absent name -> Printf.sprintf "method is absent method = %s" name
  | Method_private name -> Printf.sprintf "method is not public method = %s" name
  | Arity (expected, actual) ->
    Printf.sprintf "argument count differs expected = %d actual = %d"
      expected actual
  | Value (index, typ) ->
    Printf.sprintf "argument value is invalid index = %d type = %s" index typ
  | Type (index, typ) ->
    Printf.sprintf "argument type is unavailable index = %d type = %s" index typ