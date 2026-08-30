(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type error =
  | Method_absent of string
  | Method_private of string
  | Arity of int * int
  | Value of int * string
  | Type of int * string

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
  List.filter_map
    (fun field ->
      Option.map
        (fun kind -> field.Oct_lang.sf_name, kind)
        (storage_kind ast field.sf_typ))
    ast.state

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