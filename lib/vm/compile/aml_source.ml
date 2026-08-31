(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type t = {
  name : string;
  declaration : Oct_lang.declaration;
  ast : Oct_lang.contract;
  code : Contract_vm.instr array;
  octb : string;
}

let verifier_text = function
  | Contract_vm.Verifier.InvalidReg (pc, reg) ->
    Printf.sprintf "register r%d is invalid at pc %d" reg pc
  | Contract_vm.Verifier.InvalidRegSpan (pc, base, count) ->
    Printf.sprintf "register span r%d+%d is invalid at pc %d" base count pc
  | Contract_vm.Verifier.InvalidJumpDest dest ->
    Printf.sprintf "jump destination %d is absent" dest
  | Contract_vm.Verifier.DuplicateJDest dest ->
    Printf.sprintf "jump destination %d is repeated" dest
  | Contract_vm.Verifier.CodeTooLarge count ->
    Printf.sprintf "instruction count %d exceeds capacity" count
  | Contract_vm.Verifier.EmptyCode -> "instruction stream is empty"
  | Contract_vm.Verifier.ReservedKey (pc, _) ->
    Printf.sprintf "storage key is reserved at pc %d" pc

let body_empty ast =
  match ast.Oct_lang.declaration with
  | Oct_lang.InterfaceDecl -> ast.interfaces = []
  | Oct_lang.ProgramDecl | Oct_lang.ContractDecl ->
    ast.structs = []
    && ast.enums = []
    && ast.consts = []
    && ast.invariants_decl = []
    && ast.state = []
    && ast.events = []
    && ast.errors = []
    && Option.is_none ast.ctor
    && ast.funcs = []

let compile_ast ast =
  let program = ast.Oct_lang.declaration = Oct_lang.ProgramDecl in
  if body_empty ast then Error "source declaration body is empty"
  else if program
     && List.length ast.Oct_lang.funcs > Program_limits.max_functions then
    Error "program function count exceeds capacity"
  else
    let code = Oct_gen.generate ast in
    if program && Array.length code > Program_limits.max_instructions then
      Error "program instruction count exceeds capacity"
    else
      match Contract_vm.Verifier.verify code with
      | Error error -> Error (verifier_text error)
      | Ok () ->
        let state =
          match ast.Oct_lang.declaration with
          | Oct_lang.ProgramDecl ->
            begin
              match Aml_input.storage_kinds ast with
              | [] -> None
              | rows -> Some rows
            end
          | Oct_lang.ContractDecl | Oct_lang.InterfaceDecl -> None
        in
        Ok {
          name = ast.Oct_lang.name;
          declaration = ast.declaration;
          ast;
          code;
          octb = Bytecode.encode ?state code;
        }

let diagnostic source line column message =
  let file =
    match source with
    | Some path -> "source = " ^ path ^ " "
    | None -> ""
  in
  if line < 1 then file ^ message
  else
    match column with
    | Some value ->
      Printf.sprintf "%sline %d column %d: %s" file line value message
    | None -> Printf.sprintf "%sline %d: %s" file line message

let caught ?source action =
  try action () with
  | Oct_lex.LexError (message, line, column) ->
    Error (diagnostic source line (Some column) message)
  | Oct_parse.ParseError (message, line, column) ->
    Error (diagnostic source line (Some column) message)
  | Oct_gen.GenError (message, line, column) ->
    let column = if column < 1 then None else Some column in
    Error (diagnostic source line column message)
  | Stack_overflow -> Error "stack capacity exceeded"
  | Out_of_memory -> Error "memory capacity exceeded"
  | Failure message | Invalid_argument message -> Error message

let compile source =
  caught (fun () ->
    let ast = Oct_parse.parse source in
    compile_ast ast)

let compile_multi resolver main_path =
  let cache = Hashtbl.create 16 in
  let load path =
    match Hashtbl.find_opt cache path with
    | Some source -> Ok source
    | None ->
      begin
        match resolver path with
        | Some source ->
          Hashtbl.add cache path source;
          Ok source
        | None -> Error ("source is absent path = " ^ path)
      end
  in
  let parse path =
    match load path with
    | Error reason -> Error reason
    | Ok source ->
      caught ~source:path (fun () -> Ok (Oct_parse.parse source))
  in
  let select path parsed names =
    let rec loop out = function
      | [] -> Ok (List.rev out)
      | name :: rest ->
        begin
          match
            List.find_opt
              (fun iface -> String.equal iface.Oct_lang.if_name name)
              parsed.Oct_lang.interfaces
          with
          | Some iface -> loop (iface :: out) rest
          | None ->
            Error
              (Printf.sprintf
                "source = %s imported interface is absent name = %s"
                path name)
        end
    in
    loop [] names
  in
  let rec imports out = function
    | [] -> Ok (List.rev out |> List.concat)
    | import :: rest ->
      let path = import.Oct_lang.imp_path in
      begin
        match parse path with
        | Error reason -> Error reason
        | Ok parsed ->
          begin
            match select path parsed import.imp_names with
            | Error reason -> Error reason
            | Ok selected -> imports (selected :: out) rest
          end
      end
  in
  match parse main_path with
  | Error reason -> Error reason
  | Ok main ->
    begin
      match imports [] main.Oct_lang.imports with
      | Error reason -> Error reason
      | Ok interfaces ->
        caught ~source:main_path (fun () ->
          compile_ast
            { main with Oct_lang.interfaces = interfaces @ main.interfaces })
    end