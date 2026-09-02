(* SPDX-License-Identifier: BSD-3-Clause *)
(* Copyright (c) 2023-2026 Octra Labs <dev@octra.org> *)

type config = {
  method_name : string;
  args : Contract_vm.v list;
  storage : (string * string) list;
  storage_kinds : (string * Contract_vm.storage_kind) list;
  caller : string;
  origin : string;
  address : string;
  value : Z.t;
  limit : int;
  step_cap : int;
  epoch : int;
  epoch_time : int64;
  tree_hash : string;
  node_id : string;
  tx_hash : string;
  view : bool;
  byte_result : Contract_vm.byte_result;
}

type stop =
  | Returned
  | Reverted
  | Step_cap
  | Host_operation of int * string

type frame = {
  index : int;
  pc : int;
  next_pc : int;
  effort_before : int;
  effort_after : int;
  op : Contract_vm.instr;
  result : Contract_vm.v;
}

type outcome = {
  stop : stop;
  result : Contract_vm.v;
  effort : int;
  steps : int;
  storage : (string * string) list;
  events : Contract_vm.event_record list;
  frames : frame list;
}

type error =
  | Dispatcher_absent
  | Duplicate_storage of string
  | Invalid_step_cap
  | Program_counter of int

let local_address =
  "oct11111111111111111111111111111111111111111111"

let config
    ?(storage = [])
    ?(storage_kinds = [])
    ?(caller = local_address)
    ?origin
    ?(address = local_address)
    ?(value = Z.zero)
    ?(limit = 1_000_000)
    ?(step_cap = 100_000)
    ?(epoch = 0)
    ?(epoch_time = 0L)
    ?(tree_hash = String.make 64 '0')
    ?(node_id = "local")
    ?(tx_hash = String.make 64 '0')
    ?(view = false)
    ?(byte_result = Contract_vm.Text_result)
    ~method_name
    ~args
    () =
  {
    method_name;
    args;
    storage;
    storage_kinds;
    caller;
    origin = Option.value origin ~default:caller;
    address;
    value;
    limit;
    step_cap;
    epoch;
    epoch_time;
    tree_hash;
    node_id;
    tx_hash;
    view;
    byte_result;
  }

let host_operation = function
  | Contract_vm.BALANCE _ -> Some "balance"
  | Contract_vm.TRANSFER _ -> Some "transfer"
  | Contract_vm.XCALL _ -> Some "program_call"
  | Contract_vm.SPAWN _ | Contract_vm.SPAWN2 _ -> Some "program_spawn"
  | Contract_vm.STATE_PATH_KEY _ -> Some "state_path"
  | Contract_vm.OBJECT_MEMBER_COUNT _
  | Contract_vm.OBJECT_HAS_MEMBER _
  | Contract_vm.OBJECT_MEMBER_REF_AT _
  | Contract_vm.OBJECT_TRANSITION_APPLY _ -> Some "object_state"
  | Contract_vm.ED25519_OK _ -> Some "ed25519"
  | Contract_vm.GROTH16_VERIFY_BN254 _ -> Some "groth16"
  | Contract_vm.FHE_LOAD_PK _
  | Contract_vm.FHE_ADD _
  | Contract_vm.FHE_SUB _
  | Contract_vm.FHE_MUL _
  | Contract_vm.FHE_SCALE _
  | Contract_vm.FHE_DIV_CONST _
  | Contract_vm.FHE_ADD_CONST _
  | Contract_vm.FHE_SUB_CONST _
  | Contract_vm.FHE_VERIFY_ZERO _
  | Contract_vm.FHE_VERIFY_RANGE _
  | Contract_vm.FHE_VERIFY_BOUND _
  | Contract_vm.FHE_COMMIT _
  | Contract_vm.FHE_PEDERSEN _
  | Contract_vm.FHE_SER _
  | Contract_vm.FHE_DESER _
  | Contract_vm.FHE_SER_PK _
  | Contract_vm.FHE_DESER_PK _ -> Some "fhe"
  | _ -> None

let storage rows =
  let table = Hashtbl.create (List.length rows) in
  let rec add = function
    | [] -> Ok table
    | (key, value) :: rest ->
      if Hashtbl.mem table key then Error (Duplicate_storage key)
      else begin
        Hashtbl.add table key value;
        add rest
      end
  in
  add rows

let storage_rows table =
  Hashtbl.fold (fun key value rows -> (key, value) :: rows) table []
  |> List.sort (fun (left, _) (right, _) -> String.compare left right)

let make_state config storage =
  let ctx = {
    Contract_vm.default_ctx with
    current_epoch = config.epoch;
    epoch_time_ms = config.epoch_time;
    tree_hash = config.tree_hash;
    node_id = config.node_id;
    tx_hash = config.tx_hash;
  }
  in
  let state =
    Contract_vm.create_state
      ~limit:config.limit
      ~int_work_epoch:(Some 0)
      ~ctx
      ~is_view:config.view
      ~strict_values:true
      ~byte_result:config.byte_result
      ~storage_kinds:config.storage_kinds
      ~caller:config.caller
      ~origin:config.origin
      ~address:config.address
      ~value:config.value
      ~storage
      ()
  in
  Hashtbl.replace state.memory.data 999 (Contract_vm.VString "call");
  Hashtbl.replace state.memory.data 1000
    (Contract_vm.VString config.method_name);
  List.iteri
    (fun index value ->
      Hashtbl.replace state.memory.data (1001 + index) value)
    config.args;
  state

let outcome state stop steps frames storage =
  {
    stop;
    result = state.Contract_vm.regs.(0);
    effort = state.effort_used;
    steps;
    storage = storage_rows storage;
    events = List.rev !(state.logs);
    frames = List.rev frames;
  }

let execute ~trace config code entry =
  if config.step_cap < 1 then Error Invalid_step_cap
  else if entry < 0 || entry >= Array.length code then
    Error (Program_counter entry)
  else
    begin
      begin
        match storage config.storage with
        | Error error -> Error error
        | Ok storage ->
          let state = make_state config storage in
          state.Contract_vm.pc <- entry;
          let rec run index frames =
            if index >= config.step_cap then
              Ok (outcome state Step_cap index frames storage)
            else
              let pc = state.pc in
              if pc < 0 || pc >= Array.length code then
                Error (Program_counter pc)
              else
                let effort_before = state.effort_used in
                let op = code.(pc) in
                match host_operation op with
                | Some name ->
                  Ok (outcome state (Host_operation (pc, name)) index frames storage)
                | None ->
                  let progress = Contract_vm.step state code in
                  let frame = {
                    index;
                    pc;
                    next_pc = state.pc;
                    effort_before;
                    effort_after = state.effort_used;
                    op;
                    result = state.regs.(0);
                  }
                  in
                  let frames = if trace then frame :: frames else frames in
                  match progress with
                  | Contract_vm.Running -> run (index + 1) frames
                  | Contract_vm.Finished ->
                    Ok (outcome state Returned (index + 1) frames storage)
                  | Contract_vm.Refused ->
                    Ok (outcome state Reverted (index + 1) frames storage)
          in
          run 0 []
      end
    end

let run_at ~trace config ~entry raw =
  execute ~trace config (Vm_program.fix raw) entry

let run ~trace config raw =
  let code = Vm_program.fix raw in
  match Vm_program.entry code with
  | None -> Error Dispatcher_absent
  | Some entry -> execute ~trace config code entry

let hex value =
  let out = Bytes.create (String.length value * 2) in
  let digit value =
    if value < 10 then Char.chr (Char.code '0' + value)
    else Char.chr (Char.code 'a' + value - 10)
  in
  String.iteri
    (fun index char ->
      let code = Char.code char in
      Bytes.set out (index * 2) (digit (code lsr 4));
      Bytes.set out (index * 2 + 1) (digit (code land 15)))
    value;
  Bytes.to_string out

let text tag value =
  if String.length value <= 96 then tag ^ String.escaped value
  else
    Printf.sprintf "%ssize:%d:sha256:%s"
      tag
      (String.length value)
      Digestif.SHA256.(to_hex (digest_string value))

let value_text = function
  | Contract_vm.VInt value -> "int:" ^ Z.to_string value
  | Contract_vm.VBool value -> "bool:" ^ string_of_bool value
  | Contract_vm.VString value -> text "text:" value
  | Contract_vm.VBytes value -> text "bytes:" (hex value)
  | Contract_vm.VBytes32 value -> text "bytes32:" (hex value)
  | Contract_vm.VU64 value -> "u64:" ^ Z.to_string value
  | Contract_vm.VU128 value -> "u128:" ^ Z.to_string value
  | Contract_vm.VU256 value -> "u256:" ^ Z.to_string value
  | Contract_vm.VAddr value -> "addr:" ^ value
  | Contract_vm.VCipher _ -> "cipher"
  | Contract_vm.VPubKey _ -> "pubkey"

let stop_text = function
  | Returned -> "returned"
  | Reverted -> "reverted"
  | Step_cap -> "step_cap"
  | Host_operation (pc, name) ->
    Printf.sprintf "host_operation pc = %d operation = %s" pc name

let error_text = function
  | Dispatcher_absent -> "program dispatcher is absent"
  | Duplicate_storage key ->
    Printf.sprintf "storage key is repeated key = %s" key
  | Invalid_step_cap -> "step cap is invalid"
  | Program_counter pc ->
    Printf.sprintf "program counter is invalid pc = %d" pc