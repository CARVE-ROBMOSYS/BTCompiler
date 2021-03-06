(* Specification extractor
   This version works for binary-branching BTs, implementing the new
   semantics + OCRA interface (post-deliverable 5.3) *)

open Btgspec
module Btree = BT_gen_spec(Skills)

open Btbspec
module Btbin = BT_bin_spec(Skills)

open Utils

(*** Start of load_bt code ***)

(* This function is called by input_tree to manage opening/closing tags *)
let f1 tag children =
  let rec tree_of_list = function
      [] -> raise (Parsing "ill-formed BT (decorator with no children)")
    | [h] -> h
    | _ -> raise (Parsing "ill-formed BT (decorator with too many children)")
  in
  let rec forest_of_list = function
      [] -> (raise (Parsing "ill-formed BT (node with no children)"))
    | [h] -> Btree.Child h
    | h :: t -> Btree.Add (h, forest_of_list t)
  in
  let n = extract_node tag in
  if (n = "Action") || (n = "Condition") then
    Btree.Skill (Skills.skill_id (extract "ID" tag))
  else match n with
         "Sequence" ->
         Btree.Node (Btree.Sequence,
                     (coqstring_of_camlstring (extract "name" tag)),
                     (forest_of_list children))
       | "Fallback" ->
          Btree.Node (Btree.Fallback,
                      (coqstring_of_camlstring (extract "name" tag)),
                      (forest_of_list children))
       | "Parallel" ->
          begin
            let tres = extract "threshold" tag in
            match int_of_string tres with
            | exception (Failure _) ->
               raise (Parsing ("bad threshold in parallel node "
                               ^ (extract "name" tag)))
            | n ->
               if (n < 0) || (n > (List.length children)) then
                 raise (Parsing ("bad threshold in parallel node "
                                 ^ (extract "name" tag)))
               else
                 Btree.Node (Btree.Parallel n,
                             (coqstring_of_camlstring (extract "name" tag)),
                             (forest_of_list children))
          end
       | "Decorator" ->
          begin
            let d = extract "ID" tag in
            match d with
            | "Negation" ->
               Btree.Dec (Btree.Not,
                          (coqstring_of_camlstring (extract "name" tag)),
                          (tree_of_list children))
            | "IsRunning" ->
               Btree.Dec (Btree.IsRunning,
                          (coqstring_of_camlstring (extract "name" tag)),
                          (tree_of_list children))
            | _ -> raise (Parsing ("unknown decorator: " ^ d))
          end
       | _ -> raise (Parsing ("unkown node: " ^ n))

(* This function is called by input_tree to manage data tags
   Since our XML files never have data fields, we just throw an exception *)
let f2 s =
  raise (Parsing "unexpected data in input XML file")

(* Parses a BT using the Xmlm input_tree facility *)
let input_bt i =
  match Xmlm.peek i with
  | `El_start t ->
    if (extract_node t) = "Root" then
      let _ = Xmlm.input i in                (* opening Root tag *)
      let bt = Xmlm.input_tree ~el:f1 ~data:f2 i in
      let _ = Xmlm.input i in                (* closing Root tag *)
      bt
    else
      Xmlm.input_tree ~el:f1 ~data:f2 i
  | _ -> raise (Parsing "ill-formed BehaviorTree tag")

(* Loads a BT from an XML file *)
let load_bt filename =
  try
    let input_ch = open_in filename in
    let i = Xmlm.make_input ~strip:true (`Channel input_ch) in
    let _ = Xmlm.input i in                  (* discard the dtd *)
    let root_tag = Xmlm.input i in
    match root_tag with
    | `El_start t1 ->
      if (extract_node t1) = "root" then     (* root node found *)
        let bt = ref None in
        while (Xmlm.peek i <> `El_end) do    (* repeat until end of root node *)
          let next_tag = Xmlm.input i in
          match next_tag with
          | `El_start t2 ->
            (match (extract_node t2) with
             | "BehaviorTree" ->
               if !bt = None then
                 bt := Some (input_bt i)
               else
                 raise (Parsing "too many BehaviorTree tags")
             | _ -> ());                (* unknown tags are silently ignored *)
            discard_tag i 1             (* jump to closing tag *)
          | _ -> raise (Parsing "ill-formed input file")
        done;
        close_in input_ch;
        match !bt with
        | Some x -> x
        | None -> raise (Parsing "cannot find BehaviorTree node")
      else raise (Parsing "cannot find root node")
    | _ -> raise (Parsing "ill-formed input file")
  with
    Sys_error s -> Printf.eprintf "System error: %s\n" s;
                   exit 2
  | Xmlm.Error (pos, err) -> Printf.eprintf "XML parsing error at line %d: %s\n"
                                            (fst pos)
                                            (Xmlm.error_message err);
                             exit 1
  | Parsing s -> Printf.eprintf "BT parsing error: %s\n" s;
                 exit 1
  (* Invalid_argument is raised when you pass to Skills.skill_id a string 
     which does not correspond to any skill *)
  | Invalid_argument s -> Printf.eprintf "Error: %s\n" s;
                          exit 1

(*** End of load_bt code ***)

(* The following function is used to map the arbitrary-branching BT
   read by load_bt to an equivalent binary-branching BT. *)

exception Unsupported

let rec binbt_of_genbt gbt =
  let undo_forest f kind name =
    if Btree.len f <> 2 then raise Unsupported
    else
      let first, second =
        match f with
        | Btree.Add (t1, Btree.Child t2) -> t1, t2
        | _ -> assert false  (* should never happen *)
      in
      Btbin.Node (kind,
                  name,
                  (binbt_of_genbt first),
                  (binbt_of_genbt second))
  in
  (* we could use a more clever implementation which maps a forest into a
  sequence of binary constructors using associativity; however this would fail
  anyway for Parallel nodes with intermediate threshold, so it is more
  transparent to just alert the user if he supplies an unsupported BT *)

  match gbt with
  | Btree.Skill s -> Btbin.Skill s
  | Btree.TRUE -> Btbin.TRUE
  | Btree.Node (nk, name, f) ->
     begin
       match nk with
       | Btree.Sequence -> undo_forest f Btbin.Sequence name
       | Btree.Fallback -> undo_forest f Btbin.Fallback name
       | Btree.Parallel n -> undo_forest f
                                         (if n = 1 then Btbin.Parallel1
                                          else Btbin.Parallel2)
                                         name
     end
  | Btree.Dec (dk,name,t) ->
     let new_dec =
       match dk with
       | Btree.Not -> Btbin.Not
       | Btree.IsRunning -> Btbin.IsRunning
     in
     Btbin.Dec (new_dec,name,binbt_of_genbt t)

(*** Code for reading the configuration file ***)

(*** Contracts ***)

type contract = {
    name: string;
    assumptions: string;
    guarantees: string;
  }

let contract_stack: contract list ref = ref []

let push_contract c =
  contract_stack := c :: !contract_stack

let read_contract id tag =
  let ass = opt_extract "assume" tag in
  let gua = opt_extract "guarantee" tag in
  { name = id;
    assumptions = (match ass with
                   | Some s -> s
                   | None -> "true");
    guarantees = (match gua with
                  | Some s -> s
                  | None -> "true") }

let retrieve_contract id =
  try
    List.find (fun x -> x.name = id) !contract_stack
  with
    Not_found ->
    Printf.eprintf "Could not find a contract for component %s" id;
    exit 1

(*** Signals ***)

type signal = {
    id: string;
    target: string list;
  }

let in_signals: signal list ref = ref []

let out_signals: signal list ref = ref []

(*** Other globals ***)

let sys_name = ref ""

let exports = ref []

(* The following functions are taken (with changes) from readskill.ml *)
let rec get_skill_contracts acc i =
  match Xmlm.peek i with
    `El_start t ->
    let _ = Xmlm.input i in
    let n = extract_node t in
    begin
      match n with
        "Action" | "Condition" ->
        let id = extract "ID" t in
        if Xmlm.input i = (`El_end) then
          if not (List.mem id acc) then      (* new skill? *)
            begin
              push_contract (read_contract id t);
              get_skill_contracts (id :: acc) i
            end
          else
            raise (Parsing ("duplicated skill: " ^ id))
        else
          raise (Parsing ("unexpected data in skill " ^ id))
      | _ -> raise (Parsing ("unknown skill specifier: " ^ n))
    end
  | `El_end -> ()
  | _ -> raise (Parsing "ill-formed input file")

let rec read_taglist i name attr acc =
  match Xmlm.input i with
  | `El_start t ->
     let n = extract_node t in
     if n = name then
       let id = extract attr t in
       if Xmlm.input i = (`El_end) then
         if not (List.mem id acc) then
           read_taglist i name attr (id :: acc)
         else
           raise (Parsing ("duplicated skill: " ^ id))
       else
         raise (Parsing ("unexpected data in tag " ^ n))
     else
       raise (Parsing ("unknown tag: " ^ n))
  | `El_end -> List.rev acc
  | _ -> raise (Parsing "ill-formed input file")

(* This function is used to read the list of InSignal and OutSignal
   inside the Environment tag *)
let read_signals i =
  while (Xmlm.peek i <> `El_end) do
    let next_tag = Xmlm.input i in
    match next_tag with
    | `El_start t ->
      let n = extract_node t in
      begin
        match n with
        | "OutSignal" ->
          let name = extract "name" t in
          let dests = read_taglist i "Destination" "ID" [] in
          let signal = {
            id = name;
            target = dests } in
          out_signals := signal :: !out_signals
        | "InSignal" ->
          let name = extract "name" t in
          let srcs = read_taglist i "Source" "ID" [] in
          let signal = {
            id = name;
            target = srcs } in
          in_signals := signal :: !in_signals
        | _ -> raise (Parsing ("unknown tag in Environment: " ^ n))
      end
    | _ -> raise (Parsing "ill-formed input file")
  done

(* This function is used to read the list of Export inside the System tag *)
let read_exports i =
  while (Xmlm.peek i <> `El_end) do
    let next_tag = Xmlm.input i in
    match next_tag with
    | `El_start t ->
      let n = extract_node t in
      begin
        match n with
        | "Export" ->
          let a = extract "name" t in
          let b = extract "from" t in
          exports := (a, b) :: !exports
        | _ -> raise (Parsing ("unknown tag in System: " ^ n))
      end;
      discard_tag i 1
    | _ -> raise (Parsing "ill-formed input file")
  done

(* Reads the system configuration file *)
let load_conf filename =
  try
    let input_ch = open_in filename in
    let i = Xmlm.make_input ~strip:true (`Channel input_ch) in
    let _ = Xmlm.input i in                  (* discard the dtd *)
    let root_tag = Xmlm.input i in
    match root_tag with
    | `El_start t1 ->
      if (extract_node t1) = "root" then     (* root node found *)
        (* System, SkillList and Environment tags are all required *)
        let sys_found, sklist_found, env_found = ref false, ref false, ref false in
        while (Xmlm.peek i <> `El_end) do    (* repeat until end of root node *)
          match Xmlm.input i with
          | `El_start t2 ->
            (match extract_node t2 with
             | "SkillList" ->
               if not !sklist_found then
                 begin
                   sklist_found := true;
                   get_skill_contracts [] i
                 end
               else
                 raise (Parsing "too many SkillList tags")
             | "System" ->
               if not !sys_found then
                 begin
                   sys_found := true;
                   sys_name := extract "ID" t2;
                   push_contract (read_contract "System" t2);
                   read_exports i
                 end
               else
                 raise (Parsing "too many System tags")
             | "Environment" ->
               if not !env_found then
                 begin
                   env_found := true;
                   push_contract (read_contract "Environment" t2);
                   read_signals i
                 end
               else
                 raise (Parsing "too many Environment tags")
             | _ -> ());                (* unknown tags are silently ignored *)
            discard_tag i 1             (* jump to closing tag *)
          | _ -> raise (Parsing "ill-formed input file")
        done;
        close_in input_ch;
        if not !env_found then
          raise (Parsing "could not find Environment node")
        else
        if not !sklist_found then
          raise (Parsing "could not find SkillList node")
        else
        if not !sys_found then
          raise (Parsing "could not find System node")
        else
          ()                            (* return successfully *)
      else raise (Parsing "cannot find root node")
    | _ -> raise (Parsing "ill-formed input file")
  with
    Sys_error s -> Printf.eprintf "System error: %s\n" s;
                   exit 2
  | Xmlm.Error (pos, err) -> Printf.eprintf "XML parsing error at line %d: %s\n"
                                            (fst pos)
                                            (Xmlm.error_message err);
                             exit 1
  | Parsing s -> Printf.eprintf "Parsing error: %s\n" s;
                 exit 1
  | Invalid_argument s -> Printf.eprintf "Error: %s\n" s;
                          exit 1


(*** Code for OSS file generation ***)

let vis_type_text = "{no, enable, disable}"
let out_type_text = "{none, disabled, running, failed, succeeded}"
let sig_type_text = "{none, failed, succeeded}"

let rec skills_to_names = function
  | [] -> []
  | s :: rest -> (camlstring_of_coqstring (Skills.skillName s))
                 :: skills_to_names rest

(* System component *)

let rec mk_sysout = function
  | [] -> []
  | export :: rest ->
    let (name, component) = export in
    (* Signals skill -> Environment (of type boolean) *)
    match List.find_opt (fun x -> x.id = name) !in_signals with
    | Some _ -> ["  OUTPUT PORT "; (component ^ "_" ^ name); ": boolean;\n"]
                @ mk_sysout rest
    | None ->
      (* Signals Environment -> skill (of type sig_type) *)
      match List.find_opt (fun x -> x.id = name) !out_signals with
      | Some _ -> ["  OUTPUT PORT "; (component ^ "_" ^ name); ": "; sig_type_text; ";\n"]
                  @ mk_sysout rest
      | None ->
        (* Internal signals (of type out_type) *)
        (* Note: we do not test whether the signal really exists... *)
        ["  OUTPUT PORT "; (component ^ "_" ^ name); ": "; out_type_text; ";\n"]
        @ mk_sysout rest

let rec mksubs_skills = function
  | [] -> ["\n  "]
  | skname :: rest ->
     ["SUB "; skname; ": "; String.uppercase_ascii skname; ";\n  "]
     @ mksubs_skills rest

let rec in_conn skname = function
  | [] -> []
  | signal :: rest ->
     if List.mem skname signal.target then
       ["CONNECTION Robot_env."; signal.id; " := "; skname; "."; signal.id; ";\n  "]
       @ in_conn skname rest
     else in_conn skname rest

let rec out_conn skname = function
  | [] -> []
  | signal :: rest ->
     if List.mem skname signal.target then
       ["CONNECTION "; skname; "."; signal.id; " := Robot_env."; signal.id; ";\n\n  "]
       @ out_conn skname rest
     else out_conn skname rest
    
let rec mkconn = function
  | [] -> []
  | skname :: rest ->
     ["CONNECTION Bt_fsm.from_"; skname; " := "; skname; ".to_bt;\n  ";
      "CONNECTION "; skname; ".from_bt := Bt_fsm.to_"; skname; ";\n  "]
     @ in_conn skname !in_signals
     @ out_conn skname !out_signals
     @ mkconn rest

let rec mkconn_exp = function
  | [] -> ["CONNECTION output := Bt_fsm.output;\n\n  ";]
  | export :: rest ->
    let (name, component) = export in
    ["CONNECTION "; component; "_"; name; " := "; component; "."; name; ";\n  "]
    @ mkconn_exp rest

let rec mktail = function
  | [] -> [";\n  "]
  | skname :: rest -> [", "; skname; ".skill_contract"] @ mktail rest

let make_comp_system in_list sk_list =
  let disc_time_head = "@requires discrete-time\n" in
  let header =
    String.concat "" (["COMPONENT "; !sys_name; " system\n INTERFACE\n";
                       "  OUTPUT PORT output: "; out_type_text; ";\n"]
                      @ mk_sysout !exports) in
  let c = retrieve_contract "System" in
  let contract =
    String.concat "" ["  CONTRACT mission\n";
                      "    assume: "; c.assumptions; ";\n";
                      "    guarantee: "; c.guarantees; ";\n"] in
  let subs
    = String.concat "" (["\n REFINEMENT\n";
                         "  SUB Tick_generator: TICK_GENERATOR;\n";
                         "  SUB Bt_fsm: BT_FSM;\n";
                         "  SUB Robot_env: ROBOT_AND_ENVIRONMENT;\n  "]
                        @ (mksubs_skills sk_list)) in
  let connections =
    String.concat "" (["CONNECTION Bt_fsm.visit := Tick_generator.tick;\n  ";
                       "CONNECTION Tick_generator.from_bt := Bt_fsm.output;\n\n  "]
                      @ (mkconn sk_list)
                      @ (mkconn_exp !exports)) in
  let refinement =
    String.concat "" (["CONTRACT mission REFINEDBY Tick_generator.tick_contract, ";
                       "Bt_fsm.bt_fsm_contract, ";
                       "Robot_env.env_contract"] @ mktail sk_list) in

  String.concat "" [disc_time_head; header; contract; subs; connections; refinement]

let component_tick_generator =
  "COMPONENT TICK_GENERATOR\n INTERFACE\n  INPUT PORT from_bt: {none, disabled, running, failed, succeeded};\n  OUTPUT PORT tick: {no, enable};\n  CONTRACT tick_contract\n    assume: true;\n    guarantee: always in the future ((from_bt = none -> tick = no) and (from_bt != none -> tick = enable));\n"

let rec mkports_bt = function
  | [] -> ["INPUT PORT visit: {no, enable};\n  OUTPUT PORT output: "; out_type_text; ";\n"]
  | skname :: rest ->
     ["INPUT PORT from_"; skname; ": "; out_type_text; ";\n  ";
      "OUTPUT PORT to_"; skname; ": "; vis_type_text; ";\n  "]
     @ mkports_bt rest

let make_comp_bt lst =
  let header = "COMPONENT BT_FSM\n INTERFACE\n  " in
  let ports = String.concat "" (mkports_bt lst) in
  let contract = "  CONTRACT bt_fsm_contract\n    assume: true;\n    guarantee: true;\n" in

  String.concat "" [header; ports; contract]

let make_comp_robot lst =
  let rec mkinports_env = function
    | [] -> []
    | signal :: rest ->
      ["INPUT PORT "; signal.id; ": boolean;\n  "]
      @ mkinports_env rest
  in
  let rec mkoutports_env = function
    | [] -> ["\n"]
    | signal :: rest ->
      ["OUTPUT PORT "; signal.id; ": "; sig_type_text; ";\n  "]
      @ mkoutports_env rest
  in
  let header = "COMPONENT ROBOT_AND_ENVIRONMENT\n INTERFACE\n  " in
  let ports = String.concat "" ((mkinports_env !in_signals)
                                @ (mkoutports_env !out_signals)) in
  let c = retrieve_contract "Environment" in
  let contract = String.concat "" ["  CONTRACT env_contract\n";
                                   "   assume: "; c.assumptions; ";\n";
                                   "   guarantee: "; c.guarantees; ";\n"] in

  String.concat "" [header; ports; contract]

let make_comp_skill skname =
  let rec mkinport_sk = function
    | [] -> []
    | signal :: rest ->
       if List.mem skname signal.target then
         ["INPUT PORT "; signal.id; ": "; sig_type_text; ";\n  "] @ mkinport_sk rest
       else mkinport_sk rest
  in
  let rec mkoutport_sk = function
    | [] -> []
    | signal :: rest ->
       if List.mem skname signal.target then
         ["OUTPUT PORT "; signal.id; ": boolean;\n  "] @ mkoutport_sk rest
       else mkoutport_sk rest
  in
  let header =
    String.concat "" ["COMPONENT "; String.uppercase_ascii skname; "\n INTERFACE\n  "] in
  let ports =
    String.concat "" (["INPUT PORT from_bt: "; vis_type_text; ";\n  "]
                      @ mkinport_sk !out_signals
                      @ ["OUTPUT PORT to_bt: "; out_type_text; ";\n  "]
                      @ mkoutport_sk !in_signals) in
  let c = List.find (fun x -> x.name = skname) !contract_stack in
  let contract = String.concat "" ["CONTRACT skill_contract\n";
                                   "   assume: "; c.assumptions; ";\n";
                                   "   guarantee: "; c.guarantees; ";\n"] in

  String.concat "" [header; ports; contract]

(*** Main program ***)

let _ =
  let bt_filename = ref "" in
  let conf_filename = ref "" in
  let arg_usage = "Usage: mkspec bt_file conf_file" in
  let set_filenames s =
    if !bt_filename = "" then bt_filename := s
    else if !conf_filename = "" then conf_filename := s
    else
      begin
        Printf.eprintf "Too many arguments on the command line: %s\n" s;
        exit 1
      end
  in
  Arg.parse [] set_filenames arg_usage;
  if !bt_filename = "" then
    begin
      Printf.eprintf "Please specify the XML file containing the Behavior Tree\n";
      exit 1
    end
  else
  if !conf_filename = "" then
    begin
      Printf.eprintf "Please specify the configuration file\n";
      exit 1
    end
  else                                  (* parameters are ok *)
    let bt = load_bt !bt_filename in    (* load_bt has its own error management *)
    try
      (* Part 1: generation of the SMV module describing the FSM equivalent
         to the loaded BT *)

      let btb = binbt_of_genbt bt in
      let trunk = Filename.remove_extension !bt_filename in
      let smv_filename = String.concat "" [trunk; ".smv"] in
      let smv_outfile = open_out smv_filename in
      let smv_spec = translate_spec (Btbin.make_spec_ocra btb) in
      output_string smv_outfile (camlstring_of_coqstring smv_spec);
      close_out smv_outfile;
      
      (* Part 2: generation of the OSS specification describing the whole
         system (BT + skills + environment) *)

      let _ = load_conf !conf_filename in
      let skill_list = skills_to_names (Btbin.sklist btb) in
      let inner_list = Btbin.inlist btb [] in
      let components_list = [make_comp_system inner_list skill_list;
                             component_tick_generator;
                             make_comp_bt skill_list;
                             make_comp_robot skill_list]
                            @ List.map make_comp_skill skill_list in
      let oss_spec = String.concat "\n" components_list in
      let oss_filename = String.concat "" [trunk; ".oss"] in
      let oss_outfile = open_out oss_filename in
      output_string oss_outfile oss_spec;
      close_out oss_outfile;
      exit 0
    with
    | Sys_error s -> Printf.eprintf "System error: %s\n" s;
      exit 2
    | Unsupported -> Printf.eprintf "The supplied BT has a non-binary node, aborting\n";
      exit 1
