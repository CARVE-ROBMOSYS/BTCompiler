(* Specification extractor *)

open Btgspec

module Btree = BT_gen_spec(Skills)

open Utils

type contract = {
    name: string;
    assumptions: string;
    guarantees: string;
  }

let contract_stack = ref []

let push_contract c =
  contract_stack := c :: !contract_stack

let mission = ref ""

(* The following functions are adapted from the corresponding ones in
   interp.ml, adding support for reading contracts *)

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
    let id = extract "ID" tag in
    begin
      (* retrieve contract and store it in the stack *)
      let ass = opt_extract "assume" tag in
      let gua = opt_extract "guarantee" tag in
      let node_contract =
        { name = id;
          assumptions = (match ass with
                         | Some s -> s
                         | None -> "true");
          guarantees = (match gua with
                        | Some s -> s
                        | None -> "true") }
      in
      push_contract node_contract;
      (* go on building the BT as usual *)
      Btree.Skill (Skills.skill_id id)
    end
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

let f2 s =
  raise (Parsing "unexpected data in input XML file")

let input_bt i =
  Xmlm.input_tree ~el:f1 ~data:f2 i

let load_bt filename =
  try
    let input_ch = open_in filename in
    let i = Xmlm.make_input ~strip:true (`Channel input_ch) in
    let _ = Xmlm.input i in                   (* discard the dtd *)
    let root_tag = Xmlm.input i in
    match root_tag with
    | `El_start t1 ->
       if (extract_node t1) = "root" then
         let bt = ref None in
         let env_found = ref false in
         while (Xmlm.peek i <> `El_end) do    (* end of root node *)
           let next_tag = Xmlm.input i in
           match next_tag with
           | `El_start t2 ->
              (match (extract_node t2) with
               | "BehaviorTree" ->
                  if !bt = None then
                    begin
                      bt := Some (input_bt i);
                      mission := extract "mission" t2;
                      let ass = opt_extract "assume" t2 in
                      let gua = opt_extract "guarantee" t2 in
                      let bt_contract =
                        { name = "Bt";
                          assumptions = (match ass with
                                         | Some s -> s
                                         | None -> "true");
                          guarantees = (match gua with
                                        | Some s -> s
                                        | None -> "true") }
                      in
                      push_contract bt_contract
                    end
                  else
                    raise (Parsing "too many BehaviorTree tags")
               | "Environment" ->
                  if not !env_found then
                    begin
                      env_found := true;
                      let ass = opt_extract "assume" t2 in
                      let gua = opt_extract "guarantee" t2 in
                      let env_contract =
                        { name = "Environment";
                          assumptions = (match ass with
                                         | Some s -> s
                                         | None -> "true");
                          guarantees = (match gua with
                                        | Some s -> s
                                        | None -> "true") }
                      in
                      push_contract env_contract
                    end
                  else
                    raise (Parsing "too many Environment tags")
               | _ -> ());              (* unknown tags are silently ignored *)
              discard_tag i 1
           | _ -> raise (Parsing "ill-formed input file")
         done;
         close_in input_ch;
         if not !env_found then
           raise (Parsing "cannot find Environment node");
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
  (* Invalid_argument is raised (among other places...) when you pass to
     Skills.skill_id a string which does not correspond to any skill *)
  | Invalid_argument s -> Printf.eprintf "Error: %s\n" s;
                          exit 1

(* Code for OSS-file generation *)

let rec skills_to_names = function
  | [] -> []
  | s :: rest -> (camlstring_of_coqstring (Skills.skillName s))
                 :: skills_to_names rest

let rec mksubs = function
  | [] -> ["\n  "]
  | skname :: rest ->
     ["SUB "; skname; ": "; String.uppercase_ascii skname; ";\n  "]
     @ mksubs rest

let rec mkconn = function
  | [] -> [""]
  | skname :: rest ->
     ["CONNECTION Bt_fsm.from_"; skname; " := "; skname; ".to_bt;\n  ";
      "CONNECTION "; skname; ".from_bt := Bt_fsm.to_"; skname; ";\n  ";
      "CONNECTION Robot_env.req_"; skname; " := "; skname; ".req_"; skname; ";\n  ";
      "CONNECTION "; skname; ".is_"; skname; " := Robot_env.is_"; skname; ";\n\n  "]
     @ mkconn rest

let rec mktail = function
  | [] -> [";\n  "]
  | skname :: rest -> [", "; skname; ".skill_contract"] @ mktail rest

let make_comp_system lst =
  let header =
    String.concat "" ["COMPONENT uc1 system\n INTERFACE\n";
                      "  OUTPUT PORT mission: boolean;\n\n";
                      "  CONTRACT mission\n";
                      "   assume: true;\n";
                      "   guarantee: in the future mission;\n\n";
                      " REFINEMENT\n";
                      "  SUB Bt_fsm: BT_FSM;\n";
                      "  SUB Robot_env: ROBOT_AND_ENVIRONMENT;\n  "] in
  let subs = String.concat "" (mksubs lst) in
  let connections = String.concat "" (mkconn lst) in
  let refinement =
    String.concat "" (["CONNECTION mission := Robot_env."; !mission; ";\n\n  ";
                       "CONTRACT mission REFINEDBY Bt_fsm.bt_contract, ";
                       "Robot_env.env_contract"] @ mktail lst) in

  String.concat "" [header; subs; connections; refinement]

let rec mkports = function
  | [] -> ["\n"]
  | skname :: rest ->
     ["INPUT PORT from_"; skname; ": {none, running, failed, succeeded};\n  ";
      "OUTPUT PORT to_"; skname; ": {Enable, Reset};\n  "]
     @ mkports rest

let make_comp_bt lst =
  let header = "COMPONENT BT_FSM\n INTERFACE\n  " in
  let ports = String.concat "" (mkports lst) in
  let c = List.find (fun x -> x.name = "Bt") !contract_stack in
  let contract = String.concat "" ["  CONTRACT bt_contract\n";
                                   "   assume: "; c.assumptions; ";\n";
                                   "   guarantee: "; c.guarantees; ";\n"] in

  String.concat "" [header; ports; contract]

let rec mkports2 = function
  | [] -> ["\n"]
  | skname :: rest ->
     ["INPUT PORT req_"; skname; ": boolean;\n  ";
      "OUTPUT PORT is_"; skname; ": boolean;\n  "]
     @ mkports2 rest

let make_comp_robot lst =
  let header = "COMPONENT ROBOT_AND_ENVIRONMENT\n INTERFACE\n  " in
  let ports = String.concat "" (mkports2 lst) in
  let c = List.find (fun x -> x.name = "Environment") !contract_stack in
  let contract = String.concat "" ["  CONTRACT env_contract\n";
                                   "   assume: "; c.assumptions; ";\n";
                                   "   guarantee: "; c.guarantees; ";\n"] in

  String.concat "" [header; ports; contract]

let make_comp_skill skname =
  let header =
    String.concat "" ["COMPONENT "; String.uppercase_ascii skname; "\n INTERFACE\n  "] in
  let ports =
    String.concat "" ["INPUT PORT from_bt: {Enable, Reset};\n  ";
                      "INPUT PORT is_"; skname; ": boolean;\n  ";
                      "OUTPUT PORT to_bt: {none, running, failed, succeeded};\n  ";
                      "OUTPUT PORT req_"; skname; ": boolean;\n\n"] in
  let c = List.find (fun x -> x.name = skname) !contract_stack in
  let contract = String.concat "" ["  CONTRACT skill_contract\n";
                                   "   assume: "; c.assumptions; ";\n";
                                   "   guarantee: "; c.guarantees; ";\n"] in

  String.concat "" [header; ports; contract]

(* Main program *)

let _ =
  let argc = Array.length Sys.argv in
  if argc <> 2 then begin
      Printf.printf "Please specify an input XML file\n";
      exit 1
    end
  else
    let bt = load_bt Sys.argv.(1) in   (* has its own error management *)
    try
      (* Part 1: generation of the SMV module describing the FSM equivalent
         to the loaded BT *)

      let trunk = Filename.remove_extension Sys.argv.(1) in
      let smv_spec = translate_spec (Btree.make_spec bt) in
      let smv_filename = String.concat "" [trunk; ".smv"] in
      let smv_outfile = open_out smv_filename in
      output_string smv_outfile (camlstring_of_coqstring smv_spec);
      close_out smv_outfile;
      
      (* Part 2: generation of the OSS specification describing the whole
         system (BT + skills + environment) *)

      let skill_list = skills_to_names (Btree.sklist bt) in
      let components_list = [make_comp_system skill_list;
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
      Sys_error s -> Printf.eprintf "System error: %s\n" s;
                     exit 2


