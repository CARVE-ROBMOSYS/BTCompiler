(* Library to package the BT interpreter - version without reset support *)

open Btsem

module Btree = BT_gen_semantics(Skills)

open Utils

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
  Xmlm.input_tree ~el:f1 ~data:f2 i

(* Loads a BT from an XML file *)
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
         while (Xmlm.peek i <> `El_end) do    (* end of root node *)
           let next_tag = Xmlm.input i in
           match next_tag with
           | `El_start t2 ->
              (match (extract_node t2) with
               | "BehaviorTree" ->
                  if !bt = None then
                    bt := Some (input_bt i)
                  else
                    raise (Parsing "too many BehaviorTree tags")
               | _ -> ());              (* unknown tags are silently ignored *)
              discard_tag i 1           (* jump to closing tag *)
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


(* C function mapping (a string identifying) a skill to its return value *)
external exec: string -> Btree.return_enum = "exec"

(* Equivalent term of type skills_input *)
let input_f s =
  exec (camlstring_of_coqstring (Skills.skillName s))

(* The function we shall actually export *)
let tick1 bt =
  Btree.tick bt input_f


(* Callbacks from C code *)
let _ = Callback.register "readbt" load_bt
let _ = Callback.register "tick" tick1
