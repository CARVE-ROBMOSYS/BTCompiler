(* This module contains the helper functions common to the BT interpreter
   and the BT specification extractor. *)

open Btsem

module Btree = BT_gen_semantics(Skills)

(* Helper functions for translating between camlstrings and coqstrings
   Taken from https://github.com/AbsInt/CompCert/blob/master/lib/Camlcoq.ml *)

let camlstring_of_coqstring (s: char list) =
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)

let coqstring_of_camlstring s =
  let rec cstring accu pos =
    if pos < 0 then accu else cstring (s.[pos] :: accu) (pos - 1)
  in cstring [] (String.length s - 1)

(* Infrastructure for reading BT-related stuff from XML files *)

exception Parsing of string

(* Extracts the name of an XML tag. Notice that our input files never
   use the XML namespace mechanism *)
let extract_node tag = (snd (fst tag))

(* Extracts an attribute (by name) from an XML tag *)
let extract attr_name tag =
  let attr_list = snd tag in
  try
    let name = List.find (fun attr -> (snd (fst attr)) = attr_name) attr_list in
    snd name
  with
    Not_found ->
    raise (Parsing
             ("missing attribute " ^ attr_name ^
                " in node " ^ (extract_node tag)))

(* This function is called by input_tree to manage opening/closing tags *)
let f1 tag childs =
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
                     (forest_of_list childs))
       | "Fallback" ->
          Btree.Node (Btree.Fallback,
                      (coqstring_of_camlstring (extract "name" tag)),
                      (forest_of_list childs))
       | "Parallel" ->
          begin
            let tres = extract "threshold" tag in
            let n = (int_of_string tres) in
            Btree.Node (Btree.Parallel n,
                        (coqstring_of_camlstring (extract "name" tag)),
                        (forest_of_list childs))
          end
       (* Decorators still to be added... *)
       | _ -> raise (Parsing ("unkown node: " ^ n))

(* This function is called by input_tree to manage data tags
   Since our XML files never have data fields, we just throw an exception *)
let f2 s =
  raise (Parsing "unexpected data in input XML file")

let input_bt i =
  Xmlm.input_tree ~el:f1 ~data:f2 i

(* The above implementation is a bit inefficient; it may be better to
   rework directly the input_tree function from the Xmlm module...

let input_bt i =
  match Xmlm.input i with
  | `El_start tag ->
     let rec aux i tags context =
       match Xmlm.input i with
       | `El_start tag -> aux i (tag :: tags) ([] :: context)
       | `El_end ->
          begin
            match tags, context with
            | tag :: tags', childs :: context' ->
               let e = f1 tag (List.rev childs) in
               begin match context' with
               | parent :: context'' -> aux i tags' ((e :: parent) :: context'')
               | [] -> e
               end
            | _ -> assert false
          end
       | _ -> assert false
     in
     aux i (tag :: []) [[]]
  | _ -> raise (Parsing "unexpected tag")
 *)
    
(* Loads a BT from an XML file *)
let load_bt filename =
  try
    let input_ch = open_in filename in
    let i = Xmlm.make_input ~strip:true (`Channel input_ch) in
    let _ = Xmlm.input i in               (* discard the dtd *)
    let root_tag = Xmlm.input i in
    match root_tag with
      `El_start t1 ->
      if (extract_node t1) = "root" then
        let tree_tag = Xmlm.input i in
        match tree_tag with
          `El_start t2 ->
          if (extract_node t2) = "BehaviorTree" then
            let bt = input_bt i in
            close_in input_ch;  (* only one BT per file! *)
            bt
          else raise (Parsing "cannot find BehaviorTree node")
        | _ -> raise (Parsing "cannot find BehaviorTree node")
      else raise (Parsing "first node is not root")
    | _ -> raise (Parsing "first node is not root")
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
