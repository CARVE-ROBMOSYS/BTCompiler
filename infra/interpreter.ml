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

let coqstring_uppercase_ascii_of_camlstring s =
  let rec cstring accu pos =
    if pos < 0 then accu else
    let d = if s.[pos] >= 'a' && s.[pos] <= 'z' then
      Char.chr (Char.code s.[pos] - 32)
    else
      s.[pos] in
    cstring (d :: accu) (pos - 1)
  in cstring [] (String.length s - 1)

(* Infrastructure for reading a BT from an XML file *)

let extract_node t =
  (snd (fst t))

let extract_id t =
  let attr_list = snd t in
  let id = List.find (fun attr -> (snd (fst attr)) = "ID") attr_list in
  snd id

let extract_name t =
  let attr_list = snd t in
  let name = List.find (fun attr -> (snd (fst attr)) = "name") attr_list in
  snd name

(* This function is called by input_bt to manage opening/closing tags *)
let f1 t childs =
  let rec forest_of_list = function
      [] -> assert false
    | [h] -> Btree.Child h
    | h::t -> Btree.Add (h, forest_of_list t)
  in
  let n = extract_node t in
  if (n = "Action") || (n = "Condition") then
    Btree.Skill (Skills.skill_id (extract_id t))
  else match n with
         "Sequence" -> Btree.Node (Btree.Sequence,
                                   (coqstring_of_camlstring (extract_name t)),
                                   (forest_of_list childs))
       | "Fallback" -> Btree.Node (Btree.Fallback,
                                   (coqstring_of_camlstring (extract_name t)),
                                   (forest_of_list childs))
       (* Parallel nodes, Decorators still to be added... *)
       | _ -> invalid_arg ("Unkown node: " ^ n)

(* This function is called by input_bt to manage data tags
   since our XML files never have data fields, we just throw an exception *)
let f2 s =
  invalid_arg "unexpected data in input XML file"

let input_bt i =
  Xmlm.input_tree ~el:f1 ~data:f2 i

(* This implementation is a bit inefficient; it may be better to 
   rework directly the input_tree function from the Xmlm module

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
  | _ -> invalid_arg "unexpected tag"
 *)

let load_bt filename =
  let input_ch = open_in filename in
  let i = Xmlm.make_input ~strip:true (`Channel input_ch) in
  let _ = Xmlm.input i in                    (* discard the dtd *)
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
        else invalid_arg "cannot find BehaviorTree node"
      | _ -> invalid_arg "cannot find BehaviorTree node"
    else invalid_arg "first node is not root"
  | _ -> invalid_arg "cannot find root node"


let main () =
  let argc = Array.length Sys.argv in
  if argc = 1 then print_endline "No file specified"
  else
    try
      let bt = load_bt Sys.argv.(1) in
      print_string "Found a bt with ";
      print_int (Btree.count_skills bt);
      print_string " leaves\n";
      (* ... other things to do ... *)
      exit 0
    with
      (* raised by open_in *)
      (* raised by load_bt *)
      Invalid_argument s -> print_endline s; exit 1
;;


main();;
