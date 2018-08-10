open Utils
open Btspec
open Btsem

module Btree = BT_gen_semantics(Skills)
module Btbin = BT_bin_spec(Skills)

(* stuff from interpr.ml *)

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
            let n = (int_of_string tres) in
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

(* Now we need to bridge the general and the binary implementation... *)

let rec binbt_of_genbt gbt =
  let undo_forest f kind name =
    if Btree.len f <> 2 then raise Not_found
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
;;


let main () =
  (* perhaps we should use getopt here... *)
  let argc = Array.length Sys.argv in
  if argc = 1 then begin
      Printf.printf "Please specify an input XML file\n";
      exit 1
    end
  else
    let gbt = load_bt Sys.argv.(1) in
    try
      let bbt = binbt_of_genbt gbt in
      let spec = translate_spec (Btbin.make_spec bbt) in
      print_string (camlstring_of_coqstring spec);
      exit 0
    with
    | Not_found -> print_endline "Sorry, this BT is not supported.";
                   exit 1
;;

main();;

  
