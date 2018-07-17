(* build this file with:
   ocamlfind ocamlc -package xmlm -linkpkg readskill.ml -o rs
   ocamlbuild -use-ocamlfind 'readskill.native'
 *)

exception Parsing of string

(* we never use XML namespaces *)
let generate_tagname name = ("", name)
let extract_name tagname = snd tagname

(* returns the first attribute of a tag *)
let get_attr alist = snd (List.hd alist)

(* helper function to format a list of strings for displaying *)
let string_of_slist l =
  "[" ^ String.concat "; " l ^ "]"

(* reads a sequence of "Action" or "Condition" nodes 
   (no children or data is allowed) *)
let rec read_skill_list acc i =
  match Xmlm.input i with
    `El_start t ->
    let n = extract_name (fst t) in
    begin
      match n with
        "Action" | "Condition" ->
        let id = get_attr (snd t) in
        if Xmlm.input i = (`El_end) then
          read_skill_list (id :: acc) i
        else
          raise (Parsing ("unexpected data in skill " ^ id))
        | _ -> raise (Parsing ("unknown skill specifier: " ^ n))
    end
  | `El_end -> List.rev acc
  | _ -> raise (Parsing "ill-formed input file")
;;

(* translates a camlstring to the syntactic representation of a coqstring
   (= immutable list of characters) *)
let coqstrrep_of_string s =
  let rec aux result pos =
    if pos < 0 then result
    else aux ("('" ^ String.make 1 s.[pos] ^ "' :: " ^ result ^ ")") (pos - 1)
  in aux "[]" (String.length s - 1)

(* generate the ML module contents *)
let make_skills_module l =
  let rec make_id_list i = function
      [] -> []
    | h :: t -> ("Sk" ^ (string_of_int i)) :: make_id_list (i+1) t
  in
  let rec make_names_list idlist = function
      [] -> []
    | h :: t -> ("| " ^ (List.hd idlist) ^ " -> " ^ coqstrrep_of_string h)
                :: make_names_list (List.tl idlist) t
  in
  let rec make_transl_func idlist = function
      [] -> "| _ -> invalid_arg (\"unknown skill: \" ^ s)" :: []
    | h :: t -> ("| \"" ^ h ^ "\" -> " ^ (List.hd idlist))
                :: make_transl_func (List.tl idlist) t
  in
  let idlist = make_id_list 1 l in
  let nameslist = make_names_list idlist l in
  let trfunc = make_transl_func idlist l in
  "type coq_SkillSet =\n  " ^ (String.concat " | " idlist) ^ "\n\n"
  ^ "let coq_SkillName = function\n  " ^ (String.concat "\n  " nameslist) ^ "\n\n"
  ^ "let skill_id s =\n  match s with\n  " ^ (String.concat "\n  " trfunc) ^ "\n"
;;

let read_skills filename =
  let input_ch = open_in filename in
  let i = Xmlm.make_input ~strip:true (`Channel input_ch) in
  let _ = Xmlm.input i in               (* discard the dtd *)
  let first_tag = Xmlm.input i in
  match first_tag with
    `El_start t -> let n = extract_name (fst t) in
                   if n = "SkillList" then
                     read_skill_list [] i
                   else
                     raise (Parsing ("expected SkillList tag, found " ^ n))
  | _ -> raise (Parsing "input XML is ill-formed")

let main () =
  let argc = Array.length Sys.argv in
  if argc = 1 then begin
      Printf.printf "Please specify an input XML file\n";
      exit 1
    end
  else
    try
      let sklist = read_skills Sys.argv.(1) in
      begin
        if sklist = [] then Printf.printf "Warning: no skills found\n"
        else Printf.printf "Found %d skills: %s\n"
                           (List.length sklist)
                           (string_of_slist sklist);
        let output_ch = open_out "skills.ml" in
        output_string output_ch (make_skills_module sklist);
        close_out output_ch;
        exit 0
      end
    with
      Sys_error s -> Printf.eprintf "System error: %s\n" s; exit 2
    | Xmlm.Error (pos, err) -> Printf.eprintf "XML parsing error at line %d: %s\n"
                                              (fst pos)
                                              (Xmlm.error_message err); exit 1
    | Parsing s -> Printf.eprintf "Error: %s\n" s; exit 1
    | Invalid_argument s -> Printf.eprintf "Error: %s\n" s; exit 1
;;

main();;

(* TODO:
   - accept more than one input file? (concatenating the resulting lists)
 *)
