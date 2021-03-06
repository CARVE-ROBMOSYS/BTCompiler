(* This program reads a list of "basic skills" from an input XML file
   and writes the corresponding definitions needed for the BT interpreter
   in the OCaml module "skills.ml".

   Two syntaxes are supported:
   - The XML file contains a single SkillList tag. In this case the program
     reads the tags' contents and stops.
   - The XML file contains a root node whose name is not "SkillList". In 
     this case the program reads every SkillList tag which is found inside
     the root node (there may be any number of them). Unknown tags are ignored.

   The program does NOT signal an error if no skills are actually given 
   (i.e., the SkillList tag is empty).
*)

open Utils

(* Reads a sequence of "Action" or "Condition" nodes until first closing tag
   (no children or data is allowed; attributes other than "ID" are ignored) *)
let rec read_skill_list acc i =
  match Xmlm.input i with
    `El_start t ->
    let n = extract_node t in
    begin
      match n with
        "Action" | "Condition" ->
        let id = extract "ID" t in
        if Xmlm.input i = (`El_end) then
          if not (List.mem id acc) then
            read_skill_list (id :: acc) i
          else
            raise (Parsing ("duplicated skill: " ^ id))
        else
          raise (Parsing ("unexpected data in skill " ^ id))
        | _ -> raise (Parsing ("unknown skill specifier: " ^ n))
    end
  | `El_end -> List.rev acc
  | _ -> raise (Parsing "ill-formed input file")

(* Translates a camlstring to the syntactic representation of a coqstring
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
  (* notice that the Parsing exception is not available in the module
     we are generating, so we resort to Invalid_argument *)
  let rec make_transl_func idlist = function
      [] -> "| _ -> invalid_arg (\"unknown skill: \" ^ s)" :: []
    | h :: t -> ("| \"" ^ h ^ "\" -> " ^ (List.hd idlist))
                :: make_transl_func (List.tl idlist) t
  in
  let idlist = make_id_list 1 l in
  let nameslist = make_names_list idlist l in
  let trfunc = make_transl_func idlist l in
  "type skillSet =\n  " ^ (String.concat " | " idlist) ^ "\n\n"
  ^ "let skillName = function\n  " ^ (String.concat "\n  " nameslist) ^ "\n\n"
  ^ "let skill_id s =\n  match s with\n  " ^ (String.concat "\n  " trfunc) ^ "\n"

let read_skills filename =
  let input_ch = open_in filename in
  let i = Xmlm.make_input ~strip:true (`Channel input_ch) in
  let _ = Xmlm.input i in                    (* discard the dtd *)
  let first_tag = Xmlm.input i in
  match first_tag with
  | `El_start t ->
    let n = extract_node t in
    if n = "SkillList" then
      read_skill_list [] i
    else                                     (* there may be a root tag *)
      let sklist_found = ref false in
      let sklist = ref [] in
      while (Xmlm.peek i <> `El_end) do
        let next_tag = Xmlm.input i in
        match next_tag with
        | `El_start t2 ->
          (match extract_node t2 with
           | "SkillList" ->
             sklist_found := true;
             sklist := read_skill_list !sklist i
           | _ -> discard_tag i 1)
        | _ -> raise (Parsing "ill-formed input file")
      done;
      if !sklist_found then
        !sklist
      else
        raise (Parsing "could not find SkillList tag")
  | _ -> raise (Parsing "ill-formed input file")

let _ =
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
                           (String.concat ", " sklist);
        let output_ch = open_out "skills.ml" in
        output_string output_ch (make_skills_module sklist);
        close_out output_ch;
        exit 0
      end
    with
      Sys_error s -> Printf.eprintf "System error: %s\n" s;
                     exit 2
    | Xmlm.Error (pos, err) -> Printf.eprintf "XML parsing error at line %d: %s\n"
                                              (fst pos)
                                              (Xmlm.error_message err);
                               exit 1
    | Parsing s -> Printf.eprintf "Error: %s\n" s;
                   exit 1
    | Invalid_argument s -> Printf.eprintf "Error: %s\n" s;
                            exit 1



