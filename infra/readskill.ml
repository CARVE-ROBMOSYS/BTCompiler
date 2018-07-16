(* build this file with:
   ocamlfind ocamlc -package xmlm -linkpkg readskill.ml -o rs *)

(* we never use XML namespaces *)
let generate_tagname name = ("", name)
let extract_name tagname = snd tagname

(* returns the first attribute of a tag *)
let get_attr alist = snd (List.hd alist)

(* helper function to format a list of strings for displaying *)
let string_of_slist l =
  "[" ^ String.concat "; " l ^ "]"

(* reads a list of skills wrapped in a SkillList tag *)
let rec read_skill_list acc i =
  match Xmlm.input i with
    `El_start t -> let n = extract_name (fst t) in
                   begin
                     match n with
                       "Action" | "Condition" ->
                                   if Xmlm.input i = (`El_end) then
                                     read_skill_list
                                       ((get_attr (snd t))::acc) i
                                   else invalid_arg "unexpected tag in input file"
                       | _ -> invalid_arg ("unknown skill specifier: " ^ n)
                   end
  | `El_end -> List.rev acc
  | _ -> invalid_arg "ill-formed input file"
;;

(* translates a camlstring to a syntactic representation of a coqstring
   (= immutable list of characters) *)
let coqstrrep_of_string s =
  let rec aux result pos =
    if pos < 0 then result
    else aux ("('" ^ String.make 1 s.[pos] ^ "'::" ^ result ^ ")") (pos - 1)
  in aux "[]" (String.length s - 1)

(* generate the ML module contents *)
let make_skills_module l =
  let rec make_id_list i = function
      [] -> []
    | h::t -> ("Sk" ^ (string_of_int i)) :: make_id_list (i+1) t
  in
  let rec make_names_list idlist = function
      [] -> []
    | h::t -> ("| " ^ (List.hd idlist) ^ " -> " ^ coqstrrep_of_string h)
              :: make_names_list (List.tl idlist) t
  in
  let rec make_transl_func idlist = function
      [] -> "| _ -> invalid_arg (\"unknown skill: \" ^ s)"::[]
    | h::t -> ("| \"" ^ h ^ "\" -> " ^ (List.hd idlist))
              :: make_transl_func (List.tl idlist) t
  in
  let idlist = make_id_list 1 l in
  let nameslist = make_names_list idlist l in
  let trfunc = make_transl_func idlist l in
  "type coq_SkillSet =\n  " ^ (String.concat " | " idlist) ^ "\n\n"
  ^ "let coq_SkillName = function\n  " ^ (String.concat "\n  " nameslist) ^ "\n\n"
  ^ "let skill_id s =\n  match s with\n  " ^ (String.concat "\n  " trfunc) ^ "\n"
;;


let main () =
  let argc = Array.length Sys.argv in
  if argc = 1 then invalid_arg "Please specify an input XML file"
  else let input_ch = open_in Sys.argv.(1) in
       let i = Xmlm.make_input ~strip:true (`Channel input_ch) in
       let _ = Xmlm.input i in          (* discards the dtd *)
       let first_tag = Xmlm.input i in
       let sklist =
         match first_tag with
           `El_start t -> if (extract_name (fst t)) = "SkillList" then
                            read_skill_list [] i
                          else
                            invalid_arg "unexpected tag in input file"
         | _ -> invalid_arg "input file is ill-formed"
       in
       begin
         if sklist = [] then print_endline "No skills found"
         else print_endline ("Found "
                             ^ string_of_int (List.length sklist)
                             ^ " skills: "
                             ^ string_of_slist sklist);
         let output_ch = open_out "skills.ml" in
         output_string output_ch (make_skills_module sklist);
         close_out output_ch;
         exit 0
       end
;;

main();;

(* TODO:
   - accept more than one input file? (concatenating the resulting lists)
   - exception handling
 *)
