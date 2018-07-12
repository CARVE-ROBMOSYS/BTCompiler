
(* we never use namespaces *)
let generate_tagname name = ("", name)
let extract_name tagname = snd tagname

(* returns the first attribute of a tag *)
let get_attr alist = snd (List.hd alist)

(* helper function to display a list of strings *)
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

         (* write ML type description in "skills.mli" *)
         (* launch compilation of interpreter library *)

         exit 0
       end
;;

main();;
  
(* TODO:
   - more than one input file? (concatenate the resulting lists...)
   - how to specify contracts?
 *)
