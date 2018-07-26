(* This module contains the helper functions common to the BT interpreter
   and the BT specification extractor. *)

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
