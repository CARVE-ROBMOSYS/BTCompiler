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

(* Extracts a mandatory attribute from an XML tag *)
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

(* Extracts a optional attribute from an XML tag *)
let opt_extract attr_name tag =
  let attr_list = snd tag in
  try
    let name = List.find (fun attr -> (snd (fst attr)) = attr_name) attr_list in
    Some (snd name)
  with
    Not_found -> None

(* Discards a tag from input stream i *)
let rec discard_tag i depth =
  match Xmlm.input i with
  | `El_start _ -> discard_tag i (depth + 1)
  | `El_end -> if depth = 1 then () else discard_tag i (depth - 1)
  | _ -> raise (Parsing "ill-formed input file")

(* This function can be used to map an arbitrary-branching BT to a 
   binary-branching one. Currently it is not needed, so it is
   commented out.

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

 *)  
