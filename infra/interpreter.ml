(* Library to package the BT interpreter *)

open Btsem

module Btree = BT_gen_semantics(Skills)

open Btload

(* C function mapping (a string identifying) a skill to its return value *)
external exec: string -> Btree.return_enum = "exec"

(* This is the equivalent term of type skills_input *)
let input_f s =
  exec (camlstring_of_coqstring (Skills.skillName s))

(* The function we shall actually export *)
let tick1 bt =
  Btree.tick bt input_f

(* Callbacks from C code *)
let _ = Callback.register "readbt" load_bt
let _ = Callback.register "tick" tick1
