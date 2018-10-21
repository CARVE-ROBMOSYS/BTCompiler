
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

module Nat :
 sig
  val sub : int -> int -> int

  val eqb : int -> int -> bool

  val divmod : int -> int -> int -> int -> int * int

  val div : int -> int -> int

  val modulo : int -> int -> int

  val eq_dec : int -> int -> bool
 end

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos :
 sig
  val succ : positive -> positive

  val of_succ_nat : int -> positive
 end

module N :
 sig
  val of_nat : int -> n
 end

val zero : char

val one : char

val shift : bool -> char -> char

val ascii_of_pos : positive -> char

val ascii_of_N : n -> char

val ascii_of_nat : int -> char

val append : char list -> char list -> char list

val concat : char list -> char list list -> char list

module type BT_SIG =
 sig
  type skillSet

  val skillName : skillSet -> char list
 end

type symbolic_constant = char list

type identifier = char list

type bool_constant =
| SmvF
| SmvT

type qualid =
| Id of identifier
| Mod of identifier * qualid

type sexp =
| BConst of bool_constant
| SConst of symbolic_constant
| Qual of qualid
| Paren of sexp
| Neg of sexp
| And of sexp * sexp
| Or of sexp * sexp
| Equal of sexp * sexp
| Less of sexp * sexp
| Sum of sexp * sexp
| Count of sexplist
| Case of scexp
and sexplist =
| Sexp of sexp
| AddSexp of sexp * sexplist
and scexp =
| Cexp of sexp * sexp
| AddCexp of sexp * sexp * scexp

type simp_type_spec =
| TBool
| TEnum of symbolic_constant list

type param_list =
| LastP of sexp
| AddP of sexp * param_list

type mod_type_spec =
| TMod of identifier
| TModPar of identifier * param_list

type type_spec =
| TSimp of simp_type_spec
| TComp of mod_type_spec

type varlist =
| LastV of identifier * type_spec
| AddV of identifier * type_spec * varlist

type ivarlist =
| LastI of identifier * simp_type_spec
| AddI of identifier * simp_type_spec * ivarlist

type deflist =
| LastD of identifier * sexp
| AddD of identifier * sexp * deflist

type assign_cons =
| Invar of qualid * sexp
| Init of qualid * sexp
| Next of qualid * sexp

type asslist =
| LastA of assign_cons
| AddA of assign_cons * asslist

type smv_module = { name : identifier; params : identifier list;
                    vars : varlist option; ivars : ivarlist option;
                    defs : deflist option; assigns : asslist option }

val name : smv_module -> identifier

val params : smv_module -> identifier list

val vars : smv_module -> varlist option

val ivars : smv_module -> ivarlist option

val defs : smv_module -> deflist option

val assigns : smv_module -> asslist option

type smv_spec = smv_module list

val varlist_app : varlist -> varlist -> varlist

val varlist_rev : varlist -> varlist

val newline : char list

val translate_qualid : qualid -> identifier

val translate_sexp : sexp -> char list

val translate_sexplist : sexplist -> char list

val translate_cexp : scexp -> char list

val translate_simp_type_spec : simp_type_spec -> char list

val translate_param_list : param_list -> char list

val translate_mod_type_spec : mod_type_spec -> identifier

val translate_type_spec : type_spec -> char list

val translate_varlist : varlist -> char list

val translate_ivarlist : ivarlist -> char list

val translate_deflist : deflist -> char list

val translate_assign_cons : assign_cons -> char list

val translate_asslist : asslist -> char list

val translate : smv_module -> char list

val translate_spec : smv_spec -> char list

type 'a set = 'a list

val empty_set : 'a1 set

val set_add : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set

val string_of_digit : int -> char list

val string_of_nat : int -> char list

val bt_input_type : simp_type_spec

val bt_output_type : simp_type_spec

val bt_action_type : simp_type_spec

val bp_tick_generator : smv_module

val bp_skill_autonomous : smv_module

val bp_skill : smv_module

val bp_TRUE : smv_module

val bp_not : smv_module

val bp_isRunning : smv_module

type modtype =
| Skmod
| TRUEmod
| Seqmod of int
| Fbmod of int
| Parmod of int * int
| Notmod
| Runmod

val modtype_dec : modtype -> modtype -> bool

val bp_identity : char list -> smv_module

module BT_gen_spec :
 functor (X:BT_SIG) ->
 sig
  type nodeKind =
  | Sequence
  | Fallback
  | Parallel of int

  val nodeKind_rect : 'a1 -> 'a1 -> (int -> 'a1) -> nodeKind -> 'a1

  val nodeKind_rec : 'a1 -> 'a1 -> (int -> 'a1) -> nodeKind -> 'a1

  type decKind =
  | Not
  | IsRunning

  val decKind_rect : 'a1 -> 'a1 -> decKind -> 'a1

  val decKind_rec : 'a1 -> 'a1 -> decKind -> 'a1

  type btree =
  | Skill of X.skillSet
  | TRUE
  | Node of nodeKind * char list * btforest
  | Dec of decKind * char list * btree
  and btforest =
  | Child of btree
  | Add of btree * btforest

  val btree_rect :
    (X.skillSet -> 'a1) -> 'a1 -> (nodeKind -> char list -> btforest -> 'a1)
    -> (decKind -> char list -> btree -> 'a1 -> 'a1) -> btree -> 'a1

  val btree_rec :
    (X.skillSet -> 'a1) -> 'a1 -> (nodeKind -> char list -> btforest -> 'a1)
    -> (decKind -> char list -> btree -> 'a1 -> 'a1) -> btree -> 'a1

  val btforest_rect :
    (btree -> 'a1) -> (btree -> btforest -> 'a1 -> 'a1) -> btforest -> 'a1

  val btforest_rec :
    (btree -> 'a1) -> (btree -> btforest -> 'a1 -> 'a1) -> btforest -> 'a1

  val len : btforest -> int

  val sklist : btree -> X.skillSet list

  val skl_forest : btforest -> X.skillSet list

  val normalize : btree -> btree

  val normalize_forest : btforest -> btforest

  val rootName : btree -> char list

  val nodeName : nodeKind -> int -> char list

  val decName : decKind -> char list

  val addmod : btree -> modtype set -> modtype set

  val addmod_f : btforest -> modtype set -> modtype set

  val mk_param_list : int -> char list list

  val mk_seq_invar : int -> asslist

  val mk_seq_trans : int -> scexp

  val make_sequence : int -> smv_module

  val mk_fb_invar : int -> asslist

  val mk_fb_trans : int -> scexp

  val make_fallback : int -> smv_module

  val mk_par_invar : int -> asslist

  val mk_countlist : int -> char list -> sexplist

  val make_parallel : int -> int -> smv_module

  val make_mod : modtype -> bool -> smv_module

  val make_mod_list : modtype list -> bool -> smv_module list

  val make_paramlist : btforest -> param_list

  val make_vars : btree -> varlist

  val make_vars_f : btforest -> varlist

  val make_main : btree -> char list -> smv_module

  val make_spec : btree -> smv_module list

  val mkop : X.skillSet list -> char list list

  val mkov : X.skillSet list -> varlist

  val mkot : X.skillSet list -> asslist

  val ocra_bt_fsm : btree -> smv_module

  val mkparomain : X.skillSet list -> param_list

  val mkvaromain : X.skillSet list -> varlist

  val mkdefomain : X.skillSet list -> deflist

  val ocra_main : btree -> smv_module

  val make_spec_ocra : btree -> smv_module list
 end
