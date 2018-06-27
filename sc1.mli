
val add : int -> int -> int

val append : char list -> char list -> char list

val concat : char list -> char list list -> char list

module type BT_SIG =
 sig
  type coq_SkillSet

  val coq_SkillName : coq_SkillSet -> char list
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

type nexp =
| Simple of sexp
| Basic of sexp

type simp_type_spec =
| TBool
| TEnum of symbolic_constant list

type param_list =
| LastP of nexp
| AddP of nexp * param_list

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
| Next of qualid * nexp

type asslist =
| LastA of assign_cons
| AddA of assign_cons * asslist

type smv_element =
| VAR of varlist
| IVAR of ivarlist
| DEFINE of deflist
| ASSIGN of asslist

type smv_module = { name : identifier; params : identifier list;
                    body : smv_element list }

val name : smv_module -> identifier

val params : smv_module -> identifier list

val body : smv_module -> smv_element list

type smv_spec = smv_module list

val varlist_app : varlist -> varlist -> varlist

val newline : char list

val translate_qualid : qualid -> identifier

val translate_sexp : sexp -> char list

val translate_sexplist : sexplist -> char list

val translate_cexp : scexp -> char list

val translate_nexp : nexp -> char list

val translate_simp_type_spec : simp_type_spec -> char list

val translate_param_list : param_list -> char list

val translate_mod_type_spec : mod_type_spec -> identifier

val translate_type_spec : type_spec -> char list

val translate_varlist : varlist -> char list

val translate_ivarlist : ivarlist -> char list

val translate_deflist : deflist -> char list

val translate_assign_cons : assign_cons -> char list

val translate_asslist : asslist -> char list

val translate_smv_element : smv_element -> char list

val translate_body : smv_element list -> char list

val translate : smv_module -> char list

val translate_spec : smv_spec -> char list

module BT_bin_spec :
 functor (X:BT_SIG) ->
 sig
  type coq_NodeKind =
  | Sequence
  | Fallback
  | Parallel1
  | Parallel2

  val coq_NodeKind_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_NodeKind -> 'a1

  val coq_NodeKind_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_NodeKind -> 'a1

  type coq_DecKind =
  | Not
  | Coq_isRunning

  val coq_DecKind_rect : 'a1 -> 'a1 -> coq_DecKind -> 'a1

  val coq_DecKind_rec : 'a1 -> 'a1 -> coq_DecKind -> 'a1

  type btree =
  | Skill of X.coq_SkillSet
  | TRUE
  | Coq_node of coq_NodeKind * char list * btree * btree
  | Coq_dec of coq_DecKind * char list * btree

  val btree_rect :
    (X.coq_SkillSet -> 'a1) -> 'a1 -> (coq_NodeKind -> char list -> btree -> 'a1 ->
    btree -> 'a1 -> 'a1) -> (coq_DecKind -> char list -> btree -> 'a1 -> 'a1) ->
    btree -> 'a1

  val btree_rec :
    (X.coq_SkillSet -> 'a1) -> 'a1 -> (coq_NodeKind -> char list -> btree -> 'a1 ->
    btree -> 'a1 -> 'a1) -> (coq_DecKind -> char list -> btree -> 'a1 -> 'a1) ->
    btree -> 'a1

  val count_leaves : btree -> int

  val coq_RootName : btree -> char list

  val bt_input_type : simp_type_spec

  val bt_output_type : type_spec

  val boiler_tick_generator : smv_module

  val boiler_skill : smv_module

  val boiler_TRUE : smv_module

  val boiler_sequence : smv_module

  val boiler_fallback : smv_module

  val boiler_par1 : smv_module

  val boiler_par2 : smv_module

  val boiler_not : smv_module

  val boiler_isRunning : smv_module

  val nodename : coq_NodeKind -> char list

  val decname : coq_DecKind -> char list

  val make_vars : btree -> varlist

  val make_main : btree -> smv_module

  val make_spec : btree -> smv_module list
 end

type my_skills =
| Sk1
| Sk2
| Sk3
| Sk4

val my_names : my_skills -> char list

module Coq_ex_skills :
 sig
  type coq_SkillSet = my_skills

  val coq_SkillName : my_skills -> char list
 end

module Coq_bts1 :
 sig
  type coq_NodeKind =
  | Sequence
  | Fallback
  | Parallel1
  | Parallel2

  val coq_NodeKind_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_NodeKind -> 'a1

  val coq_NodeKind_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_NodeKind -> 'a1

  type coq_DecKind =
  | Not
  | Coq_isRunning

  val coq_DecKind_rect : 'a1 -> 'a1 -> coq_DecKind -> 'a1

  val coq_DecKind_rec : 'a1 -> 'a1 -> coq_DecKind -> 'a1

  type btree =
  | Skill of Coq_ex_skills.coq_SkillSet
  | TRUE
  | Coq_node of coq_NodeKind * char list * btree * btree
  | Coq_dec of coq_DecKind * char list * btree

  val btree_rect :
    (Coq_ex_skills.coq_SkillSet -> 'a1) -> 'a1 -> (coq_NodeKind -> char list ->
    btree -> 'a1 -> btree -> 'a1 -> 'a1) -> (coq_DecKind -> char list -> btree ->
    'a1 -> 'a1) -> btree -> 'a1

  val btree_rec :
    (Coq_ex_skills.coq_SkillSet -> 'a1) -> 'a1 -> (coq_NodeKind -> char list ->
    btree -> 'a1 -> btree -> 'a1 -> 'a1) -> (coq_DecKind -> char list -> btree ->
    'a1 -> 'a1) -> btree -> 'a1

  val count_leaves : btree -> int

  val coq_RootName : btree -> char list

  val bt_input_type : simp_type_spec

  val bt_output_type : type_spec

  val boiler_tick_generator : smv_module

  val boiler_skill : smv_module

  val boiler_TRUE : smv_module

  val boiler_sequence : smv_module

  val boiler_fallback : smv_module

  val boiler_par1 : smv_module

  val boiler_par2 : smv_module

  val boiler_not : smv_module

  val boiler_isRunning : smv_module

  val nodename : coq_NodeKind -> char list

  val decname : coq_DecKind -> char list

  val make_vars : btree -> varlist

  val make_main : btree -> smv_module

  val make_spec : btree -> smv_module list
 end

val sc1 : Coq_bts1.btree
