
val app : 'a1 list -> 'a1 list -> 'a1 list

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

val translate : smv_module -> char list

val translate_spec : smv_spec -> char list

val bt_output_type : simp_type_spec

val bt_action_type : simp_type_spec

val bp_tick_generator : smv_module

val bp_skill : smv_module

val bp_TRUE : smv_module

val bp_not : smv_module

val bp_isRunning : smv_module

module BT_bin_spec :
 functor (X:BT_SIG) ->
 sig
  type nodeKind =
  | Sequence
  | Fallback
  | Parallel1
  | Parallel2

  val nodeKind_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> nodeKind -> 'a1

  val nodeKind_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> nodeKind -> 'a1

  type decKind =
  | Not
  | IsRunning

  val decKind_rect : 'a1 -> 'a1 -> decKind -> 'a1

  val decKind_rec : 'a1 -> 'a1 -> decKind -> 'a1

  type btree =
  | Skill of X.skillSet
  | TRUE
  | Node of nodeKind * char list * btree * btree
  | Dec of decKind * char list * btree

  val btree_rect :
    (X.skillSet -> 'a1) -> 'a1 -> (nodeKind -> char list -> btree -> 'a1 ->
    btree -> 'a1 -> 'a1) -> (decKind -> char list -> btree -> 'a1 -> 'a1) ->
    btree -> 'a1

  val btree_rec :
    (X.skillSet -> 'a1) -> 'a1 -> (nodeKind -> char list -> btree -> 'a1 ->
    btree -> 'a1 -> 'a1) -> (decKind -> char list -> btree -> 'a1 -> 'a1) ->
    btree -> 'a1

  val sklist : btree -> X.skillSet list

  val bp_bin_seq : smv_module

  val bp_bin_fb : smv_module

  val bp_par1 : smv_module

  val bp_par2 : smv_module

  val rootName : btree -> char list

  val nodeName : nodeKind -> char list

  val decName : decKind -> char list

  val make_vars : btree -> varlist

  val make_main : btree -> smv_module

  val mkop : X.skillSet list -> char list list

  val mkov : X.skillSet list -> varlist

  val mkot : X.skillSet list -> asslist

  val ocra_bt_fsm : btree -> smv_module

  val mkparomain : X.skillSet list -> param_list

  val mkvaromain : X.skillSet list -> varlist

  val mkdefomain : X.skillSet list -> deflist

  val ocra_main : btree -> smv_module

  val make_spec : btree -> smv_module list
 end
