(* deep embedding of a subset of the SMV specification language into Coq *)

Require Import List String.

(* terminals *)
Definition symbolic_constant := string.
Definition identifier := string.
(* integer constants will be treated as symbols (i.e., strings) *)
Inductive bool_constant := FALSE | TRUE.

Inductive qualid :=
| Id: identifier -> qualid
| Mod: identifier -> qualid -> qualid.

(* syntax of simple expressions *)
Inductive sexp :=
| BConst: bool_constant -> sexp
| SConst: symbolic_constant -> sexp
| Qual: qualid -> sexp
| Paren: sexp -> sexp
| Not: sexp -> sexp
| And: sexp -> sexp -> sexp
| Equal: sexp -> sexp -> sexp
| Less: sexp -> sexp -> sexp
| Sum: sexp -> sexp -> sexp
| Count: sexplist -> sexp
| Case: scexp -> sexp
with sexplist :=
     | Sexp: sexp -> sexplist
     | AddSexp: sexp -> sexplist -> sexplist
with scexp :=
     | Cexp: sexp -> sexp -> scexp
     | AddCexp: sexp -> sexp -> scexp -> scexp.

(* for simplicity, next expressions are constrained to a single application
   of the next operator ("basic next expression") to a simple expression *)
Inductive nexp :=
| Simple: sexp -> nexp
| Basic: sexp -> nexp.

(* type specifiers; we only model booleans and symbolic enums *)
Inductive simp_type_spec :=
| TBool: simp_type_spec
| TEnum: list symbolic_constant -> simp_type_spec.

Inductive param_list :=
| LastP: nexp -> param_list
| AddP: nexp -> param_list -> param_list.

Inductive mod_type_spec :=
| TMod: identifier -> mod_type_spec
| TModPar: identifier -> param_list -> mod_type_spec.

Inductive type_spec :=
| TSimp: simp_type_spec -> type_spec
| TComp: mod_type_spec -> type_spec.

(* variable declarations *)
Inductive varlist :=
| LastV: identifier -> type_spec -> varlist
| AddV: identifier -> type_spec -> varlist -> varlist.

Inductive ivarlist :=
| LastI: identifier -> simp_type_spec -> ivarlist
| AddI: identifier -> simp_type_spec -> ivarlist -> ivarlist.

(* define declarations *)
Inductive deflist :=
| LastD: identifier -> sexp -> deflist
| AddD: identifier -> sexp -> deflist -> deflist.

(* assign constraints *)
Inductive assign_cons :=
| invar: qualid -> sexp -> assign_cons
| init: qualid -> sexp -> assign_cons
| next: qualid -> nexp -> assign_cons.

Inductive asslist :=
| LastA: assign_cons -> asslist
| AddA: assign_cons -> asslist -> asslist.

(* general element of an SMV module *)
Inductive smv_element :=
| VAR: varlist -> smv_element
| IVAR: ivarlist -> smv_element
| DEFINE: deflist -> smv_element
| ASSIGN: asslist -> smv_element.

Record smv_module: Set :=
  {name: identifier;
   params: list identifier;
   body: list smv_element}.

Definition smv_spec := list smv_module.

(* Utility functions *)

Fixpoint varlist_app (a b: varlist) :=
  match a with
  | LastV v t => AddV v t b
  | AddV v t c => AddV v t (varlist_app c b)
  end.
