(* deep embedding of a subset of the SMV specification language into Coq
   Version without modules *)

Require Import List String.

(* terminals *)
Definition symbolic_constant := string.
Definition identifier := string.
(* integer constants will be treated as symbols (i.e., strings) *)
Inductive bool_constant := FALSE | TRUE.

(* syntax of simple expressions *)
Inductive sexp :=
| BConst: bool_constant -> sexp
| SConst: symbolic_constant -> sexp
| Ident: identifier -> sexp
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
Inductive type_spec :=
| TBool: type_spec
| TEnum: list symbolic_constant -> type_spec.

(* variable declarations *)
Inductive varlist :=
| LastV: identifier -> type_spec -> varlist
| AddV: identifier -> type_spec -> varlist -> varlist.

(*Inductive ivar_stat := *)

(* define declarations *)
Inductive deflist :=
| LastD: identifier -> sexp -> deflist
| AddD: identifier -> sexp -> deflist -> deflist.

(* assign constraints *)
Inductive assign_cons :=
| invar: identifier -> sexp -> assign_cons
| init: identifier -> sexp -> assign_cons
| next: identifier -> nexp -> assign_cons.

Inductive asslist :=
| LastA: assign_cons -> asslist
| AddA: assign_cons -> asslist -> asslist.

(* general element of an SMV module *)
Inductive smv_element :=
| VAR: varlist -> smv_element
(*| IVAR: ivar_stat -> smv_element*)
| DEFINE: deflist -> smv_element
| ASSIGN: asslist -> smv_element.

Definition smv_module := list smv_element.


