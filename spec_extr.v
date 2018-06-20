(* Extraction of a micro-SMV specification from an embedded one *)

Require Import List String.
Require Import bt micro_smv.
Open Scope string_scope.

Definition newline := String "010" EmptyString.

Fixpoint translate_sexp (e: sexp) : string :=
  match e with
(* base cases *)
  | BConst bc => match bc with
                 | TRUE => "TRUE"
                 | FALSE => "FALSE"
                 end
  | SConst sc => sc
  | Ident i => i
(* inductive cases *)
  | Paren e' => "(" ++ translate_sexp e' ++ ")"
  | Not e' => "! " ++ translate_sexp e'
  | And e' e'' => translate_sexp e' ++ " & " ++ translate_sexp e''
  | Equal e' e'' => translate_sexp e' ++ " = " ++ translate_sexp e''
  | Less e' e'' => translate_sexp e' ++ " < " ++ translate_sexp e''
  | Sum e' e'' => translate_sexp e' ++ " + " ++ translate_sexp e''
  | Count lst => "count(" ++ translate_sexplist lst ++ ")"
  | Case ce => "case" ++ newline ++ translate_cexp ce ++ "esac"
  end
with translate_sexplist (l: sexplist): string :=
  match l with
  | Sexp e => translate_sexp e
  | AddSexp e rest => translate_sexp e ++ ", " ++ translate_sexplist rest
  end
with translate_cexp (c: scexp): string :=
  match c with
  | Cexp e1 e2 => translate_sexp e1 ++ " : " ++ translate_sexp e2 ++ ";"
                  ++ newline
  | AddCexp e1 e2 rest => translate_sexp e1 ++ " : " ++ translate_sexp e2
                          ++ ";" ++ newline ++ translate_cexp rest
  end.

Definition translate_nexp (e: nexp) :=
  match e with
  | Simple e' => translate_sexp e'
  | Basic e' => "next(" ++ translate_sexp e' ++ ")"
  end.

Definition translate_type_spec (t: type_spec) :=
  match t with
  | TBool => "boolean"
  | TEnum values => "{ " ++ concat ", " values ++ " }"
  end.

Fixpoint translate_varlist (vl: varlist) :=
  match vl with
  | LastV id ty => id ++ " : " ++ translate_type_spec ty ++ ";" ++ newline
  | AddV id ty rest => id ++ " : " ++ translate_type_spec ty ++ ";" ++ newline
                       ++ translate_varlist rest
  end.

Fixpoint translate_ivarlist (il: ivarlist) :=
  match il with
  | LastI id ty => id ++ " : " ++ translate_type_spec ty ++ ";" ++ newline
  | AddI id ty rest => id ++ " : " ++ translate_type_spec ty ++ ";" ++ newline
                       ++ translate_ivarlist rest
  end.

Fixpoint translate_deflist (dl: deflist) :=
  match dl with
  | LastD id e => id ++ " := " ++ translate_sexp e ++ ";" ++ newline
  | AddD id e rest => id ++ " := " ++ translate_sexp e ++ ";" ++ newline
                      ++ translate_deflist rest
  end.

Definition translate_assign_cons (c: assign_cons) :=
  match c with
  | invar id e => id ++ " := " ++ translate_sexp e ++ ";" ++ newline
  | init id e => "init(" ++ id ++ ") := " ++ translate_sexp e ++ ";" ++ newline
  | next id ne => "next(" ++ id ++ ") := " ++ translate_nexp ne ++ ";" ++ newline
  end.

Fixpoint translate_asslist (al: asslist) :=
  match al with
  | LastA c => translate_assign_cons c
  | AddA c rest => translate_assign_cons c ++ translate_asslist rest
  end.

Definition translate_smv_element (e: smv_element) :=
  match e with
  | VAR vl => "VAR" ++ newline ++ translate_varlist vl
  | IVAR il => "IVAR" ++ newline ++ translate_ivarlist il
  | DEFINE dl => "DEFINE" ++ newline ++ translate_deflist dl
  | ASSIGN al => "ASSIGN" ++ newline ++ translate_asslist al
  end.

Fixpoint translate (m: smv_module) :=
  match m with
  | nil => ""
  | cons e rest => translate_smv_element e ++ translate rest
  end.

(* examples *)

Definition skill :=
  (IVAR (LastI "input" (TEnum ("runn"::"fail"::"succ"::nil))))
  ::
  (VAR (LastV "output" (TEnum ("none"::"running"::"failed"::"succeeded"::nil))))
  ::
  (ASSIGN (AddA (init "output" (SConst "none"))
                (LastA (next "output" (Simple (Case
                                                 (AddCexp (Equal (Ident "input") (SConst "runn"))
                                                          (SConst "running")
                                                          (AddCexp (Equal (Ident "input") (SConst "fail"))
                                                                   (SConst "failed")
                                                                   (Cexp (Equal (Ident "input") (SConst "succ"))
                                                                         (SConst "succeeded"))))))))))
  ::nil.

Compute translate skill.



Definition prova1 :=
  (VAR (AddV "state" (TEnum ("ready"::"busy"::nil)) (LastV "request" TBool)))
    ::
    (ASSIGN
       (AddA (init "state" (SConst "ready"))
             (LastA (next "state"
                          (Simple (Case
                                     (AddCexp (And (Equal (Ident "state") (SConst "ready"))
                                                   (Equal (Ident "request") (BConst TRUE)))
                                              (SConst "busy")
                                              (Cexp (BConst TRUE)
                                                    (SConst "ready"))))))))) :: nil.

Compute translate prova1.



(* program extraction *)

Require Import Extraction.
Require ExtrOcamlBasic ExtrOcamlString.

(*
Extract Inductive nat => "int" ["0" "succ"]
                               "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
Extract Constant beq_nat => "( = )".
*)

(* Extraction "spec_extr" translate. *)

