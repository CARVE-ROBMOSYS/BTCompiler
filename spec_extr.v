(* Extraction of a micro-SMV specification from an embedded one *)

Require Import List String.
Require Import bt micro_smv.
Open Scope string_scope.

Definition newline := String "010" EmptyString.

Fixpoint translate_qualid (q: qualid) :=
  match q with
  | Id i => i
  | Mod m q' => m ++ "." ++ translate_qualid q'
  end.

Fixpoint translate_sexp (e: sexp) : string :=
  match e with
(* base cases *)
  | BConst bc => match bc with
                 | smvT => "TRUE"
                 | smvF => "FALSE"
                 end
  | SConst sc => sc
  | Qual q => translate_qualid q
(* inductive cases *)
  | Paren e' => "(" ++ translate_sexp e' ++ ")"
  | Neg e' => "!(" ++ translate_sexp e' ++ ")"
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

Definition translate_simp_type_spec (t: simp_type_spec) :=
  match t with
  | TBool => "boolean"
  | TEnum values => "{ " ++ concat ", " values ++ " }"
  end.

Fixpoint translate_param_list (pl: param_list) :=
  match pl with
  | LastP e => translate_nexp e
  | AddP e pl' => translate_nexp e ++ ", " ++ translate_param_list pl'
  end.

Fixpoint translate_mod_type_spec (m: mod_type_spec) :=
  match m with
  | TMod i => i
  | TModPar i pl => i ++ "(" ++ translate_param_list pl ++ ")"
  end.

Definition translate_type_spec (t: type_spec) :=
  match t with
  | TSimp sts => translate_simp_type_spec sts
  | TComp mts => translate_mod_type_spec mts
  end.

Fixpoint translate_varlist (vl: varlist) :=
  match vl with
  | LastV id ty => id ++ " : " ++ translate_type_spec ty ++ ";" ++ newline
  | AddV id ty rest => id ++ " : " ++ translate_type_spec ty ++ ";" ++ newline
                       ++ translate_varlist rest
  end.

Fixpoint translate_ivarlist (il: ivarlist) :=
  match il with
  | LastI id ty => id ++ " : " ++ translate_simp_type_spec ty ++ ";" ++ newline
  | AddI id ty rest => id ++ " : " ++ translate_simp_type_spec ty ++ ";" ++ newline
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
  | invar q e => translate_qualid q ++ " := " ++ translate_sexp e ++ ";" ++ newline
  | init q e => "init(" ++ translate_qualid q ++ ") := " ++ translate_sexp e ++ ";" ++ newline
  | next q ne => "next(" ++ translate_qualid q ++ ") := " ++ translate_nexp ne ++ ";" ++ newline
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

Fixpoint translate_body (b: list smv_element) :=
  match b with
  | nil => ""
  | cons e rest => translate_smv_element e ++ translate_body rest
  end.

Definition translate (m: smv_module) :=
  "MODULE " ++ (name m) ++ "(" ++ concat ", " (params m) ++ ")" ++ newline
  ++ translate_body (body m) ++ newline.

Fixpoint translate_spec (f: smv_spec) :=
  match f with
  | nil => ""
  | cons m rest => translate m ++ translate_spec rest
  end.

