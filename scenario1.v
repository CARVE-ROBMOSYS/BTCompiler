Require Import bt micro_smv spec_extr bt2spec.
Require Import List String.
Open Scope string_scope.
Require Import Extraction.
Require ExtrOcamlBasic ExtrOcamlString.
Extract Inductive nat => "int" ["0" "succ"]
                               "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Constant plus => "( + )".
Extract Constant mult => "( * )".
(* Extract Constant beq_nat => "( = )".*)

Inductive my_skills :=
  sk1 | sk2 | sk3 | sk4.
Definition my_names (x: my_skills) :=
  match x with
  | sk1 => "goto_kitchen"
  | sk2 => "find_bottle"
  | sk3 => "fetch_bottle"
  | sk4 => "ask_help"
  end.

Module ex_skills.
  Definition SkillSet := my_skills.
  Definition SkillName := my_names.
End ex_skills.

Module bts1 := BT_bin_spec ex_skills.
Import bts1.

Definition sc1 :=
  (node Fallback "do_with_help"
        (node Sequence "go_and_fetch_bottle" (Skill sk1)
              (node Sequence "find_and_fetch_bottle" (Skill sk2) (Skill sk3)))
        (Skill sk4)).

(*Compute translate_spec (make_spec sc1).*)

Extraction "sc1.ml" sc1 make_spec translate_spec.

