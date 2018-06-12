Require Import bt.

(* Some simple examples of BTs *)

Inductive my_skills :=
  sk1 | sk2 | sk3 | sk4.

Module bt_ex.

  Definition SkillSet := my_skills.

End bt_ex.

Module my_bt := BT_binary bt_ex.

Import my_bt. (* short names available *)

Definition ex1 := (Skill sk1).          (* a node *)

Definition ex2 :=                       (* sequence *)
  (node Sequence (Skill sk1)
        (node Sequence (Skill sk2) (Skill sk3))).

Definition ex3 :=                       (* fallback *)
  (node Fallback (Skill sk3) (Skill sk4)).

Definition ex4 :=                       (* parallel *)
  (node Parallel1 (Skill sk1)
        (node Parallel1 (Skill sk2) (Skill sk3))).

Definition ex6 :=                  (* a BT similar to the one from scenario 1 *)
  (node Fallback (Skill sk1)
        (node Sequence (Skill sk2)
              (node Sequence (Skill sk3) (Skill sk4)))).

Compute count_leaves ex6.
  

