Require Import bt shallow.

(* Some simple examples of BTs *)

Inductive my_skills :=
  sk1 | sk2 | sk3 | sk4.

Module ex_skills.

  Definition SkillSet := my_skills.

End ex_skills.

(*
Module my_binary_bt := BT_binary ex_skills.

Import my_binary_bt. (* makes short names available *)

Definition ex1 := (Skill sk1).          (* a node *)

Definition ex2 :=                       (* sequence *)
  (node Sequence (Skill sk1)
        (node Sequence (Skill sk2) (Skill sk3))).

Definition ex3 :=                       (* fallback *)
  (node Fallback (Skill sk3) (Skill sk4)).

Definition ex4 :=                       (* parallel *)
  (node Parallel1 (Skill sk1)
        (node Parallel1 (Skill sk2) (Skill sk3))).

Definition sc1 :=                  (* a BT similar to the one from scenario 1 *)
  (node Fallback (Skill sk1)
        (node Sequence (Skill sk2)
              (node Sequence (Skill sk3) (Skill sk4)))).

Compute count_leaves sc1. 
 *)

Module my_bin_bt_with_sem := BT_bin_semantics ex_skills.

Import my_bin_bt_with_sem.

Definition ex1 := (Skill sk1).          (* a node *)

Definition ex2 :=                       (* sequence *)
  (node Sequence (Skill sk1)
        (node Sequence (Skill sk2) (Skill sk3))).

Definition ex3 :=                       (* fallback *)
  (node Fallback (Skill sk3) (Skill sk4)).

Definition ex4 :=                       (* parallel *)
  (node Parallel1 (Skill sk1)
        (node Parallel1 (Skill sk2) (Skill sk3))).

Definition sc1 :=                  (* a BT similar to the one from scenario 1 *)
  (node Fallback (Skill sk1)
        (node Sequence (Skill sk2)
              (node Sequence (Skill sk3) (Skill sk4)))).

Compute (tick ex1).
Compute (tick ex2).
Compute (tick ex3).
Compute (tick ex4).
Compute (tick sc1).
