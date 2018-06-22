Require Import bt shallow.

(* Some simple examples of BTs *)

Inductive my_skills :=
  sk1 | sk2 | sk3 | sk4.

Module ex_skills.

  Definition SkillSet := my_skills.

End ex_skills.

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

Definition ex5 :=                       (* not *)
  (node Sequence (Skill sk1)
        (dec Not (node Parallel1 (Skill sk2) (Skill sk3)))).

Definition sc1 :=                  (* a BT similar to the one from scenario 1 *)
  (node Fallback (Skill sk1)
        (node Sequence (Skill sk2)
              (node Sequence (Skill sk3) (Skill sk4)))).

Compute count_leaves sc1. 

(* execution examples *)

Compute (tick ex4).

Compute (tick sc1 (fun s: my_skills =>
                     match s with
                     | sk1 => Succ
                     | sk2 => Succ
                     | sk3 => Fail
                     | sk4 => Succ
                     end)).

Compute (tick ex5 (fun s: my_skills =>
                     match s with
                     | sk1 => Succ
                     | sk2 => Succ
                     | sk3 => Fail
                     | sk4 => Fail
                     end)).

(* Examples with stream semantics *)

Require Import Streams stream.

Module alt_sem := BT_bin_str_sem ex_skills.

Import alt_sem.

CoFixpoint EverythingFails: Stream skills_input :=
  Cons (fun s: my_skills =>
          match s with
          | sk1 => Fail
          | sk2 => Fail
          | sk3 => Fail
          | sk4 => Fail
          end)
       EverythingFails.

CoFixpoint all_ok: Stream skills_input :=
  Cons (fun s: my_skills =>
          match s with
          | sk1 => Succ
          | sk2 => Succ
          | sk3 => Succ
          | sk4 => Succ
          end)
       all_ok.

Definition s1 :=
  Cons (fun s: my_skills =>
          match s with
          | sk1 => Runn
          | sk2 => Fail
          | sk3 => Fail
          | sk4 => Succ
          end)
       (Cons (fun s: my_skills =>
                match s with
                | sk1 => Succ
                | sk2 => Fail
                | sk3 => Fail
                | sk4 => Succ
                end)
             (Cons (fun s: my_skills =>
                      match s with
                      | sk1 => Succ
                      | sk2 => Runn
                      | sk3 => Fail
                      | sk4 => Succ
                      end)
                   (Cons (fun s: my_skills =>
                            match s with
                            | sk1 => Succ
                            | sk2 => Succ
                            | sk3 => Fail
                            | sk4 => Succ
                            end)
                         (Cons (fun s: my_skills =>
                                  match s with
                                  | sk1 => Succ
                                  | sk2 => Succ
                                  | sk3 => Fail
                                  | sk4 => Succ
                                  end)
                               (Cons (fun s: my_skills =>
                                        match s with
                                        | sk1 => Succ
                                        | sk2 => Succ
                                        | sk3 => Fail
                                        | sk4 => Succ
                                        end)
                               all_ok))))).

Compute reptick (node Fallback (Skill sk2) (Skill sk3))
        3 s1.

Compute tick2 (node Sequence (Skill sk1)
                    (node Sequence (Skill sk2) (Skill sk3)))
        s1.

Compute reptick (node Sequence (Skill sk1)
                      (node Sequence (Skill sk2) (Skill sk3)))
        3 s1.


