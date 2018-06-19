Require Import bt shallow.

(* Some simple examples of BTs *)

Inductive my_skills :=
  sk1 | sk2 | sk3 | sk4.

Module ex_skills.

  Definition SkillSet := my_skills.

End ex_skills.

Module my_bt := BT_gen_semantics ex_skills.

Import my_bt. (* makes short names available *)

Definition ex1 := (Skill sk1).          (* a node *)

Definition ex2 :=                       (* a ternary sequence *)
  (node Sequence (add (Skill sk1)
                      (add (Skill sk2)
                           (child (Skill sk3))))).

Definition ex3 :=                       (* a binary fallback *)
  (node Fallback (add (Skill sk1)
                 (child (Skill sk2)))).

Definition ex4 :=                       (* a ternary parallel *)
  (node (Parallel 1) (add (Skill sk1)
                          (add (Skill sk2)
                               (child (Skill sk3))))).

Definition ex5 :=                       (* ill-formed parallel *)
  (node (Parallel 3) (add (Skill sk1)
                          (child (Skill sk2)))).

Definition sc1 :=                  (* a BT similar to the one from scenario 1 *)
  (node Fallback (add (node Sequence (add (Skill sk1)
                                          (add (Skill sk2)
                                               (child (Skill sk3)))))
                      (child (Skill sk4)))).

Compute count_leaves sc1.

(* mangled version of sc1, to test normalization *)

Definition sc1m :=
  (node Fallback (add (node Sequence (add (node Fallback (child (Skill sk1)))
                                          (add (Skill sk2)
                                               (child (node Sequence (child (Skill sk3)))))))
                      (child (Skill sk4)))).

Compute normalize sc1m.

(* execution examples *)

Compute (tick ex4).
(* current implementation will happily run on this ill-formed BT... *)
Compute (tick ex5).

Compute (tick sc1 (fun s: my_skills =>
                     match s with
                     | sk1 => Succ
                     | sk2 => Succ
                     | sk3 => Fail
                     | sk4 => Succ
                     end)).

(* Examples with stream semantics *)

Require Import Streams stream.

Module alt_sem := BT_gen_str_sem ex_skills.

Import alt_sem.

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
          | sk1 => Succ
          | sk2 => Succ
          | sk3 => Succ
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
                      | sk2 => Runn
                      | sk3 => Succ
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

Compute tick (node Sequence (add (Skill sk1)
                                 (add (Skill sk2) (child (Skill sk3)))))
        s1.




