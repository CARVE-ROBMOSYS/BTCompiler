Require Import bt shallow.
Require Import String.
Open Scope string_scope.

(* Some simple examples of BTs *)

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

  Definition skillSet := my_skills.
  Definition skillName := my_names.

End ex_skills.

Module my_bt := BT_gen_semantics ex_skills.

Import my_bt.

Definition ex1 := (Skill sk1).          (* a skill *)

Definition ex2 :=                       (* a ternary sequence *)
  (Node Sequence "seq3" (Add (Skill sk1)
                             (Add (Skill sk2)
                                  (Child (Skill sk3))))).

Definition ex3 :=                       (* a binary fallback *)
  (Node Fallback "bf" (Add (Skill sk1)
                           (Child (Skill sk2)))).

Definition ex4 :=                       (* a ternary parallel *)
  (Node (Parallel 1) "par" (Add (Skill sk1)
                                (Add (Skill sk2)
                                     (Child (Skill sk3))))).

Definition ex5 :=                       (* ill-formed parallel *)
  (Node (Parallel 3) "nopar" (Add (Skill sk1)
                                  (Child (Skill sk2)))).

Definition sc1 :=                  (* a BT similar to the one from scenario 1 *)
  (Node Fallback "do_with_help"
        (Add (Node Sequence "go_find_fetch" (Add (Skill sk1)
                                                 (Add (Skill sk2)
                                                      (Child (Skill sk3)))))
             (Child (Skill sk4)))).

Compute count_skills sc1.

(* mangled version of sc1, to test normalization *)

Definition sc1m :=
  (Node Fallback "do_with_help"
        (Add (Node Sequence "go_find_fetch"
                   (Add (Node Fallback "useless" (Child (Skill sk1)))
                        (Add (Skill sk2)
                             (Child (Node Sequence "useless2" (Child (Skill sk3)))))))
             (Child (Skill sk4)))).

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
                                  | sk3 => Runn
                                  | sk4 => Succ
                                  end)
                               (Cons (fun s: my_skills =>
                                        match s with
                                        | sk1 => Succ
                                        | sk2 => Succ
                                        | sk3 => Succ
                                        | sk4 => Succ
                                        end)
                               all_ok))))).

Compute reptick (Node Sequence "prova" (Add (Skill sk1)
                                            (Add (Skill sk2)
                                                 (Child (Skill sk3)))))
        3 s1.

