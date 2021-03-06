Require Import bt basic.
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

Module my_bin_bt_with_sem := BT_bin_semantics ex_skills.

Import my_bin_bt_with_sem.

Definition sc1 :=
  (Node Fallback "do_with_help"
        (Node Sequence "go_and_fetch" (Skill sk1)
              (Node Sequence "find_and_fetch" (Skill sk2) (Skill sk3)))
        (Skill sk4)).

(* execution examples *)

Compute (tick sc1 (fun s: my_skills =>
                     match s with
                     | sk1 => Succ
                     | sk2 => Succ
                     | sk3 => Fail
                     | sk4 => Succ
                     end)).

Compute (tick sc1 (fun s: my_skills =>
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

Compute reptick (Node Fallback "prova" (Skill sk2) (Skill sk3))
        3 s1.

Compute tick2 (Node Sequence "s1" (Skill sk1)
                    (Node Sequence "s2" (Skill sk2) (Skill sk3)))
        s1.

Compute reptick (Node Sequence "s1" (Skill sk1)
                      (Node Sequence "s2" (Skill sk2) (Skill sk3)))
        3 s1.

(* SMV specifications *)

Require Import spec_extr bt2spec.

Module spec := BT_bin_spec ex_skills.

Import spec.

Definition uc1 :=
  (Node Fallback "do_with_help"
        (Node Sequence "go_and_fetch" (Skill sk1)
              (Node Sequence "find_and_fetch" (Skill sk2) (Skill sk3)))
        (Skill sk4)).

Compute translate_spec (make_spec uc1).


