
(* In this file we realize the operational semantics for BTs as programs
   specified in the Gallina language. In other words, we define a
   shallow embedding of the BT language in the type theory used by Coq. *)

Require Import bt.

(* Version for BTs with binary nodes only. *)

Module BT_bin_semantics (X: BT_SIG).

  Include BT_binary X.

  Inductive return_enum := Runn | Fail | Succ.

  Definition skills_input := X.SkillSet -> return_enum.
  (* A term of this type encapsulates a returns value for each skill
     at the instant of time in which the tick is executed. *)

  Fixpoint tick (t: btree) (input_f: skills_input) :=
    match t with
    | Skill s => input_f s
    | node k t1 t2 => match k with
                      | Sequence =>
                        match (tick t1 input_f) with
                        | Runn => Runn
                        | Fail => Fail
                        | Succ => (tick t2 input_f)
                        end
                      | Fallback =>
                        match (tick t1 input_f) with
                        | Runn => Runn
                        | Fail => (tick t2 input_f)
                        | Succ => Succ
                        end
                      | Parallel1 =>
                        let a := tick t1 input_f in
                        let b := tick t2 input_f in
                        match a , b with
                        | Succ , _ => Succ
                        | _ , Succ => Succ
                        | Fail , Fail => Fail
                        | _ , _ => Runn
                        end
                      | Parallel2 =>
                        let a := tick t1 input_f in
                        let b := tick t2 input_f in
                        match a , b with
                        | Succ , Succ => Succ
                        | Fail , _ => Fail
                        | _ , Fail => Fail
                        | _ , _ => Runn
                        end
                      end
    end.

  Definition return_same_value (a: btree) (b: btree): Prop :=
    forall i: skills_input, (tick a i) = (tick b i).

  Theorem all_nodes_are_associative:
    forall k: NodeKind,
    forall c_1 c_2 c_3: btree,
      let a := (node k (node k c_1 c_2) c_3) in
      let b := (node k c_1 (node k c_2 c_3)) in
      return_same_value a b.
  Proof.
    unfold return_same_value.
    intros.
    induction k.
    - simpl.
      destruct (tick c_1); auto.
    - simpl.
      destruct (tick c_1); auto.
    - simpl.
      destruct (tick c_1); destruct (tick c_2); destruct (tick c_3); auto.
    - simpl.
      destruct (tick c_1); destruct (tick c_2); destruct (tick c_3); auto.
  Qed.

End BT_bin_semantics.



