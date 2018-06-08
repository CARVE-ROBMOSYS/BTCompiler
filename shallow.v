
(* In this file we realize the operational semantics for BTs as programs
   specified in the Gallina language. In other words, we define a
   shallow embedding of the BT language in the type theory used by Coq.

   This is the version for BTs with binary nodes only. *)

Load "bt3.v".

Inductive return_enum := Runn | Fail | Succ.

Definition skills_input := SkillSet -> return_enum.
(* A term of this type encapsulates a returns value for each skill. *)

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
                    | Parallel1 => Fail
                    | Parallel2 => Fail
                    end
  end.

Definition return_same_value (a: btree) (b: btree): Prop :=
  forall i: skills_input, (tick a i) = (tick b i).

Theorem sequence_associativity:
  forall c_1 c_2 c_3: btree,
    let a := (node Sequence (node Sequence c_1 c_2) c_3) in
    let b := (node Sequence c_1 (node Sequence c_2 c_3)) in
    return_same_value a b.
Proof.
  unfold return_same_value.
  intros.
  simpl.
  destruct (tick c_1); auto.
Qed.  

Theorem fallback_associativity:
  forall c_1 c_2 c_3: btree,
    let a := (node Fallback (node Fallback c_1 c_2) c_3) in
    let b := (node Fallback c_1 (node Fallback c_2 c_3)) in
    return_same_value a b.
Proof.
  unfold return_same_value.
  intros.
  simpl.
  destruct (tick c_1); auto.
Qed.  



