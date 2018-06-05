(*** Definition of Behaviour Trees as an abstract data type ***)

(* An abstraction for skills; may be altered later, once we know precisely
   how skills are specified... *)

Parameter SkillSet: Set.
Parameter sk1 sk2 sk3: SkillSet.

(* Definition of the BT type as a tree with arbitrary (but finite) nonzero
   branching, in mutual induction style. Leaves are labeled by an element of
   the set Skillset. *)

Inductive btree: Set :=
  | Skill: SkillSet -> btree
  | Sequence: btforest -> btree
  | Fallback: btforest -> btree
  | Parallel: nat -> btforest -> btree
(*  | Decorator: DecKind -> btree -> btree *)
with btforest: Set :=
  | child: btree -> btforest              (* a forest has at least one tree *)
  | add: btree -> btforest -> btforest.

(* Instantiation of the correct mutual induction principles *)

Scheme btree_mind := Induction for btree Sort Prop
with btforest_mind := Induction for btforest Sort Prop.


(* Some simple examples of BTs *)
Definition ex1 := (Skill sk1).          (* a node *)

Definition ex2 :=                       (* a ternary sequence *)
  (Sequence (add (Skill sk1)
                 (add (Skill sk2)
                      (child (Skill sk3))))).

Definition ex3 :=                       (* a binary fallback *)
  (Fallback (add (Skill sk1)
                 (child (Skill sk2)))).

Definition ex4 :=                       (* a ternary parallel *)
  (Parallel 1 (add (Skill sk1)
                   (add (Skill sk2)
                        (child (Skill sk3))))).

(* With the above definition, the argument of a parallel node can be greater
   than the number of children. This is arguably ill-formed, and will be 
   detected at compile time *)

Definition ex5 :=                       (* faulty parallel *)
  (Parallel 3 (add (Skill sk1)
                   (child (Skill sk2)))).

Definition ex6 :=                  (* a BT similar to the one from scenario 1 *)
  (Fallback (add (Sequence (add (Skill sk1)
                                (add (Skill sk2)
                                     (child (Skill sk3)))))
                 (child (Skill sk1)))).

(* We could also replace the Parallel constructor with a dependent constructor
   of the form
   Parallel (k: nat) (l: btforest) (p: k <= (n_of_children l)): btree
   but such a solution seems overkill at the moment. *)

(* Possible Decorator nodes (as per ALES draft):
   Succeed
   Not
   Is_running
   Is_enabled *)

(* Utility functions *)

Fixpoint n_of_children (f: btforest) :=
  match f with
  | child t => 1
  | add t tl => 1 + (n_of_children tl)
  end.

Fixpoint count_leaves (t: btree) :=
  match t with
  | Skill s => 1
  | Sequence f => cl_forest f
  | Fallback f => cl_forest f
  | Parallel n f => cl_forest f
  end
with cl_forest (f: btforest) :=
  match f with
  | child t => count_leaves t
  | add t tl => count_leaves t + cl_forest tl
  end.

Compute count_leaves ex6.

(* The following function replaces inner nodes with a single child with the
   child tree itself. We could prove later that this operation does not alter
   the semantics of the BT. *)

Fixpoint normalize (t: btree) :=
  match t with
  | Skill s => Skill s
  | Sequence f => match f with
                  | child t => t
                  | _ => Sequence (normalize_forest f)
                  end
  | Fallback f => match f with
                  | child t => t
                  | _ => Fallback (normalize_forest f)
                  end
  | Parallel n f => match f with
                    | child t => t
                    | _ => Parallel n (normalize_forest f)
                    end
  end
with normalize_forest (f: btforest) :=
       match f with
       | child t => child (normalize t)
       | add t ts => add (normalize t) (normalize_forest ts)
       end.

(* let us test it on a "truncated" version of the BT for scenario 2: *)
Definition ex7 :=
  (Fallback (add (Sequence (add (Fallback (child (Skill sk1)))
                                (add (Skill sk1)
                                     (child (Skill sk2)))))
                 (child (Skill sk1)))).

Compute normalize ex7.


    


