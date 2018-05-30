(*** Definition of Behaviour Trees as an abstract data type ***)

(* An abstraction for skills; may be altered later, once we know precisely
   how skills are specified... *)

Parameter SkillSet: Set.
Parameter sk1 sk2 sk3: SkillSet.

(* Definition of the BT type as a tree with arbitrary (but finite) branching,
   in mutual induction style *)

Inductive NodeKind: Set :=
  Sequence | Fallback | Parallel1 | Parallel2.

Inductive btree: Set :=
  | node: NodeKind -> btree -> btree -> btree
(*  | Decorator: DecKind -> btree -> btree *)
  | Skill: SkillSet -> btree.

(*
btree_ind: forall P : btree -> Prop,
  (forall (k : NodeKind) (b : btree), P b -> forall b0 : btree, P b0 -> P (node k b b0)) ->
  (forall s : SkillSet, P (Skill s)) -> 
  forall b : btree, P b
 *)

(* Some simple examples of BTs *)
Definition ex1 := (Skill sk1).          (* a node *)

Definition ex2 :=                       (* sequence *)
  (node Sequence (Skill sk1)
        (node Sequence (Skill sk2) (Skill sk3))).

Definition ex3 :=                       (* fallback *)
  (node Fallback (Skill sk1) (Skill sk2)).

Definition ex4 :=                       (* parallel *)
  (node Parallel1 (Skill sk1)
        (node Parallel1 (Skill sk2) (Skill sk3))).

Definition ex6 :=                  (* a BT similar to the one from scenario 1 *)
  (node Fallback (Skill sk1)
        (node Sequence (Skill sk1)
              (node Sequence (Skill sk2) (Skill sk3)))).

(* Possible Decorator nodes (as per ALES draft):
   Succeed
   Not
   Is_running
   Is_enabled *)

(* Utility functions *)

Fixpoint count_leaves (t: btree) :=
  match t with
  | Skill s => 1
  | node k t1 t2 => (count_leaves t1) + (count_leaves t2)
  end.

Compute count_leaves ex6.

         


