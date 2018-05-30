(*** Definition of Behaviour Trees as an abstract data type ***)

(* An abstraction for skills; may be altered later, once we know precisely
   how skills are specified... *)

Parameter SkillSet: Set.
Parameter sk1 sk2 sk3: SkillSet.

(* Definition of the BT type as a tree with arbitrary (but finite) branching,
   in mutual induction style *)

Inductive btree: Set :=
  | Sequence: btlist -> btree
  | Fallback: btlist -> btree
  | Parallel: nat -> btlist -> btree
(*  | Decorator: DecKind -> btree -> btree *)
  | Skill: SkillSet -> btree
with btlist: Set :=
  | fnil: btlist
  | fcons: btree -> btlist -> btlist.

(* Instantiation of the correct mutual induction principles *)

Scheme btree_mind := Induction for btree Sort Prop
with btlist_mind := Induction for btlist Sort Prop.

(*
btree_mind: forall (P : btree -> Prop) (P0 : btlist -> Prop),
  (forall b : btlist, P0 b -> P (Sequence b)) ->
  (forall b : btlist, P0 b -> P (Fallback b)) ->
  (forall (n : nat) (b : btlist), P0 b -> P (Parallel n b)) ->
  (forall s : SkillSet, P (Skill s)) ->
  P0 fnil ->
  (forall b : btree, P b -> forall b0 : btlist, P0 b0 -> P0 (fcons b b0)) ->
  forall b : btree, P b 

btlist_mind: forall (P : btree -> Prop) (P0 : btlist -> Prop),
  (forall b : btlist, P0 b -> P (Sequence b)) ->
  (forall b : btlist, P0 b -> P (Fallback b)) ->
  (forall (n : nat) (b : btlist), P0 b -> P (Parallel n b)) ->
  (forall s : SkillSet, P (Skill s)) ->
  P0 fnil ->
  (forall b : btree, P b -> forall b0 : btlist, P0 b0 -> P0 (fcons b b0)) ->
  forall b : btlist, P0 b
 *)


(* Some simple examples of BTs *)
Definition ex1 := (Skill sk1).          (* a node *)

Definition ex2 :=                       (* sequence *)
  (Sequence (fcons (Skill sk1)
                   (fcons (Skill sk2)
                          (fcons (Skill sk3) fnil)))).

Definition ex3 :=                       (* fallback *)
  (Fallback (fcons (Skill sk1)
                   (fcons (Skill sk2) fnil))).

Definition ex4 :=                       (* parallel *)
  (Parallel 1 (fcons (Skill sk1)
                     (fcons (Skill sk2)
                            (fcons (Skill sk3) fnil)))).

(* By convention, if the argument of a parallel node is greater than 
   the length of the corresponding forest, the argument will be "truncated" 
   at the said length. So for instance: *)
Definition ex5 :=
  (Parallel 3 (fcons (Skill sk1)
                     (fcons (Skill sk2) fnil))).
(* will be interpreted as Parallel 2 (...) *)

Definition ex6 :=                  (* a BT similar to the one from scenario 1 *)
  (Fallback (fcons (Skill sk1)
                   (fcons (Sequence (fcons (Skill sk1)
                                           (fcons (Skill sk2)
                                                  (fcons (Skill sk3) fnil))))
                          fnil))).

(* We could also replace the Parallel constructor with a dependent constructor
   of the form
   Parallel (k: nat) (l: btlist) (p: k <= (len l)) : btree
   but such a solution seems overkill at the moment. *)

(* Possible Decorator nodes (as per ALES draft):
   Succeed
   Not
   Is_running
   Is_enabled *)

(* Utility functions *)

Fixpoint len (f: btlist) :=
  match f with
  | fnil => 0
  | fcons t tl => 1 + (len tl)
  end.

Fixpoint count_leaves (t: btree) :=
  match t with
  | Skill s => 1
  | Sequence f => cl_forest f
  | Fallback f => cl_forest f
  | Parallel n f => cl_forest f
  end
with cl_forest (f: btlist) :=
  match f with
  | fnil => 0
  | fcons t tl => count_leaves t + cl_forest tl
  end.

Compute count_leaves ex6.



