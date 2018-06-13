
(* This module contains two implementations for the BT data type.
   Both are parameterized modules over the signature BT_SIG, which defines
   (for now) only a set specifying the basic skills available. *)

Module Type BT_SIG.
  
  Parameter SkillSet: Set.

End BT_SIG.

(* First implementation: trees with binary branching only *)

Module BT_binary (X: BT_SIG).
  
  Inductive NodeKind: Set :=
    Sequence | Fallback | Parallel1 | Parallel2.

  (* Inductive DecKind: Set := Not | isRunning | isEnabled | ... *)
  
  Inductive btree: Set :=
  | Skill: X.SkillSet -> btree
  | node: NodeKind -> btree -> btree -> btree.
  (*  | dec: DecKind -> btree -> btree *)

  (* Utility functions *)

  Fixpoint count_leaves (t: btree) :=
    match t with
    | Skill s => 1
    | node k t1 t2 => (count_leaves t1) + (count_leaves t2)
    end.

End BT_binary.

(* Second implementation: trees with arbitrary branching *)

Module BT_general (X: BT_SIG).

  Inductive NodeKind: Set :=
  | Sequence: NodeKind
  | Fallback: NodeKind
  | Parallel: nat -> NodeKind.

  (* Inductive DecKind: Set := Not | isRunning | isEnabled | ... *)

  Inductive btree: Set :=
  | Skill: X.SkillSet -> btree
  | node: NodeKind -> btforest -> btree
  (*  | dec: DecKind -> btree -> btree *)
  with btforest: Set :=
  | child: btree -> btforest              (* a forest has at least one tree *)
  | add: btree -> btforest -> btforest.

  (* Instantiation of the correct mutual induction principles *)

  Scheme btree_mind := Induction for btree Sort Prop
  with btforest_mind := Induction for btforest Sort Prop.

  (* Utility functions *)

  Fixpoint n_of_children (f: btforest) :=
    match f with
    | child t => 1
    | add t tl => 1 + (n_of_children tl)
    end.

  Fixpoint count_leaves (t: btree) :=
    match t with
    | Skill s => 1
    | node k f => cl_forest f
    end
  with cl_forest (f: btforest) :=
    match f with
    | child t => count_leaves t
    | add t tl => count_leaves t + cl_forest tl
    end.

  (* The following function replaces inner nodes with a single child with
     the child tree itself. We will prove later that this operation does not
     alter the semantics of the BT. *)

  Fixpoint normalize (t: btree) :=
    match t with
    | Skill s => Skill s
    | node k f => match f with
                  | child t => t
                  | _ => node k (normalize_forest f)
                  end
    end
  with normalize_forest (f: btforest) :=
    match f with
    | child t => child (normalize t)
    | add t ts => add (normalize t) (normalize_forest ts)
    end.


End BT_general.

  




  
  
