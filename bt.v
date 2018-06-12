
(* This module implements the BT data type, parameterized over a set
   specifying the basic skills available. *)

Module Type BT_SIG.
  
  Parameter SkillSet: Set.

End BT_SIG.

Module BT_binary (X: BT_SIG).
  
  Inductive NodeKind: Set :=
    Sequence | Fallback | Parallel1 | Parallel2.

  (* Inductive DecKind: Set := Not | isRunning | isEnabled | ... *)
  
  Inductive btree: Set :=
  | Skill: X.SkillSet -> btree
  | node: NodeKind -> btree -> btree -> btree.
  (*  | Decorator: DecKind -> btree -> btree *)

  (*
  btree_ind: forall P : btree -> Prop,
    (forall (k : NodeKind) (b : btree), 
      P b -> forall b0 : btree, P b0 -> P (node k b b0)) ->
    (forall s : SkillSet, P (Skill s)) -> 
    forall b : btree, P b
  *)

  (* Utility functions *)

  Fixpoint count_leaves (t: btree) :=
    match t with
    | Skill s => 1
    | node k t1 t2 => (count_leaves t1) + (count_leaves t2)
    end.

End BT_binary.
