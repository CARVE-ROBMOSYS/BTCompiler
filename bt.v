
(* This module contains two implementations for the BT data type.
   Both are parameterized modules over the signature BT_SIG, which defines
   (for now) only a set specifying the basic skills available. *)

Require Import String.

Module Type BT_SIG.
  
  Parameter SkillSet: Set.
  Parameter SkillName: SkillSet -> string.
  
End BT_SIG.

(* First implementation: trees with binary branching only *)

Module BT_binary (X: BT_SIG).
  
  Inductive NodeKind: Set :=
    Sequence | Fallback | Parallel1 | Parallel2.

  Inductive DecKind: Set :=
    Not | isRunning. (* | isEnabled. *)

  (* Other decorators with memory, like the "max-N-tries" and the
     "max-T-sec" decorators described in the book by Colledanchise
     and Ogren, are best implemented as composite BTs which manage
     the state via some skills implementing a suitable interface,
     e.g. communication with a parameter server. *)
  
  Inductive btree: Set :=
  | Skill: X.SkillSet -> btree
  | TRUE: btree
  | node: NodeKind -> string -> btree -> btree -> btree
  | dec: DecKind -> string -> btree -> btree.

  (* Utility functions *)

  Fixpoint count_leaves (t: btree) :=
    match t with
    | Skill _ => 1
    | TRUE => 1
    | node _ _ t1 t2 => count_leaves t1 + count_leaves t2
    | dec _ _ t => count_leaves t
    end.

End BT_binary.

(* Second implementation: trees with arbitrary branching *)

Module BT_general (X: BT_SIG).

  Inductive NodeKind: Set :=
  | Sequence: NodeKind
  | Fallback: NodeKind
  | Parallel: nat -> NodeKind.

  Inductive DecKind: Set :=
    Not | isRunning. (* | isEnabled. *)

  Inductive btree: Set :=
  | Skill: X.SkillSet -> btree
  | TRUE: btree
  | node: NodeKind -> string -> btforest -> btree
  | dec: DecKind -> string -> btree -> btree
  with btforest: Set :=
  | child: btree -> btforest              (* a forest has at least one tree *)
  | add: btree -> btforest -> btforest.

  (* Instantiation of the correct mutual induction principles *)

  Scheme btree_mind := Induction for btree Sort Prop
  with btforest_mind := Induction for btforest Sort Prop.

  (* Utility functions *)

  Fixpoint len (f: btforest) :=
    match f with
    | child t => 1
    | add t1 rest => S (len rest)
    end.

  Fixpoint count_leaves (t: btree) :=
    match t with
    | Skill _ => 1
    | TRUE => 1
    | node _ _ f => cl_forest f
    | dec _ _ t => count_leaves t
    end
  with cl_forest (f: btforest) :=
    match f with
    | child t => count_leaves t
    | add t tl => count_leaves t + cl_forest tl
    end.

  (* The following function replaces inner nodes with a single child with
     the child tree itself. We may prove later that this operation does not
     alter the semantics of the BT. *)

  Fixpoint normalize (t: btree) :=
    match t with
    | Skill s => Skill s
    | TRUE => TRUE
    | node k n f => match k with
(* original implementation:
                    | Parallel 0 => TRUE
                    | _ => match f with
                           | child t => t
                           | _ => node k n (normalize_forest f)
                           end
                    end
   this cannot be proved correct because of meaningless thresholds in
   parallel nodes. So we leave parallel nodes alone: *)
                    | Sequence =>
                      match f with
                      | child t => t
                      | _ => node k n (normalize_forest f)
                      end
                    | Fallback =>
                      match f with
                      | child t => t
                      | _ => node k n (normalize_forest f)
                      end
                    | _ => node k n (normalize_forest f)
                    end
    | dec k n t => match k with
                   | Not => match t with
                            | dec Not _ t' => t'      (* Not is an involution *)
                            | _ => dec Not n (normalize t)
                            end
                   | _ => dec k n (normalize t)
                   end
    end
  with normalize_forest (f: btforest) :=
    match f with
    | child t => child (normalize t)
    | add t ts => add (normalize t) (normalize_forest ts)
    end.


End BT_general.

