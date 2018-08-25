
(* This module contains two implementations for the BT data type.
   Both are parameterized over the signature BT_SIG, which defines
   a set whose members are the basic skills available and a function
   mapping each skill to its name (a string). *)

Require Import String.

Module Type BT_SIG.
  
  Parameter skillSet: Set.
  Parameter skillName: skillSet -> string.
  
End BT_SIG.

(* First implementation: trees with binary branching only *)

Module BT_binary (X: BT_SIG).
  
  Inductive nodeKind: Set :=
    Sequence | Fallback | Parallel1 | Parallel2.

  Inductive decKind: Set :=
    Not | IsRunning. (* | IsEnabled. *)

  (* Other decorators with memory, like the "max-N-tries" and the
     "max-T-sec" decorators described in the book by Colledanchise
     and Ogren, are best implemented as composite BTs which manage
     the state via some skills implementing a suitable interface,
     e.g. communication with a parameter server. *)
  
  Inductive btree: Set :=
  | Skill: X.skillSet -> btree
  | TRUE: btree
  | Node: nodeKind -> string -> btree -> btree -> btree
  | Dec: decKind -> string -> btree -> btree.

  (* Utility functions *)

  Fixpoint sklist (t: btree): list X.skillSet :=
    match t with
    | Skill s => s::nil
    | TRUE => nil
    | Node _ _ t1 t2 => app (sklist t1) (sklist t2)
    | Dec _ _ t => sklist t
    end.

End BT_binary.

(* Second implementation: trees with arbitrary branching *)

Module BT_general (X: BT_SIG).

  Inductive nodeKind: Set :=
  | Sequence: nodeKind
  | Fallback: nodeKind
  | Parallel: nat -> nodeKind.

  Inductive decKind: Set :=
    Not | IsRunning. (* | IsEnabled. *)

  Inductive btree: Set :=
  | Skill: X.skillSet -> btree
  | TRUE: btree
  | Node: nodeKind -> string -> btforest -> btree
  | Dec: decKind -> string -> btree -> btree
  with btforest: Set :=
  | Child: btree -> btforest              (* a forest has at least one tree *)
  | Add: btree -> btforest -> btforest.

  (* Instantiation of the correct mutual induction principles *)

  Scheme btree_mind := Induction for btree Sort Prop
  with btforest_mind := Induction for btforest Sort Prop.

  (* Utility functions *)

  Fixpoint len (f: btforest) :=
    match f with
    | Child t => 1
    | Add t1 rest => S (len rest)
    end.

  Fixpoint sklist (t: btree): list X.skillSet :=
    match t with
    | Skill s => s::nil
    | TRUE => nil
    | Node _ _ f => skl_forest f
    | Dec _ _ t => sklist t
    end
  with skl_forest (f: btforest) :=
    match f with
    | Child t => sklist t
    | Add t tl => app (sklist t) (skl_forest tl)
    end.

  (* The following function replaces inner nodes having a single child with
     the child tree itself. We may prove later that this operation does not
     alter the semantics of the BT. *)

  Fixpoint normalize (t: btree) :=
    match t with
    | Skill s => Skill s
    | TRUE => TRUE
    | Node k n f => match k with
(* original implementation:
                    | Parallel 0 => TRUE
                    | _ => match f with
                           | Child t => t
                           | _ => Node k n (normalize_forest f)
                           end
                    end
   This cannot be proved correct because of the unsharp specification of
   parallel nodes. So we leave parallel nodes alone: *)
                    | Sequence =>
                      match f with
                      | Child t => t
                      | _ => Node k n (normalize_forest f)
                      end
                    | Fallback =>
                      match f with
                      | Child t => t
                      | _ => Node k n (normalize_forest f)
                      end
                    | _ => Node k n (normalize_forest f)
                    end
    | Dec k n t => match k with
                   | Not => match t with
                            | Dec Not _ t' => t'    (* Not is an involution *)
                            | _ => Dec Not n (normalize t)
                            end
                   | _ => Dec k n (normalize t)
                   end
    end
  with normalize_forest (f: btforest) :=
    match f with
    | Child t => Child (normalize t)
    | Add t ts => Add (normalize t) (normalize_forest ts)
    end.


End BT_general.

