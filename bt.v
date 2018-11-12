(* This module contains two implementations for the BT data type.
   Both are parameterized over the signature BT_SIG, which defines
   a set whose members are the basic skills available and a function
   mapping each skill to its name (a string). *)

Require Import String.
Require Import Coq.Init.Datatypes.
Require Import Coq.Bool.Bool.

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

Module BT_binary_with_state (X: BT_SIG).

  Inductive btree: Set :=
  | Skill: X.skillSet -> btree
  | Sequence: btree -> btree -> btree
  | Fallback: btree -> btree -> btree
  | SequenceStar: bool -> btree -> btree -> btree.

  Fixpoint init_state (t: btree) :=
    match t with
    | Skill s => Skill s
    | Sequence l r => Sequence l r
    | Fallback l r => Fallback l r
    | SequenceStar s l r => SequenceStar false l r
    end.

  Inductive return_enum := Runn | Fail | Succ.

  Definition skills_input := X.skillSet -> return_enum.

  Fixpoint tick (t: btree) (input_f: skills_input) :=
    match t with
    | Skill s => (t, input_f s)
    | Sequence l r =>
      let (l', result) := tick l input_f in
      match result with
      | Succ =>
        let (r', result') := tick r input_f in
        (Sequence l' r', result')
      | _ => (Sequence l' r, result)
      end
    | Fallback l r =>
      let (l', result) := tick l input_f in
      match result with
      | Fail =>
        let (r', result') := tick r input_f in
        (Fallback l' r', result')
      | _ => (Fallback l' r, result)
      end
    | SequenceStar s l r =>
      match s with
      | true =>
        let (r', result_r) := tick r input_f in
        let flag := match result_r with
                    | Succ => false
                    | _ => true
                    end in
        (SequenceStar flag l r', result_r)
      | false =>
        let (l', result_l) := tick l input_f in
        match result_l with
        | Succ =>
          let (r', result_r) := tick r input_f in
          let flag := match result_r with
                      | Succ => false
                      | _ => true
                      end in
          (SequenceStar flag l' r', result_r)
        | _ => (SequenceStar false l' r, result_l)
        end
      end
    end.

End BT_binary_with_state.

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

