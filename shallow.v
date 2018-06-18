
(* In this file we realize the operational semantics for BTs as programs
   specified in the Gallina language. In other words, we define a
   shallow embedding of the BT language in the type theory used by Coq. *)

Require Import Arith.
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
    | TRUE => Succ
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
    | dec k t => match k with
                 | Not =>
                   match (tick t input_f) with
                   | Runn => Runn
                   | Fail => Succ
                   | Succ => Fail
                   end
                 | isRunning =>
                   match (tick t input_f) with
                   | Runn => Succ
                   | Fail => Fail
                   | Succ => Fail
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

(* Version for BTs with arbitrary branching. *)

Module BT_gen_semantics (X: BT_SIG).

  Include BT_general X.

  Inductive return_enum := Runn | Fail | Succ.

  Definition skills_input := X.SkillSet -> return_enum.

  Fixpoint countSucc (l: list return_enum) :=
    match l with
    | nil => 0
    | cons head tail => match head with
                        | Succ => countSucc tail + 1
                        | _ => countSucc tail
                        end
    end.

  Fixpoint countFail (l: list return_enum) :=
    match l with
    | nil => 0
    | cons head tail => match head with
                        | Fail => countFail tail + 1
                        | _ => countFail tail
                        end
    end.

  Fixpoint tick (t: btree) (input_f: skills_input) :=
    match t with
    | Skill s => input_f s
    | TRUE => Succ
    | node k f => match k with
                  | Sequence => tick_sequence f input_f
                  | Fallback => tick_fallback f input_f
                  | Parallel n => tick_parallel n f input_f
                  end
    end
  with tick_sequence (f: btforest) (input_f: skills_input) :=
         match f with
         | child t => tick t input_f
         | add t1 rest => match (tick t1 input_f) with
                          | Runn => Runn
                          | Fail => Fail
                          | Succ => tick_sequence rest input_f
                          end
         end
  with tick_fallback (f: btforest) (input_f: skills_input) :=
         match f with
         | child t => tick t input_f
         | add t1 rest => match (tick t1 input_f) with
                          | Runn => Runn
                          | Fail => tick_fallback rest input_f
                          | Succ => Succ
                          end
         end
  with tick_parallel (threshold: nat) (f: btforest) (input_f: skills_input) :=
         let results := (fix tick_all (f': btforest): list return_enum :=
                           match f' with
                           | child t => cons (tick t input_f) nil
                           | add t1 rest => cons (tick t1 input_f)
                                                 (tick_all rest)
                           end) f in
         if threshold <=? (countSucc results) then Succ
         else if (len f - threshold) <? (countFail results) then Fail
              else Runn.

  Definition return_same_value (t1 t2: btree) :=
    forall i: skills_input, (tick t1 i) = (tick t2 i).

  Fixpoint all_return_same_value (f1 f2: btforest) :=
    match f1, f2 with
    | child t1, child t2 => return_same_value t1 t2
    | child t1, add t2 r2 => False
    | add t1 r1, child t2 => False
    | add t1 r1, add t2 r2 => return_same_value t1 t2
                              /\ all_return_same_value r1 r2
    end.
(*
  Fixpoint all_return_same_value (f1 f2: btforest) :=
    (len f1 = len f2) /\
    match f1 with
    | child t1 => match f2 with
                  | child t2 => return_same_value t1 t2
                  | _ => False
                  end
    | add t1 r1 => match f2 with
                   | child t2 => False
                   | add t2 r2 => return_same_value t1 t2
                                  /\ all_return_same_value r1 r2
                   end
    end.
*)
  Hint Unfold return_same_value all_return_same_value.
  
  Lemma norm_seq: forall f: btforest,
      all_return_same_value f (normalize_forest f)
      -> forall i: skills_input,
        tick_sequence f i = tick_sequence (normalize_forest f) i.
  Proof.
    apply (btforest_mind
             (fun bt: btree => return_same_value bt (normalize bt)
                               -> forall i: skills_input, tick bt i = tick (normalize bt) i)
             (fun f: btforest => all_return_same_value f (normalize_forest f)
                                 -> forall i: skills_input, tick_sequence f i = tick_sequence (normalize_forest f) i)).
    - simpl; auto.
    - simpl; auto.
    - simpl; auto.
    - simpl; auto.
    - simpl.
      intros b Hb f Hf.
      intros [H0 H1] i.
      rewrite (Hb H0).
      rewrite (Hf H1).
      trivial.
  Qed.

  Lemma norm_fall: forall f: btforest,
      all_return_same_value f (normalize_forest f)
      -> forall i: skills_input,
        tick_fallback f i = tick_fallback (normalize_forest f) i.
  Proof.
    apply (btforest_mind
             (fun bt: btree => return_same_value bt (normalize bt)
                               -> forall i: skills_input, tick bt i = tick (normalize bt) i)
             (fun f: btforest => all_return_same_value f (normalize_forest f)
                                 -> forall i: skills_input, tick_fallback f i = tick_fallback (normalize_forest f) i)).
    - simpl; auto.
    - simpl; auto.
    - simpl; auto.
    - simpl; auto.
    - simpl.
      intros b Hb f Hf.
      intros [H0 H1] i.
      rewrite (Hb H0).
      rewrite (Hf H1).
      trivial.
  Qed.

  Lemma normalize_preserves_length:
    forall f: btforest, len (normalize_forest f) = len f.
  Proof.
    induction f.
    - auto.
    - simpl; f_equal; assumption.
(*    apply (btforest_mind
             (fun bt: btree => True)
             (fun f: btforest => len (normalize_forest f) = len f)).
    - auto.
    - auto.
    - auto.
    - auto.
    - intros b _ f H.
      simpl; f_equal; assumption.*)
  Qed.

  Lemma norm_par: forall f: btforest,
      all_return_same_value f (normalize_forest f)
      -> forall n:nat, forall i: skills_input, tick_parallel n f i = tick_parallel n (normalize_forest f) i.
  Proof.
    apply (btforest_mind
             (fun bt: btree => return_same_value bt (normalize bt)
                               -> forall i: skills_input, tick bt i = tick (normalize bt) i)
             (fun f: btforest => all_return_same_value f (normalize_forest f)
                                 -> forall n: nat, forall i: skills_input, tick_parallel n f i = tick_parallel n (normalize_forest f) i)).
    - simpl; auto.
    - simpl; auto.
    - simpl; auto.
    - simpl; auto.
      intros b Hb H0 n i.
      rewrite (Hb H0 i).
      auto.
    - simpl.
      intros b Hb f Hf.
      intros [H0 H1] n i.
      rewrite (Hb H0).
      shelve.
  Abort.
                                          
(* doesn't work; we need to reason about tick_all and prove, e.g.,
  tick_all (normalize_forest f) = tick_all f
  tick_all (normalize_forest f) = tick_all f
  ...
*)

  Theorem normalize_preserves_return_value:
    forall t: btree, return_same_value t (normalize t).
  Proof.
    apply (btree_mind
             (fun bt: btree => return_same_value bt (normalize bt))
             (fun f: btforest => all_return_same_value f (normalize_forest f))).
    - simpl; auto.
    - simpl; auto.
    - induction n.
(* sequence case *)      
      + destruct b.
        -- simpl; auto.
        -- simpl.
           intros [H H0] i.
           simpl.
           assert (H1: tick b i = tick (normalize b) i) by (apply H).
           rewrite <- H1.
           assert (H2: tick_sequence b0 i = tick_sequence (normalize_forest b0) i) by (apply norm_seq; assumption).
           rewrite <- H2.
           trivial.
(* fallback case *)
      + destruct b.
        -- simpl; auto.
        -- simpl.
           intros [H H0] i.
           simpl.
           assert (H1: tick b i = tick (normalize b) i) by (apply H).
           rewrite <- H1.
           assert (H2: tick_fallback b0 i = tick_fallback (normalize_forest b0) i) by (apply norm_fall; assumption).
           rewrite <- H2.
           trivial.
(* parallel case *)
      + destruct b.
        -- simpl.
           intros H i.
           simpl; rewrite H; auto.
(*           destruct n.
           ++ compute; auto.
           ++ simpl; rewrite H; auto.  *)
        -- simpl.
           intros [H H0] i.
           simpl.
           (* same problem as above... *)
           give_up.
(*           destruct n.
           ++ compute; auto.
           ++ shelve.  *)
    - destruct b; simpl; auto.
    - destruct b; simpl; auto.
  Abort.

    
End BT_gen_semantics.

  




