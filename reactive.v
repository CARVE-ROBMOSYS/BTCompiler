
(* Operational semantics for reactive BTs (= skills with reset function) *)

Require Import Arith.
Require Import bt.

(* Version for BTs with arbitrary branching. *)

Module BT_gen_rsem (X: BT_SIG).

  Include BT_general X.

  Inductive return_enum := Runn | Fail | Succ.

  Definition skills_input := X.skillSet -> return_enum.
  Definition skills_reset := X.skillSet -> unit.

  Fixpoint countSucc (l: list return_enum) :=
    match l with
    | nil => 0
    | cons head tail => match head with
                        | Succ => S (countSucc tail)
                        | _ => countSucc tail
                        end
    end.

  Fixpoint countFail (l: list return_enum) :=
    match l with
    | nil => 0
    | cons head tail => match head with
                        | Fail => S (countFail tail)
                        | _ => countFail tail
                        end
    end.

  Fixpoint reset (t: btree) (reset_f: skills_reset) :=
    match t with
    | Skill s => reset_f s
    | TRUE => tt
    | Node _ _ f => reset_forest f reset_f
    | Dec _ _ t => reset t reset_f
    end
  with reset_forest (f: btforest) (reset_f: skills_reset) :=
    match f with
    | Child t => reset t reset_f
    | Add t1 rest => let _ := reset t1 reset_f in
                     reset_forest rest reset_f
    end.
                        
  Fixpoint tick (t: btree) (input_f: skills_input) :=
    match t with
    | Skill s => input_f s
    | TRUE => Succ
    | Node k _ f => match k with
                    | Sequence => tick_sequence f input_f
                    | Fallback => tick_fallback f input_f
                    | Parallel n =>
                      let results := tick_all f input_f in
                      if n <=? (countSucc results) then Succ
                      else if (len f - n) <? (countFail results) then Fail
                           else Runn
                    end
    | Dec k _ t => match k with
                   | Not =>
                     match tick t input_f with
                     | Runn => Runn
                     | Fail => Succ
                     | Succ => Fail
                     end
                   | IsRunning =>
                     match tick t input_f with
                     | Runn => Succ
                     | Fail => Fail
                     | Succ => Fail
                     end
                   end
    end
  with tick_sequence (f: btforest) (input_f: skills_input) :=
         match f with
         | Child t => tick t input_f
         | Add t1 rest => match tick t1 input_f with
                          | Runn => let _ := reset_forest rest in
                                    Runn
                          | Fail => let _ := reset_forest rest in
                                    Fail
                          | Succ => tick_sequence rest input_f
                          end
         end
  with tick_fallback (f: btforest) (input_f: skills_input) :=
         match f with
         | Child t => tick t input_f
         | Add t1 rest => match tick t1 input_f with
                          | Runn => let _ := reset_forest rest in
                                    Runn
                          | Fail => tick_fallback rest input_f
                          | Succ => Succ
                          end
         end
  with tick_all (f: btforest) (input_f: skills_input) :=
         match f with
         | Child t => cons (tick t input_f) nil
         | Add t1 rest => cons (tick t1 input_f) (tick_all rest input_f)
         end.

  Definition return_same_value (t1 t2: btree) :=
    forall i: skills_input, (tick t1 i) = (tick t2 i).

  Fixpoint all_return_same_value (f1 f2: btforest) :=
    match f1, f2 with
    | Child t1, Child t2 => return_same_value t1 t2
    | Child t1, Add t2 r2 => False
    | Add t1 r1, Child t2 => False
    | Add t1 r1, Add t2 r2 => return_same_value t1 t2
                              /\ all_return_same_value r1 r2
    end.

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
      intros t H H0 i.
      rewrite (H H0 i); trivial.
    - simpl.
      intros t Ht f Hf.
      intros [H0 H1] i.
      rewrite (Ht H0); rewrite (Hf H1); trivial.
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
      intros t H H0 i.
      rewrite (H H0 i); trivial.
    - simpl.
      intros t Ht f Hf.
      intros [H0 H1] i.
      rewrite (Ht H0); rewrite (Hf H1); trivial.
  Qed.

  Lemma normalize_preserves_length:
    forall f: btforest, len (normalize_forest f) = len f.
  Proof.
    induction f.
    - auto.
    - simpl; f_equal; assumption.
  Qed.

  Lemma norm_par: forall f: btforest,
      all_return_same_value f (normalize_forest f)
      -> forall i: skills_input,
        tick_all f i = tick_all (normalize_forest f) i.
  Proof.
    apply (btforest_mind
             (fun bt: btree => return_same_value bt (normalize bt)
                               -> forall i: skills_input, tick bt i = tick (normalize bt) i)
             (fun f: btforest => all_return_same_value f (normalize_forest f)
                                 -> forall i: skills_input, tick_all f i = tick_all (normalize_forest f) i)).
    - simpl; auto.
    - simpl; auto.
    - simpl; auto.
    - simpl; auto.
    - simpl.
      intros t H H0 i.
      rewrite (H H0 i); trivial.
    - simpl.
      intros t Ht f Hf.
      intros [H0 H1] i.
      rewrite (Ht H0); rewrite (Hf H1); trivial.
  Qed.

  Lemma normalize_preserves_node:
    forall (k: nodeKind) (s: String.string) (f: btforest),
      all_return_same_value f (normalize_forest f) ->
      return_same_value (Node k s f) (normalize (Node k s f)).
  Proof.
    induction k.
    (* sequence case *)      
    + destruct f.
      -- simpl; auto.
      -- simpl.
         intros [H H0] i.
         simpl.
         assert (H1: tick b i = tick (normalize b) i) by (apply H).
         assert (H2: tick_sequence f i = tick_sequence (normalize_forest f) i) by (apply norm_seq; assumption).
         rewrite H1; rewrite H2; trivial.
    (* fallback case *)
    + destruct f.
      -- simpl; auto.
      -- simpl.
         intros [H H0] i.
         simpl.
         assert (H1: tick b i = tick (normalize b) i) by (apply H).
         assert (H2: tick_fallback f i = tick_fallback (normalize_forest f) i) by (apply norm_fall; assumption).
         rewrite H1; rewrite H2; trivial.
    (* parallel case *)
    + destruct f.
      -- simpl.
         intros H i.
         simpl; rewrite H; auto.
      -- simpl.
         intros [H H0] i.
         unfold return_same_value in H.
         simpl.
         rewrite (H i).
         rewrite (norm_par f H0 i).
         rewrite (normalize_preserves_length f).
         trivial.
  Qed.

  Lemma normalize_preserves_decs:
    forall (d: decKind) (s: String.string) (t: btree),
      return_same_value t (normalize t) ->
      return_same_value (Dec d s t) (normalize (Dec d s t)).
  Proof.
    induction d.
    (* not case *)
    + intros s t H i.
      simpl.
      destruct t.
      -- simpl; auto.
      -- simpl; auto.
      -- rewrite (H i); simpl.
         destruct n; simpl in H; rewrite <- H; trivial.
      -- destruct d.
         ++ simpl.
            destruct (tick t i); simpl; trivial.
         ++ rewrite (H i).
            simpl; trivial.
    (* isrunning case*)
    + intros s t H i.
      simpl; rewrite H; trivial.
  Qed.

  Theorem normalize_preserves_return_value:
    forall t: btree, return_same_value t (normalize t).
  Proof.
    apply (btree_mind
             (fun bt: btree => return_same_value bt (normalize bt))
             (fun f: btforest => all_return_same_value f (normalize_forest f))).
    - simpl; auto.
    - simpl; auto.
    - apply normalize_preserves_node.
    - apply normalize_preserves_decs.
    - destruct b; simpl; auto.
    - destruct b; simpl; auto.
  Qed.
    
End BT_gen_rsem.

(* Program extraction for the behavior tree interpreter *)

Require Import Extraction.
Require ExtrOcamlBasic ExtrOcamlString.
Extract Inductive nat => "int" ["0" "succ"]
                               "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Constant plus => "( + )".

Extraction "infra/btrsem.ml" BT_gen_rsem.

