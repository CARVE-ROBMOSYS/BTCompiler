Require Import Bool List ListDec String.
Require Import bt basic micro_smv bt2spec fsm.

Inductive my_skills :=
  sk1 | sk2 | sk3 | sk4.
Definition my_names (x: my_skills) :=
  match x with
  | sk1 => "Go_to_kitchen"
  | sk2 => "find"
  | sk3 => "fetch"
  | sk4 => "ask"
  end.

Module ex_skills.

  Definition skillSet := my_skills.
  Definition skillName := my_names.

End ex_skills.

Module my_bt := BT_gen_semantics ex_skills.

Import my_bt.

Definition triv := Skill sk1.

(*Compute tick triv (fun x => match x with _ => Succ end).*)

Definition sconst_of_ret (x: return_enum) :=
  match x with
  | Succ => "Succ"
  | Runn => "Runn"
  | Fail => "Fail"
  end.

Definition make_inputs (f: skills_input) :=
  cons (sconst_of_ret (f sk1))  nil.

(* equality of states *)

Scheme Equality for list.

(* specialization for states (= list of strings) *)
Definition state_beq := list_beq string string_beq.
(* state -> state -> bool *)

Definition state_eq_dec := list_eq_dec string string_beq string_beq_correct1 string_beq_correct2.
(* forall x y : state, {x = y} + {x <> y} *)

Definition state_beq_correct1 := internal_list_dec_bl string string_beq string_beq_correct1.
(* forall x y : state, state_beq x y = true -> x = y *)

Definition state_beq_correct2 := internal_list_dec_lb string string_beq string_beq_correct2.
(* forall x y : state, x = y -> state_beq x y = true *)

(* other desirable lemmas having to do with list equality *)
Lemma list_eq_1: forall A (x1 x2 : A) (l1 l2 : list A),
    x1 :: l1 = x2 :: l2 -> x1 = x2 /\ l1 = l2.
Proof.
  intros; split; injection H; auto.
Qed.
Lemma list_eq_2: forall A (x1 x2 : A) (l1 l2 : list A),
    x1 = x2 /\ l1 = l2 -> x1 :: l1 = x2 :: l2.
Proof.
  intros.
  destruct H as [H1 H2].
  rewrite H1.
  rewrite H2.
  trivial.
Qed.    

(* Trying to prove something for the inverter... *)

Theorem inverter_ini_ex: exists x: state, is_initial inverter x = true.
Proof.
  exists ("FALSE"::nil).
  unfold is_initial; simpl; auto.
Qed.
(*
Theorem inverter_ini_uniq: forall x: state,
    is_initial inverter x = true -> x = ("FALSE"::nil).
Proof.
  intros.
  destruct x.
  - easy.
  - destruct (string_dec s "FALSE").
    -- rewrite e.
       apply list_eq_2.
       split.
       --- trivial.
       --- rewrite e in H.
           simpl in H.
           compute in H.
           destruct x.
           + trivial.
           + exfalso; apply diff_false_true; exact H.
    -- red in n.
       exfalso.
       apply n.
       compute in H.


(*
  bool_choice:
  forall (S : Set) (R1 R2 : S -> Prop),
  (forall x : S, {R1 x} + {R2 x}) ->
  {f : S -> bool | forall x : S, f x = true /\ R1 x \/ f x = false /\ R2 x}

  forall (S : Set) (R1 R2 : S -> Prop),
  (forall x : S, {R1 x} + {R2 x}) ->
  {f : S -> bool | forall x : S, f x = true /\ R1 x \/ f x = false /\ R2 x}

*)
Qed.
*)

Theorem inverter_det: forall x n1 n2: state, forall i: inputs,
      (is_next_of inverter x i n1 = true) /\
      (is_next_of inverter x i n2 = true) -> n1 = n2.
Proof.
  intros.
  destruct H.
  induction n1; induction n2.
  - trivial.
  - easy.
  - easy.
  - apply list_eq_2.
    split.
    -- unfold is_next_of in H.
       simpl in H.
       
Qed.  


(* proof that single_leaf is deterministic *)

Theorem init_state_ex: exists x: state, is_initial single_leaf x = true.
Proof.
  exists ("none"::"TRUE"::nil).
  unfold is_initial; simpl; auto.
Qed.

Lemma btriv_t: forall b: bool, (if b then true else true) = true.
Proof.
  intro; destruct b; auto.
Qed.   
Lemma btriv_f: forall b: bool, (if b then false else false) = false.
Proof.
  intro; destruct b; auto.
Qed.   

(*
Goal forall P Q: Prop, (P -> Q) -> (~Q -> ~P).
  intros.
  red.
  intro.
  assert Q by apply (H H1).
  easy.
Qed.

Search (_ = false).
not_false_is_true: forall b : bool, b <> false -> b = true
eq_true_false_abs: forall b : bool, b = true -> b = false -> False
not_true_is_false: forall b : bool, b <> true -> b = false
*)

Lemma contrapp_sbc1: forall s1 s2 : string, s1 <> s2 -> string_beq s1 s2 = false.
Proof.
  intros s1 s2 H.
  apply (not_true_is_false (string_beq s1 s2)).
  red; intro.
  red in H.
  apply H.
  apply (string_beq_correct1 s1 s2 H0).
Qed.
(*
Theorem init_state_uniq: forall x: state, 
    is_initial single_leaf x = true -> x = ("none"::"TRUE"::nil).
Proof.
  intro x.
(*  unfold is_initial; simpl.*)
  destruct x.
  - easy.
  - destruct (string_dec s "none").
    -- rewrite e.
       intro H.
       apply list_eq_2.
       split.
       + auto.
       + destruct x.
         ++ easy.
         ++ destruct (string_dec s0 "TRUE").
            * rewrite e0 in *.
              apply list_eq_2.
              split.
              ** auto.
              ** destruct x.
                 --- trivial.
                 --- easy.
            * assert (string_beq s0 "TRUE" = false).
              ** apply (contrapp_sbc1 s0 "TRUE" n).
              ** compute in H.
                 compute in H0.
                 fold string_beq in H.
(* come fargli capire che questo contesto è inconsistente? *)

              
vecchia roba:

         rewrite btriv_f.
         intros [Hc _].
         exfalso.
         pose proof diff_false_true.
         red in H.
         apply (H Hc).
      -- destruct x2.
         ++ set (b := string_equal "none" s0).
            rewrite btriv_f.
            intros [_ Hc]; exfalso.
            pose proof diff_false_true.
            red in H.
            apply (H Hc).
         ++ 
*)            


(*
        
Theorem sl_is_det2: forall x n1 n2: state, forall i: inputs,
      (is_next_of single_leaf x i n1 = true) /\
      (is_next_of single_leaf x i n2 = true) -> n1 = n2.
Proof.
  intros x n1 n2 i.
  unfold is_next_of; simpl.

*)

Theorem prova: forall input_f: skills_input,
    (tick triv input_f = Succ) <->
    (exec_determ single_leaf (make_inputs input_f) = Some ("Succ" :: nil)).
Proof.
  intros.
  split.
  - intro.
    unfold exec_determ.
    simpl.
    unfold next_states.
    simpl.    (* discreto chiodo... *)

    Search filter.


(* in general:
  forall t, forall input_f, (tick t input_f = Succ) <->
  (exec_determ (flatten (make_main t)) (make_inputs input_f) 
   = Some ("Succ"::nil))

  + other cases...
*)




