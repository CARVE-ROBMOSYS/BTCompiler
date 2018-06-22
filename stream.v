
(* In this file we realize the operational semantics for BTs as programs
   specified in the Gallina language. In other words, we define a
   shallow embedding of the BT language in the type theory used by Coq. *)

Require Import Arith Streams.
Require Import bt.

(* Version for BTs with binary nodes only. *)

Module BT_bin_str_sem (X: BT_SIG).

  Include BT_binary X.

  Inductive return_enum := Runn | Fail | Succ.

  Definition skills_input := X.SkillSet -> return_enum.
  (* A term of this type encapsulates a returns value for each skill
     at the instant of time in which the tick is executed. *)

  Definition input_stream := Stream skills_input.

  (* The following function evaluates a single tick by consuming the
     input_stream as needed and discarding the resulting stream *)

  Fixpoint tick (t: btree) (i: input_stream) :=
    match t with
    | Skill s => (hd i) s
    | TRUE => Succ
    | node k t1 t2 => match k with
                      | Sequence =>
                        match tick t1 i with
                        | Runn => Runn
                        | Fail => Fail
                        | Succ => tick t2 (tl i)
                        end
                      | Fallback =>
                        match tick t1 i with
                        | Runn => Runn
                        | Fail => tick t2 (tl i)
                        | Succ => Succ
                        end
                      | Parallel1 =>
                        let a := tick t1 i in
                        let b := tick t2 i in
                        match a , b with
                        | Succ , _ => Succ
                        | _ , Succ => Succ
                        | Fail , Fail => Fail
                        | _ , _ => Runn
                        end
                      | Parallel2 =>
                        let a := tick t1 i in
                        let b := tick t2 i in
                        match a , b with
                        | Succ , Succ => Succ
                        | Fail , _ => Fail
                        | _ , Fail => Fail
                        | _ , _ => Runn
                        end
                      end
    | dec k t => match k with
                 | Not =>
                   match tick t i with
                   | Runn => Runn
                   | Fail => Succ
                   | Succ => Fail
                   end
                 | isRunning =>
                   match tick t i with
                   | Runn => Succ
                   | Fail => Fail
                   | Succ => Fail
                   end
                 end
    end.

  (* The following function evaluates a single tick by consuming the
     input_stream and returning the resulting stream as a second argument.
     Notice that it is not entirely clear whether we do the right thing 
     with the returned stream in case of parallel nodes. As it is now,
     it works only when the two branches consume exactly the same number
     of symbols. *)
  
  Fixpoint tick2 (t: btree) (i: input_stream): return_enum * input_stream :=
    match t with
    | Skill s => pair ((hd i) s) (tl i)
    | TRUE => pair Succ i
    | node k t1 t2 => match k with
                      | Sequence =>
                        let (res , str) := tick2 t1 i in
                        match res with
                        | Runn => pair Runn str
                        | Fail => pair Fail str
                        | Succ => tick2 t2 str
                        end
                      | Fallback =>
                        let (res , str) := tick2 t1 i in
                        match res with
                        | Runn => pair Runn str
                        | Fail => tick2 t2 str
                        | Succ => pair Succ str
                        end
                      | Parallel1 =>
                        let (r1, s1) := tick2 t1 i in
                        let (r2, s2) := tick2 t2 i in
                        match r1 , r2 with
                        | Succ , _ => pair Succ s1
                        | _ , Succ => pair Succ s1 (* or s2 ??? *)
                        | Fail , Fail => pair Fail s1
                        | _ , _ => pair Runn s1
                        end
                      | Parallel2 =>
                        let (r1 , s1) := tick2 t1 i in
                        let (r2 , s2) := tick2 t2 i in
                        match r1 , r2 with
                        | Succ , Succ => pair Succ s1
                        | Fail , _ => pair Fail s1
                        | _ , Fail => pair Fail s1
                        | _ , _ => pair Runn s1
                        end
                      end
    | dec k t => match k with
                 | Not =>
                   let (res , str) := tick2 t i in
                   match res with
                   | Runn => pair Runn str
                   | Fail => pair Succ str
                   | Succ => pair Fail str
                   end
                 | isRunning =>
                   let (res , str) := tick2 t i in
                   match res with
                   | Runn => pair Succ str
                   | Fail => pair Fail str
                   | Succ => pair Fail str
                   end
                 end
    end.

  (* The following function evaluates a specified number of ticks on the
     given input_stream; it returns a list containing the results of the
     successive tickings.
     Notice that an analogous function for unlimited values of n cannot
     be defined in Gallina (not even as a corecursive function on the
     input stream), since the corresponding corecursion would necessarily
     be unguarded. *)

  Fixpoint reptick (t: btree) (n: nat) (i: input_stream): list return_enum :=
    let (res , str) := tick2 t i in
    match n with
    | O => cons res nil
    | S p => cons res (reptick t p str)
    end.

  
  Definition return_same_value (a: btree) (b: btree): Prop :=
    forall i: input_stream, (tick a i) = (tick b i).

  (* Notice that with this implementation it is no longer true that all
     nodes are associative! For instance a Sequence node with 3 children
     *must* be coded as 
     node Sequence t1 (node Sequence t2 t3)
     
     If we use instead the tree
     node Sequence (node Sequence t1 t2) t3
     the branch t3 will be evaluated at the same "instant of time" as t2,
     which is not the intended semantics.
   *)

End BT_bin_str_sem.

(* Version for BTs with arbitrary branching *)

Module BT_gen_str_sem (X: BT_SIG).

  Include BT_general X.

  Inductive return_enum := Runn | Fail | Succ.

  Definition skills_input := X.SkillSet -> return_enum.

  Definition input_stream := Stream skills_input.

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

  (* single tick evaluation, discarding the input_stream *)
  
  Fixpoint tick (t: btree) (i: input_stream) :=
    match t with
    | Skill s => (hd i) s
    | TRUE => Succ
    | node k f => match k with
                  | Sequence => tick_sequence f i
                  | Fallback => tick_fallback f i
                  | Parallel n =>
                    let results := tick_all f i in
                    if n <=? (countSucc results) then Succ
                    else if (len f - n) <? (countFail results) then Fail
                         else Runn
                  end
    | dec k t => match k with
                 | Not =>
                   match tick t i with
                   | Runn => Runn
                   | Fail => Succ
                   | Succ => Fail
                   end
                 | isRunning =>
                   match tick t i with
                   | Runn => Succ
                   | Fail => Fail
                   | Succ => Fail
                   end
                 end
    end
  with tick_sequence (f: btforest) (i: input_stream) :=
         match f with
         | child t => tick t i
         | add t1 rest => match tick t1 i with
                          | Runn => Runn
                          | Fail => Fail
                          | Succ => tick_sequence rest (tl i)
                          end
         end
  with tick_fallback (f: btforest) (i: input_stream) :=
         match f with
         | child t => tick t i
         | add t1 rest => match tick t1 i with
                          | Runn => Runn
                          | Fail => tick_fallback rest (tl i)
                          | Succ => Succ
                          end
         end
  with tick_all (f: btforest) (i: input_stream) :=
         match f with
         | child t => cons (tick t i) nil
         | add t1 rest => cons (tick t1 i) (tick_all rest i)
         end.

  (* Single tick evaluation, preserving the input_stream *)

  Fixpoint tick2 (t: btree) (i: input_stream): return_enum * input_stream :=
    match t with
    | Skill s => pair ((hd i) s) (tl i)
    | TRUE => pair Succ i
    | node k f => match k with
                  | Sequence => tick2_sequence f i
                  | Fallback => tick2_fallback f i
                  | Parallel n =>
                    let (results , str) := tick2_all f i in
                    if n <=? (countSucc results) then pair Succ str
                    else if (len f - n) <? (countFail results) then pair Fail str
                         else pair Runn str
                  end
    | dec k t => match k with
                 | Not =>
                   let (res , str) := tick2 t i in
                   match res with
                   | Runn => pair Runn str
                   | Fail => pair Succ str
                   | Succ => pair Fail str
                   end
                 | isRunning =>
                   let (res , str) := tick2 t i in
                   match res with
                   | Runn => pair Succ str
                   | Fail => pair Fail str
                   | Succ => pair Fail str
                   end
                 end
    end
  with tick2_sequence (f: btforest) (i: input_stream): return_enum * input_stream :=
         match f with
         | child t => tick2 t i
         | add t1 rest => let (res , str) := tick2 t1 i in
                          match res with
                          | Runn => pair Runn str
                          | Fail => pair Fail str
                          | Succ => tick2_sequence rest str
                          end
         end
  with tick2_fallback (f: btforest) (i: input_stream): return_enum * input_stream :=
         match f with
         | child t => tick2 t i
         | add t1 rest => let (res , str) := tick2 t1 i in
                          match res with
                          | Runn => pair Runn str
                          | Fail => tick2_fallback rest str
                          | Succ => pair Succ str
                          end
         end
  with tick2_all (f: btforest) (i: input_stream): list return_enum * input_stream :=
         match f with
         | child t => let (res , str) := tick2 t i in
                      pair (cons res nil) str
         | add t1 rest => let (res , str) := tick2 t1 i in
                          (* keep the stream resulting from the first node *)
                          pair (cons res (fst (tick2_all rest i))) str
         end.

  (* Evaluation of a specified number of ticks *)

  Fixpoint reptick (t: btree) (n: nat) (i: input_stream): list return_enum :=
    let (res , str) := tick2 t i in
    match n with
    | O => cons res nil
    | S p => cons res (reptick t p str)
    end.




End BT_gen_str_sem.



