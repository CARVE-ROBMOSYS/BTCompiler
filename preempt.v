
(* A variation of the basic operational semantics for BTs which adds
   reactiveness: each skill comes with a reset function, which is called
   each time the skill is not ticked. *)

Require Import Arith List.
Require Import bt.

(* Version for BTs with arbitrary branching. *)

Module BT_gen_rsem (X: BT_SIG).

  Include BT_general X.

  Inductive return_enum := Runn | Fail | Succ.

  Definition skills_input := X.skillSet -> return_enum.

  Definition skills_reset := X.skillSet -> bool.

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

  Fixpoint reset_bt (t: btree) (reset_f: skills_reset) :=
    match t with
    | Skill s => reset_f s
    | TRUE => true
    | Node _ _ f => reset_forest f reset_f
    | Dec _ _ t => reset_bt t reset_f
    end
  with reset_forest (f: btforest) (reset_f: skills_reset) :=
    match f with
    | Child t => reset_bt t reset_f
    | Add t1 rest => let x := reset_bt t1 reset_f in
                     andb x (reset_forest rest reset_f)
    end.

  Fixpoint reset_running (f: btforest) (l: list return_enum) (reset_f: skills_reset) :=
  (* Notice that this function will always be called when l has the same 
     length as f, so hd and tl will never fail *)
    match f with
    | Child t => match hd Fail l with
                 | Runn => reset_bt t reset_f
                 | _ => true
                 end
    | Add t1 rest => let x :=
                         match hd Fail l with
                         | Runn => reset_bt t1 reset_f
                         | _ => true
                         end
                     in
                     andb x (reset_running rest (tl l) reset_f)
    end.
        
  Fixpoint tick (t: btree) (input_f: skills_input) (reset_f: skills_reset) :=
    match t with
    | Skill s => input_f s
    | TRUE => Succ
    | Node k _ f => match k with
                    | Sequence => tick_sequence f input_f reset_f
                    | Fallback => tick_fallback f input_f reset_f
                    | Parallel n =>
                      let results := tick_all f input_f reset_f in
                      if n <=? (countSucc results) then
                        (* result is surely Succ *)
                        let b := reset_running f results reset_f in
                        if b then Succ else Fail
                      else if (len f - n) <? (countFail results) then
                             (* result is surely Fail *)
                             let b := reset_running f results reset_f in
                             if b then Fail else Fail
                           else Runn  (* not enough results to make a decision *)
                    end
    | Dec k _ t => match k with
                   | Not =>
                     match tick t input_f reset_f with
                     | Runn => Runn
                     | Fail => Succ
                     | Succ => Fail
                     end
                   | IsRunning =>
                     match tick t input_f reset_f with
                     | Runn => Succ
                     | Fail => Fail
                     | Succ => Fail
                     end
                   end
    end
  with tick_sequence (f: btforest) (input_f: skills_input) (reset_f: skills_reset) :=
         match f with
         | Child t => tick t input_f reset_f
         | Add t1 rest => match tick t1 input_f reset_f with
                          | Runn => let b := reset_forest rest reset_f in
                                    if b then Runn else Fail
                          | Fail => let b := reset_forest rest reset_f in
                                    if b then Fail else Fail
                          | Succ => tick_sequence rest input_f reset_f
                          end
         end
  with tick_fallback (f: btforest) (input_f: skills_input) (reset_f: skills_reset) :=
         match f with
         | Child t => tick t input_f reset_f
         | Add t1 rest => match tick t1 input_f reset_f with
                          | Runn => let b := reset_forest rest reset_f in
                                    if b then Runn else Fail
                          | Fail => tick_fallback rest input_f reset_f
                          | Succ => let b := reset_forest rest reset_f in
                                    if b then Succ else Fail
                          end
         end
  with tick_all (f: btforest) (input_f: skills_input) (reset_f: skills_reset) :=
         match f with
         | Child t => cons (tick t input_f reset_f) nil
         | Add t1 rest => cons (tick t1 input_f reset_f)
                               (tick_all rest input_f reset_f)
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

End BT_gen_rsem.

(* Program extraction for the behavior tree interpreter *)

Require Import Extraction.
Require ExtrOcamlBasic ExtrOcamlString.
Extract Inductive nat => "int" ["0" "succ"]
                               "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Constant plus => "( + )".

(* The following option is needed to keep in the generated ML code the
   statements of the form 'if b then x else x' *)
Unset Extraction Optimize.
Extraction "infra/btrsem.ml" BT_gen_rsem.
