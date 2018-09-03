Require Import bt micro_smv spec_extr.
Require Import Arith List ListSet String.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.
Open Scope string_scope.

Definition bt_input_type :=
  (TEnum ("Runn"::"Fail"::"Succ"::nil)).

Definition bt_output_type :=
  (TEnum ("none"::"running"::"failed"::"succeeded"::nil)).

Definition bt_action_type :=
  (TEnum ("Enable"::"Reset"::nil)).

(* Boilerplate modules *)

Definition bp_tick_generator :=
  Build_smv_module
    "bt_tick_generator"
    ("top_level_bt"::nil)
    ((ASSIGN (AddA (init (Mod "top_level_bt" (Id "enable"))
                         (BConst smvT))
                   (LastA (next (Mod "top_level_bt" (Id "enable"))
                                (Simple (Neg (Equal (Qual (Mod "top_level_bt"
                                                               (Id "output")))
                                                    (SConst "none"))))))))
     ::nil).

Definition bp_skill_autonomous :=
  (* This module is useful for autonomous generation of an SMV specification.
     When used with OCRA, the following (simpler) module is sufficient: input
     variables and transitions are supplied by the main module. *)
  Build_smv_module
    "bt_skill"
    nil
    ((IVAR (LastI "input" bt_input_type))
     ::
     (VAR (AddV "output" (TSimp bt_output_type)
                (LastV "enable" (TSimp TBool))))
     ::
     (ASSIGN (AddA (init (Id "output") (SConst "none"))
                   (LastA
                      (next (Id "output")
                            (Simple
                               (Case
                                  (AddCexp (Neg (Qual (Id "enable")))
                                           (SConst "none")
                                           (AddCexp (Equal (Qual (Id "input"))
                                                           (SConst "Runn"))
                                                    (SConst "running")
                                                    (AddCexp (Equal (Qual (Id "input"))
                                                                    (SConst "Fail"))
                                                             (SConst "failed")
                                                             (Cexp (Equal (Qual (Id "input"))
                                                                          (SConst "Succ"))
                                                                   (SConst "succeeded")))))))))))
     ::nil).

Definition bp_skill :=
  Build_smv_module
    "bt_skill"
    nil
    ((VAR (AddV "output" (TSimp bt_output_type)
                (LastV "enable" (TSimp TBool))))
     ::nil).

Definition bp_TRUE :=
  Build_smv_module
    "bt_TRUE"
    nil
    ((VAR (LastV "enable" (TSimp TBool)))
     ::
     (DEFINE (LastD "output" (SConst "succeeded")))
     ::nil).

Definition bp_not :=
  Build_smv_module
    "bt_not"
    ("child_bt"::nil)
    ((VAR (LastV "enable" (TSimp TBool)))
     ::
     (ASSIGN (LastA (invar (Mod "child_bt" (Id "enable"))
                           (Qual (Id "enable")))))
     ::
     (DEFINE (LastD "output" (Case
                                (AddCexp (Equal (Qual (Mod "child_bt"
                                                           (Id "output")))
                                                (SConst "failed"))
                                         (SConst "succeeded")
                                         (AddCexp (Equal (Qual (Mod "child_bt"
                                                                    (Id "output")))
                                                         (SConst "succeeded"))
                                                  (SConst "failed")
                                                  (Cexp (BConst smvT)
                                                        (Qual (Mod "child_bt"
                                                                   (Id "output")))))))))
     ::nil).
    
Definition bp_isRunning := 
  Build_smv_module
    "bt_isRunning"
    ("child_bt"::nil)
    ((VAR (LastV "enable" (TSimp TBool)))
     ::
     (ASSIGN (LastA (invar (Mod "child_bt" (Id "enable"))
                           (Qual (Id "enable")))))
     ::
     (DEFINE (LastD "output" (Case
                                (AddCexp (Equal (Qual (Mod "child_bt"
                                                           (Id "output")))
                                                (SConst "running"))
                                         (SConst "succeeded")
                                         (AddCexp (Equal (Qual (Mod "child_bt"
                                                                    (Id "output")))
                                                         (SConst "none"))
                                                  (SConst "none")
                                                  (Cexp (BConst smvT)
                                                        (SConst "failed")))))))
     ::nil).

Module BT_bin_spec (X: BT_SIG).

  Include BT_binary X.

  (* Boilerplate modules specific for the binary case *)

  Definition bp_bin_seq :=
    Build_smv_module
      "bt_sequence"
      ("left_bt"::"right_bt"::nil)
      ((VAR (LastV "enable" (TSimp TBool)))
       ::
       (ASSIGN (AddA (invar (Mod "left_bt" (Id "enable"))
                            (Qual (Id "enable")))
                     (LastA (invar (Mod "right_bt" (Id "enable"))
                                   (Equal (Qual (Mod "left_bt" (Id "output")))
                                          (SConst "succeeded"))))))
       ::
       (DEFINE (LastD "output" (Case
                                  (AddCexp (Equal (Qual (Mod "left_bt" (Id "output")))
                                                  (SConst "succeeded"))
                                           (Qual (Mod "right_bt" (Id "output")))
                                           (Cexp (BConst smvT)
                                                 (Qual (Mod "left_bt" (Id "output"))))))))
       ::nil).

  Definition bp_bin_fb :=
    Build_smv_module
      "bt_fallback"
      ("left_bt"::"right_bt"::nil)
      ((VAR (LastV "enable" (TSimp TBool)))
       ::
       (ASSIGN (AddA (invar (Mod "left_bt" (Id "enable"))
                            (Qual (Id "enable")))
                     (LastA (invar (Mod "right_bt" (Id "enable"))
                                   (Equal (Qual (Mod "left_bt" (Id "output")))
                                          (SConst "failed"))))))
       ::
       (DEFINE (LastD "output" (Case
                                  (AddCexp (Equal (Qual (Mod "left_bt" (Id "output")))
                                                  (SConst "failed"))
                                           (Qual (Mod "right_bt" (Id "output")))
                                           (Cexp (BConst smvT)
                                                 (Qual (Mod "left_bt" (Id "output"))))))))
       ::nil).

  Definition bp_par1 :=
  Build_smv_module
    "bt_parallel1"
    ("left_bt"::"right_bt"::nil)
    ((VAR (LastV "enable" (TSimp TBool)))
     ::
     (ASSIGN
        (AddA (invar (Mod "left_bt" (Id "enable"))
                     (Qual (Id "enable")))
              (LastA (invar (Mod "right_bt" (Id "enable"))
                            (Qual (Id "enable"))))))
     ::
     (DEFINE
        (AddD "true_output_count"
              (Count (AddSexp
                        (Equal (Qual (Mod "left_bt" (Id "output")))
                               (SConst "succeeded"))
                        (Sexp
                           (Equal (Qual (Mod "right_bt" (Id "output")))
                                  (SConst "succeeded")))))
              (AddD "fail_output_count"
                    (Count (AddSexp
                              (Equal (Qual (Mod "left_bt" (Id "output")))
                                     (SConst "failed"))
                              (Sexp
                                 (Equal (Qual (Mod "right_bt" (Id "output")))
                                        (SConst "failed")))))
                    (LastD "output"
                           (Case
                              (AddCexp
                                 (Less (SConst "0")
                                       (Qual (Id "true_output_count")))
                                 (SConst "succeeded")
                                 (AddCexp
                                    (Less (SConst "1")
                                          (Qual (Id "fail_output_count")))
                                    (SConst "failed")
                                    (Cexp
                                       (BConst smvT)
                                       (SConst "running")))))))))
     ::nil).

  Definition bp_par2 :=
  Build_smv_module
    "bt_parallel2"
    ("left_bt"::"right_bt"::nil)
    ((VAR (LastV "enable" (TSimp TBool)))
     ::
     (ASSIGN
        (AddA (invar (Mod "left_bt" (Id "enable"))
                     (Qual (Id "enable")))
              (LastA (invar (Mod "right_bt" (Id "enable"))
                            (Qual (Id "enable"))))))
     ::
     (DEFINE
        (AddD "true_output_count"
              (Count (AddSexp
                        (Equal (Qual (Mod "left_bt" (Id "output")))
                               (SConst "succeeded"))
                        (Sexp
                           (Equal (Qual (Mod "right_bt" (Id "output")))
                                  (SConst "succeeded")))))
              (AddD "fail_output_count"
                    (Count (AddSexp
                              (Equal (Qual (Mod "left_bt" (Id "output")))
                                     (SConst "failed"))
                              (Sexp
                                 (Equal (Qual (Mod "right_bt" (Id "output")))
                                        (SConst "failed")))))
                    (LastD "output"
                           (Case
                              (AddCexp
                                 (Less (SConst "1")
                                       (Qual (Id "true_output_count")))
                                 (SConst "succeeded")
                                 (AddCexp
                                    (Less (SConst "0")
                                          (Qual (Id "fail_output_count")))
                                    (SConst "failed")
                                    (Cexp
                                       (BConst smvT)
                                       (SConst "running")))))))))
     ::nil).

  Definition rootName (t: btree) :=
    match t with
    | Skill s => X.skillName s
    | TRUE => "BTSucc"
    | Node _ n _ _ => n
    | Dec _ n _ => n
    end.

  Definition nodeName (k: nodeKind) :=
    match k with
    | Sequence => "bt_sequence"
    | Fallback => "bt_fallback"
    | Parallel1 => "bt_parallel1"
    | Parallel2 => "bt_parallel2"
    end.
  
  Definition decName (d: decKind) :=
    match d with
    | Not => "bt_not"
    | IsRunning => "bt_is_running"
    end.

  Fixpoint make_vars (t: btree): varlist :=
    match t with
    | Skill s => LastV (X.skillName s) (TComp (TMod "bt_skill"))
    | TRUE => LastV "t" (TComp (TMod "bt_TRUE"))
    | Node k name t1 t2 =>
      let x := varlist_app (make_vars t1) (make_vars t2) in
      AddV name
           (TComp (TModPar (nodeName k)
                           (AddP (Simple (Qual (Id (rootName t1))))
                                 (LastP (Simple (Qual (Id (rootName t2))))))))
           x
    | Dec d name t =>
      let x := make_vars t in
      AddV name
           (TComp (TModPar (decName d)
                           (LastP (Simple (Qual (Id (rootName t)))))))
           x
    end.

  Definition make_main (t: btree) :=
    let vars := make_vars t in
    Build_smv_module
      "main"
      nil
      ((VAR (AddV "tick_generator"
                  (TComp (TModPar "bt_tick_generator"
                                  (LastP (Simple (Qual (Id (rootName t)))))))
                  vars))
       ::nil).

  (* Modules for OCRA inteface *)

  Fixpoint mkop (lst: list X.skillSet) :=
    match lst with
    | nil => nil
    | s :: rest => cons ("from_" ++ (X.skillName s)) (mkop rest)
    end.
    
  Fixpoint mkov (lst: list X.skillSet) :=
    match lst with
    | nil => LastV "bt_main_inst" (TComp (TMod "bt_main"))
    | s :: rest => AddV ("to_" ++ (X.skillName s))
                        (TSimp bt_action_type)
                        (mkov rest)
    end.

  Fixpoint mkot (lst: list X.skillSet) :=
    match lst with
    | nil => (* will never happen *)
      (LastA (invar (Id "bt_main_inst") (BConst smvF)))
    | s :: nil =>
      (AddA
         (invar (Mod "bt_main_inst"
                     (Mod (X.skillName s)
                          (Id "output")))
                (Qual (Id ("from_" ++ (X.skillName s)))))
         (LastA (invar (Id ("to_" ++ (X.skillName s)))
                       (Case
                          (AddCexp (Equal (Qual (Mod "bt_main_inst"
                                                     (Mod (X.skillName s)
                                                          (Id "enable"))))
                                          (BConst smvT))
                                   (SConst "Enable")
                                   (Cexp (Equal (Qual (Mod "bt_main_inst"
                                                           (Mod (X.skillName s)
                                                                (Id "enable"))))
                                                (BConst smvF))
                                         (SConst "Reset")))))))
    | s :: rest =>
      (AddA
         (invar (Mod "bt_main_inst"
                     (Mod (X.skillName s)
                          (Id "output")))
                (Qual (Id ("from_" ++ (X.skillName s)))))
         (AddA (invar (Id ("to_" ++ (X.skillName s)))
                      (Case
                         (AddCexp (Equal (Qual (Mod "bt_main_inst"
                                                    (Mod (X.skillName s)
                                                         (Id "enable"))))
                                         (BConst smvT))
                                  (SConst "Enable")
                                  (Cexp (Equal (Qual (Mod "bt_main_inst"
                                                          (Mod (X.skillName s)
                                                               (Id "enable"))))
                                               (BConst smvF))
                                        (SConst "Reset")))))
               (mkot rest)))
    end.
  
  Definition ocra_bt_fsm (t: btree) :=
    Build_smv_module
      "BT_FSM"
      (mkop (sklist t))
      ((VAR (mkov (sklist t)))
       ::
       (ASSIGN (mkot (sklist t)))
       ::nil).

  Fixpoint mkparomain (l: list X.skillSet) :=
    match l with
    | nil => (* will never happen *)
      LastP (Simple (Qual (Id "")))
    | s :: nil =>
      LastP (Simple (Qual (Id ("from_" ++ (X.skillName s)))))
    | s :: rest =>
      AddP (Simple (Qual (Id ("from_" ++ (X.skillName s)))))
           (mkparomain rest)
    end.

  Fixpoint mkvaromain (lst: list X.skillSet) :=
    match lst with
    | nil => (* will never happen *)
      LastV "" (TSimp bt_output_type)
    | s :: nil =>
      LastV ("from_" ++ (X.skillName s))
            (TSimp bt_output_type)
    | s :: rest =>
      AddV ("from_" ++ (X.skillName s))
           (TSimp bt_output_type)
           (mkvaromain rest)
    end.

  Fixpoint mkdefomain (lst: list X.skillSet) :=
    match lst with
    | nil => (* will never happen *)
      LastD "" (Qual (Id ""))
    | s :: nil =>
      LastD ("to_" ++ (X.skillName s))
            (Qual (Mod "BT_FSM_inst"
                       (Id ("to_" ++ (X.skillName s)))))
    | s :: rest =>
      AddD ("to_" ++ (X.skillName s))
           (Qual (Mod "BT_FSM_inst"
                      (Id ("to_" ++ (X.skillName s)))))
           (mkdefomain rest)
    end.
  
  Definition ocra_main (t: btree) :=
    Build_smv_module
      "main"
      nil
      ((VAR (AddV "BT_FSM_inst" (TComp (TModPar "BT_FSM"
                                                (mkparomain (sklist t))))
                  (mkvaromain (sklist t))))
       ::
       (DEFINE (mkdefomain (sklist t)))
       ::
       nil).

  Definition make_spec (t: btree) :=
    bp_skill :: bp_TRUE :: bp_bin_seq :: bp_bin_fb :: bp_par1 :: bp_par2
    :: bp_not :: bp_isRunning :: bp_tick_generator :: (make_main t)
    :: (ocra_bt_fsm t) :: (ocra_main t) :: nil.

End BT_bin_spec.

(* For arbitrary-branching BTs we adopt a more fine-grained approach:
   we generate on the fly only the modules which are really needed *)

Inductive modtype :=
| Skmod: modtype
| TRUEmod: modtype
| Seqmod: nat -> modtype
| Fbmod: nat -> modtype
| Parmod: nat -> nat -> modtype   (* threshold, n. of args *)
| Notmod: modtype
| Runmod: modtype.

Theorem modtype_dec: forall x y:modtype, {x = y} + {x <> y}.
  decide equality; apply PeanoNat.Nat.eq_dec.
Defined.

(* This is used for placeholders when translating non-normalized BTs *)
Definition bp_identity (name: string) :=
  Build_smv_module
    name
    ("bt"::nil)
    ((VAR (LastV "enable" (TSimp TBool)))
     ::
     (ASSIGN (LastA (invar (Mod "bt" (Id "enable"))
                           (Qual (Id "enable")))))
     ::
     (DEFINE (LastD "output" (Qual (Mod "bt" (Id "output")))))
     ::nil).

Module BT_gen_spec (X: BT_SIG).

  Include BT_general X.

  Definition rootName (t: btree) :=
    match t with
    | Skill s => X.skillName s
    | TRUE => "BTSucc"
    | Node _ n _ => n
    | Dec _ n _ => n
    end.

  (* NOTE: this works only for n<100 ! *)
  Definition string_of_nat (n: nat) :=
    if n <? 10 then
      (String (Ascii.ascii_of_nat (n + 48))
              EmptyString)
    else if n<? 100 then
           let (q,r) := (n / 10, n mod 10) in
           (String (Ascii.ascii_of_nat (q + 48))
                   (String (Ascii.ascii_of_nat (r + 48))
                           EmptyString))
         else
           "100".

  Definition nodeName (k: nodeKind) (n: nat) :=
    match k with
    | Sequence => append "bt_sequence_"
                         (string_of_nat n)
    | Fallback => append "bt_fallback_"
                         (string_of_nat n)
    | Parallel t => append (append "bt_parallel"
                                   (string_of_nat t))
                           (append "_"
                                   (string_of_nat n))
    end.

  Definition decName (d: decKind) :=
    match d with
    | Not => "bt_not"
    | IsRunning => "bt_is_running"
    end.

  (* This function scans a BT compiling a list of the needed modules *)
  
  Fixpoint addmod (t: btree) (s: ListSet.set modtype) :=
    match t with
    | Skill _ => set_add modtype_dec Skmod s
    | TRUE => set_add modtype_dec TRUEmod s
    | Node k _ f => let l := len f in
                    addmod_f f (set_add modtype_dec
                                        match k with
                                        | Sequence => Seqmod l
                                        | Fallback => Fbmod l
                                        | Parallel n => Parmod n l
                                        end
                                        s)
    | Dec k _ t' => addmod t' (set_add modtype_dec
                                       match k with
                                       | Not => Notmod
                                       | IsRunning => Runmod
                                       end
                                       s)
    end
  with addmod_f (f: btforest) (s: ListSet.set modtype) :=
         match f with
         | Child t => addmod t s
         | Add t1 rest => addmod_f rest (addmod t1 s)
         end.

  (* Helper functions to generate the non-boilerplate SMV modules *)
  
  Fixpoint mk_param_list (l: nat) :=
    match l with
    | O => nil
    | S p => (cons ("bt" ++ string_of_nat l) (mk_param_list p))
    end.

  Fixpoint mk_seq_invar (l: nat) :=
    match l with
    | 0 => (* will never happen *)
      (LastA (invar (Id "enable") (BConst smvF)))
    | 1 =>
      (LastA (invar (Mod "bt1" (Id "enable"))
                    (Equal (Qual (Mod "bt2" (Id "output")))
                           (SConst "succeeded"))))
    | S p =>
      (AddA (invar (Mod ("bt" ++ string_of_nat (S p)) (Id "enable"))
                   (Equal (Qual (Mod ("bt" ++ string_of_nat (S (S p))) (Id "output")))
                          (SConst "succeeded")))
            (mk_seq_invar p))
    end.

  Fixpoint mk_seq_trans (l: nat) :=
    match l with
    | 0 => (* will never happen *)
      (Cexp (BConst smvT) (BConst smvT))
    | 1 =>
      (Cexp (BConst smvT)
            (Qual (Mod "bt1" (Id "output"))))
    | S p =>
      (AddCexp (Or (Equal (Qual (Mod ("bt" ++ string_of_nat l) (Id "output")))
                          (SConst "running"))
                   (Equal (Qual (Mod ("bt" ++ string_of_nat l) (Id "output")))
                          (SConst "failed")))
               (Qual (Mod ("bt" ++ string_of_nat l) (Id "output")))
               (mk_seq_trans p))
    end.

  Definition make_sequence (l: nat) :=
    match l with
    | 0 => bp_TRUE (* will never happen *)
    | 1 => bp_identity (nodeName Sequence 1)
    | S p =>
      Build_smv_module
        (nodeName Sequence l)
        (mk_param_list l)
        ((VAR (LastV "enable" (TSimp TBool)))
         ::
         (ASSIGN (AddA (invar (Mod ("bt" ++ string_of_nat l) (Id "enable"))
                              (Qual (Id "enable")))
                       (mk_seq_invar p)))
         ::
         (DEFINE (LastD "output" (Case (mk_seq_trans l))))
         ::nil)
    end.

  Fixpoint mk_fb_invar (l: nat) :=
    match l with
    | 0 => (* will never happen *)
      (LastA (invar (Id "enable") (BConst smvF)))
    | 1 =>
      (LastA (invar (Mod "bt1" (Id "enable"))
                    (Equal (Qual (Mod "bt2" (Id "output")))
                           (SConst "failed"))))
    | S p =>
      (AddA (invar (Mod ("bt" ++ string_of_nat (S p)) (Id "enable"))
                   (Equal (Qual (Mod ("bt" ++ string_of_nat (S (S p))) (Id "output")))
                          (SConst "failed")))
            (mk_fb_invar p))
    end.

  Fixpoint mk_fb_trans (l: nat) :=
    match l with
    | 0 => (* will never happen *)
      (Cexp (BConst smvT) (BConst smvT))
    | 1 =>
      (Cexp (BConst smvT)
            (Qual (Mod "bt1" (Id "output"))))
    | S p =>
      (AddCexp (Or (Equal (Qual (Mod ("bt" ++ string_of_nat l) (Id "output")))
                          (SConst "running"))
                   (Equal (Qual (Mod ("bt" ++ string_of_nat l) (Id "output")))
                          (SConst "succeeded")))
               (Qual (Mod ("bt" ++ string_of_nat l) (Id "output")))
               (mk_fb_trans p))
    end.

  Definition make_fallback (l: nat) :=
    match l with
    | 0 => bp_TRUE (* will never happen *)
    | 1 => bp_identity (nodeName Fallback 1)
    | S p =>
      Build_smv_module
        (nodeName Fallback l)
        (mk_param_list l)
        ((VAR (LastV "enable" (TSimp TBool)))
         ::
         (ASSIGN (AddA (invar (Mod ("bt" ++ string_of_nat l) (Id "enable"))
                              (Qual (Id "enable")))
                       (mk_fb_invar p)))
         ::
         (DEFINE (LastD "output" (Case (mk_fb_trans l))))
         ::nil)
    end.

  Fixpoint mk_par_invar (l: nat) :=
    match l with
    | 0 => (* will never happen *)
      (LastA (invar (Id "enable") (BConst smvF)))
    | 1 =>
      (LastA (invar (Mod "bt1" (Id "enable"))
                    (Qual (Id "enable"))))
    | S p =>
      (AddA (invar (Mod ("bt" ++ string_of_nat (S p)) (Id "enable"))
                   (Qual (Id "enable")))
            (mk_par_invar p))
    end.

  Fixpoint mk_countlist (l: nat) (res: string) :=
    match l with
    | 0 => (Sexp (BConst smvF)) (* will never happen *)
    | 1 => (Sexp (Equal (Qual (Mod ("bt" ++ string_of_nat l) (Id "output")))
                        (SConst res)))
    | S p => (AddSexp
                (Equal (Qual (Mod ("bt" ++ string_of_nat l) (Id "output")))
                       (SConst res))
                (mk_countlist p res))
    end.

  Definition make_parallel (n l: nat) :=
    match l with
    | 0 => bp_TRUE (* will never happen *)
    | 1 => if n =? 0 then
             Build_smv_module
               "parallel_0_1"
               ("bt"::nil)
               ((VAR (LastV "enable" (TSimp TBool)))
                ::
                (ASSIGN (LastA (invar (Mod "bt" (Id "enable"))
                                      (Qual (Id "enable")))))
                ::
                (DEFINE (LastD "output" (SConst "succeeded")))
                ::nil)
           else bp_identity (nodeName (Parallel 1) 1)
    | S p =>
      Build_smv_module
        (nodeName (Parallel n) l)
        (mk_param_list l)
        ((VAR (LastV "enable" (TSimp TBool)))
         ::
         (ASSIGN (mk_par_invar (S p)))
         ::
         (DEFINE
            (AddD "true_output_count"
                  (Count (mk_countlist l "succeeded"))
                  (AddD "fail_output_count"
                        (Count (mk_countlist l "failed"))
                        (LastD "output"
                               (Case
                                  (AddCexp
                                     (Less (SConst (string_of_nat n))
                                           (Sum (Qual (Id "true_output_count"))
                                                (SConst "1")))
                                     (SConst "succeeded")
                                     (AddCexp
                                        (Less (SConst (string_of_nat l))
                                              (Sum (Qual (Id "fail_output_count"))
                                                   (SConst (string_of_nat n))))
                                        (SConst "failed")
                                        (Cexp
                                           (BConst smvT)
                                           (SConst "running")))))))))
         ::nil)
    end.

  Definition make_mod (t: modtype): smv_module :=
    match t with
    | Skmod => bp_skill
    | TRUEmod => bp_TRUE
    | Seqmod l => make_sequence l
    | Fbmod l => make_fallback l
    | Parmod n l => make_parallel n l
    | Notmod => bp_not
    | Runmod => bp_isRunning
    end.

  (* Functions to generate the main module *)

  Fixpoint make_mod_list (l: list modtype): list smv_module :=
    match l with
    | nil => nil
    | m :: rest => cons (make_mod m) (make_mod_list rest)
    end.

  Fixpoint make_paramlist (f: btforest) :=
    match f with
    | Child t => (LastP (Simple (Qual (Id (rootName t)))))
    | Add t1 rest => (AddP (Simple (Qual (Id (rootName t1))))
                           (make_paramlist rest))
    end.

  Fixpoint make_vars (t: btree) :=
    match t with
    | Skill s => LastV (X.skillName s) (TComp (TMod "bt_skill"))
    | TRUE => LastV "t" (TComp (TMod "bt_TRUE"))
    | Node k name f =>
      let params := make_paramlist f in
      let vars := make_vars_f f in
      AddV name
           (TComp (TModPar (nodeName k (len f)) params))
           vars
    | Dec d name t =>
      let vars := make_vars t in
      AddV name
           (TComp (TModPar (decName d)
                           (LastP (Simple (Qual (Id (rootName t)))))))
           vars
    end
  with make_vars_f (f: btforest) :=
         match f with
         | Child t => (make_vars t)
         | Add t1 rest => varlist_app (make_vars t1) (make_vars_f rest)
         end.

  Definition make_main (t: btree) :=
    let vars := make_vars t in
    Build_smv_module
      "bt_main"
      nil
      ((VAR (AddV "tick_generator"
                  (TComp (TModPar "bt_tick_generator"
                                  (LastP (Simple (Qual (Id (rootName t)))))))
                  vars))
       ::nil).

  (* Modules for OCRA inteface *)

  Fixpoint mkop (lst: list X.skillSet) :=
    match lst with
    | nil => nil
    | s :: rest => cons ("from_" ++ (X.skillName s)) (mkop rest)
    end.
    
  Fixpoint mkov (lst: list X.skillSet) :=
    match lst with
    | nil => LastV "bt_main_inst" (TComp (TMod "bt_main"))
    | s :: rest => AddV ("to_" ++ (X.skillName s))
                        (TSimp bt_action_type)
                        (mkov rest)
    end.

  Fixpoint mkot (lst: list X.skillSet) :=
    match lst with
    | nil => (* will never happen *)
      (LastA (invar (Id "bt_main_inst") (BConst smvF)))
    | s :: nil =>
      (AddA
         (invar (Mod "bt_main_inst"
                     (Mod (X.skillName s)
                          (Id "output")))
                (Qual (Id ("from_" ++ (X.skillName s)))))
         (LastA (invar (Id ("to_" ++ (X.skillName s)))
                       (Case
                          (AddCexp (Equal (Qual (Mod "bt_main_inst"
                                                     (Mod (X.skillName s)
                                                          (Id "enable"))))
                                          (BConst smvT))
                                   (SConst "Enable")
                                   (Cexp (Equal (Qual (Mod "bt_main_inst"
                                                           (Mod (X.skillName s)
                                                                (Id "enable"))))
                                                (BConst smvF))
                                         (SConst "Reset")))))))
    | s :: rest =>
      (AddA
         (invar (Mod "bt_main_inst"
                     (Mod (X.skillName s)
                          (Id "output")))
                (Qual (Id ("from_" ++ (X.skillName s)))))
         (AddA (invar (Id ("to_" ++ (X.skillName s)))
                      (Case
                         (AddCexp (Equal (Qual (Mod "bt_main_inst"
                                                    (Mod (X.skillName s)
                                                         (Id "enable"))))
                                         (BConst smvT))
                                  (SConst "Enable")
                                  (Cexp (Equal (Qual (Mod "bt_main_inst"
                                                          (Mod (X.skillName s)
                                                               (Id "enable"))))
                                               (BConst smvF))
                                        (SConst "Reset")))))
               (mkot rest)))
    end.
  
  Definition ocra_bt_fsm (t: btree) :=
    Build_smv_module
      "BT_FSM"
      (mkop (sklist t))
      ((VAR (mkov (sklist t)))
       ::
       (ASSIGN (mkot (sklist t)))
       ::nil).

  Fixpoint mkparomain (l: list X.skillSet) :=
    match l with
    | nil => (* will never happen *)
      LastP (Simple (Qual (Id "")))
    | s :: nil =>
      LastP (Simple (Qual (Id ("from_" ++ (X.skillName s)))))
    | s :: rest =>
      AddP (Simple (Qual (Id ("from_" ++ (X.skillName s)))))
           (mkparomain rest)
    end.

  Fixpoint mkvaromain (lst: list X.skillSet) :=
    match lst with
    | nil => (* will never happen *)
      LastV "" (TSimp bt_output_type)
    | s :: nil =>
      LastV ("from_" ++ (X.skillName s))
            (TSimp bt_output_type)
    | s :: rest =>
      AddV ("from_" ++ (X.skillName s))
           (TSimp bt_output_type)
           (mkvaromain rest)
    end.

  Fixpoint mkdefomain (lst: list X.skillSet) :=
    match lst with
    | nil => (* will never happen *)
      LastD "" (Qual (Id ""))
    | s :: nil =>
      LastD ("to_" ++ (X.skillName s))
            (Qual (Mod "BT_FSM_inst"
                       (Id ("to_" ++ (X.skillName s)))))
    | s :: rest =>
      AddD ("to_" ++ (X.skillName s))
           (Qual (Mod "BT_FSM_inst"
                      (Id ("to_" ++ (X.skillName s)))))
           (mkdefomain rest)
    end.
  
  Definition ocra_main (t: btree) :=
    Build_smv_module
      "main"
      nil
      ((VAR (AddV "BT_FSM_inst" (TComp (TModPar "BT_FSM"
                                                (mkparomain (sklist t))))
                  (mkvaromain (sklist t))))
       ::
       (DEFINE (mkdefomain (sklist t)))
       ::
       nil).
  
  Definition make_spec (t: btree): list smv_module :=
    let needed := addmod t (empty_set modtype) in
    let modlist := make_mod_list needed in
    app modlist (bp_tick_generator :: (make_main t)
                 :: (ocra_bt_fsm t) :: (ocra_main t) :: nil).

End BT_gen_spec.


(* Program extraction for the BT specification builder *)

Require Import Extraction.
Require ExtrOcamlBasic ExtrOcamlString.
Extract Inductive nat => "int" ["0" "succ"]
                               "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Constant plus => "( + )".

Extraction "infra/btbspec.ml" BT_bin_spec translate_spec.
Extraction "infra/btgspec.ml" BT_gen_spec translate_spec.
