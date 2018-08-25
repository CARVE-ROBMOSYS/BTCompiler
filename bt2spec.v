Require Import bt micro_smv spec_extr.
Require Import List ListSet String.
Open Scope string_scope.

Definition bt_input_type :=
  (TEnum ("Runn"::"Fail"::"Succ"::nil)).

Definition bt_output_type :=
  (TEnum ("none"::"running"::"failed"::"succeeded"::nil)).

  (* boilerplate modules *)

  Definition boiler_tick_generator :=
    Build_smv_module
      "bt_tick_generator"
      ("top_level_bt"::nil)
      ((ASSIGN (AddA (init (Mod "top_level_bt" (Id "enable"))
                           (BConst smvT))
                     (LastA (next (Mod "top_level_bt" (Id "enable"))
                                  (Simple (Neg (Equal (Qual (Mod "top_level_bt" (Id "output")))
                                                      (SConst "none"))))))))
       ::nil).

  Definition boiler_skill :=
    Build_smv_module
      "bt_skill"
      nil
      ((IVAR (LastI "input" bt_input_type))
       ::
       (VAR (AddV "output" (TSimp bt_output_type)
                  (LastV "enable" (TSimp TBool))))
       ::
       (ASSIGN (AddA (init (Id "output") (SConst "none"))
                     (LastA (next (Id "output")
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

  Definition boiler_TRUE :=
    Build_smv_module
      "bt_TRUE"
      nil
      ((VAR (LastV "enable" (TSimp TBool)))
       ::
       (DEFINE (LastD "output" (SConst "succeeded")))
       ::nil).

  Definition boiler_identity :=
    Build_smv_module
      "bt_id"
      ("bt"::nil)
      ((VAR (LastV "enable" (TSimp TBool)))
       ::
       (ASSIGN (LastA (invar (Mod "bt" (Id "enable")) (Qual (Id "enable")))))
       ::
       (DEFINE (LastD "output" (Case (Cexp (BConst smvT)
                                           (Qual (Mod "bt" (Id "output")))))))
       ::nil).

  Definition boiler_sequence :=
    Build_smv_module
      "bt_sequence_2"
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

  Definition boiler_fallback :=
    Build_smv_module
      "bt_fallback_2"
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

  Definition boiler_par1 :=
    Build_smv_module
      "bt_parallel1"
      ("left_bt"::"right_bt"::nil)
      ((VAR (AddV "enable" (TSimp TBool)
                  (LastV "left_bt_stored_output" (TSimp bt_output_type))))
       ::
       (ASSIGN
          (AddA (invar (Mod "left_bt" (Id "enable"))
                       (Qual (Id "enable")))
                (AddA (invar (Mod "right_bt" (Id "enable"))
                             (Qual (Id "is_left_bt_active")))
                      (AddA (init (Id "left_bt_stored_output")
                                  (Qual (Id "none")))
                            (LastA (next (Id "left_bt_stored_output")
                                         (Simple
                                            (Case
                                               (AddCexp (Qual (Id "is_left_bt_active"))
                                                        (Qual (Mod "left_bt" (Id "output")))
                                                        (Cexp (BConst smvT)
                                                              (Qual (Id "left_bt_stored_output"))))))))))))
       ::
       (DEFINE
          (AddD "is_left_bt_active"
                (Neg (Equal (Qual (Mod "left_bt" (Id "output")))
                            (SConst "none")))
                (AddD "is_right_bt_active"
                      (Neg (Equal (Qual (Mod "right_bt" (Id "output")))
                                  (SConst "none")))
                      (AddD "true_output_count"
                            (Count (AddSexp
                                      (Equal (Qual (Id "left_bt_stored_output"))
                                             (SConst "succeeded"))
                                      (Sexp
                                         (Equal (Qual (Mod "right_bt" (Id "output")))
                                                (SConst "succeeded")))))
                            (AddD "running_output_count"
                                  (Count (AddSexp
                                            (Equal (Qual (Id "left_bt_stored_output"))
                                                   (SConst "running"))
                                            (Sexp
                                               (Equal (Qual (Mod "right_bt" (Id "output")))
                                                      (SConst "running")))))
                                  (LastD "output"
                                         (Case
                                            (AddCexp
                                               (And (Qual (Id "is_right_bt_active"))
                                                    (Less (SConst "0")
                                                          (Qual (Id "true_output_count"))))
                                               (SConst "succeeded")
                                               (AddCexp
                                                  (And (Qual (Id "is_right_bt_active"))
                                                       (Less (Sum (Qual (Id "true_output_count"))
                                                                  (Qual (Id "running_output_count")))
                                                             (SConst "1")))
                                                  (SConst "failed")
                                                  (AddCexp (Qual (Id "is_right_bt_active"))
                                                           (SConst "running")
                                                           (Cexp
                                                              (BConst smvT)
                                                              (SConst "none"))))))))))))
       ::nil).

  Definition boiler_par2 :=
    Build_smv_module
      "bt_parallel2"
      ("left_bt"::"right_bt"::nil)
      ((VAR (AddV "enable" (TSimp TBool)
                  (LastV "left_bt_stored_output" (TSimp bt_output_type))))
       ::
       (ASSIGN
          (AddA (invar (Mod "left_bt" (Id "enable"))
                       (Qual (Id "enable")))
                (AddA (invar (Mod "right_bt" (Id "enable"))
                             (Qual (Id "is_left_bt_active")))
                      (AddA (init (Id "left_bt_stored_output")
                                  (Qual (Id "none")))
                            (LastA (next (Id "left_bt_stored_output")
                                         (Simple
                                            (Case
                                               (AddCexp (Qual (Id "is_left_bt_active"))
                                                        (Qual (Mod "left_bt" (Id "output")))
                                                        (Cexp (BConst smvT)
                                                              (Qual (Id "left_bt_stored_output"))))))))))))
       ::
       (DEFINE
          (AddD "is_left_bt_active"
                (Neg (Equal (Qual (Mod "left_bt" (Id "output")))
                            (SConst "none")))
                (AddD "is_right_bt_active"
                      (Neg (Equal (Qual (Mod "right_bt" (Id "output")))
                                  (SConst "none")))
                      (AddD "true_output_count"
                            (Count (AddSexp
                                      (Equal (Qual (Id "left_bt_stored_output"))
                                             (SConst "succeeded"))
                                      (Sexp
                                         (Equal (Qual (Mod "right_bt" (Id "output")))
                                                (SConst "succeeded")))))
                            (AddD "running_output_count"
                                  (Count (AddSexp
                                            (Equal (Qual (Id "left_bt_stored_output"))
                                                   (SConst "running"))
                                            (Sexp
                                               (Equal (Qual (Mod "right_bt" (Id "output")))
                                                      (SConst "running")))))
                                  (LastD "output"
                                         (Case
                                            (AddCexp
                                               (And (Qual (Id "is_right_bt_active"))
                                                    (Less (SConst "1")
                                                          (Qual (Id "true_output_count"))))
                                               (SConst "succeeded")
                                               (AddCexp
                                                  (And (Qual (Id "is_right_bt_active"))
                                                       (Less (Sum (Qual (Id "true_output_count"))
                                                                  (Qual (Id "running_output_count")))
                                                             (SConst "2")))
                                                  (SConst "failed")
                                                  (AddCexp (Qual (Id "is_right_bt_active"))
                                                           (SConst "running")
                                                           (Cexp
                                                              (BConst smvT)
                                                              (SConst "none"))))))))))))
       ::nil).

  Definition boiler_not :=
    Build_smv_module
      "bt_not"
      ("child_bt"::nil)
      ((VAR (LastV "enable" (TSimp TBool)))
       ::
       (ASSIGN (LastA (invar (Mod "child_bt" (Id "enable"))
                             (Qual (Id "enable")))))
       ::
       (DEFINE (LastD "output" (Case
                                  (AddCexp (Equal (Qual (Mod "child_bt" (Id "output")))
                                                  (SConst "failed"))
                                           (SConst "succeeded")
                                           (AddCexp (Equal (Qual (Mod "child_bt" (Id "output")))
                                                           (SConst "succeeded"))
                                                    (SConst "failed")
                                                    (Cexp (BConst smvT)
                                                          (Qual (Mod "child_bt" (Id "output")))))))))
       ::nil).
    
  Definition boiler_isRunning := 
    Build_smv_module
      "bt_isRunning"
      ("child_bt"::nil)
      ((VAR (LastV "enable" (TSimp TBool)))
       ::
       (ASSIGN (LastA (invar (Mod "child_bt" (Id "enable"))
                             (Qual (Id "enable")))))
       ::
       (DEFINE (LastD "output" (Case
                                  (AddCexp (Equal (Qual (Mod "child_bt" (Id "output")))
                                                  (SConst "running"))
                                           (SConst "succeeded")
                                           (AddCexp (Equal (Qual (Mod "child_bt" (Id "output")))
                                                           (SConst "none"))
                                                    (SConst "none")
                                                    (Cexp (BConst smvT)
                                                          (SConst "failed")))))))
       ::nil).


Module BT_bin_spec (X: BT_SIG).

  Include BT_binary X.

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

  Definition make_spec (t: btree) :=
    boiler_tick_generator :: boiler_skill :: boiler_TRUE ::
    boiler_sequence :: boiler_fallback :: boiler_par1 :: boiler_par2 ::
    boiler_not :: boiler_isRunning :: (make_main t) :: nil.

End BT_bin_spec.

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

Module BT_gen_spec (X: BT_SIG).

  Include BT_general X.

  Definition rootName (t: btree) :=
    match t with
    | Skill s => X.skillName s
    | TRUE => "BTSucc"
    | Node _ n _ => n
    | Dec _ n _ => n
    end.

  (* NOTE: currently this works as expected only for n<10 ! *)
  Definition string_of_nat (n: nat) :=
    (String (Ascii.ascii_of_nat (n + 48))
            EmptyString).

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
(*
  Fixpoint mk_seq_invar (l: nat) :=
    match l with
    | 0 =>    (* this case will never happen, so any term will do *)
      (LastA (invar (Id "enable") (BConst smvF)))
    | 1 =>
      (LastA (invar (Mod "bt1" (Id "enable"))
                    (Qual (Id "enable"))))
    | (S p) =>
      (AddA (invar (Mod ("bt" ++ string_of_nat (S p)) (Id "enable"))
                   (Equal (Qual (Mod ("bt" ++ string_of_nat p) (Id "output")))
                          (SConst "succeeded")))
            (mk_seq_invar p))
    end.

  Fixpoint mk_seq_trans (l i: nat) :=
    match i with
    | 0 =>
      (Cexp (BConst smvT)
            (Qual (Mod ("bt" ++ string_of_nat l) (Id "output"))))
    | (S p) =>
      (AddCexp (Or (Equal (Qual (Mod ("bt" ++ string_of_nat (S p)) (Id "output")))
                          (SConst "running"))
                   (Equal (Qual (Mod ("bt" ++ string_of_nat (S p)) (Id "output")))
                          (SConst "failed")))
               (Qual (Mod ("bt" ++ string_of_nat (S p)) (Id "output")))
               (mk_seq_trans l p))
    end.

  Definition make_sequence (l: nat) :=
    Build_smv_module
      (nodeName Sequence l)
      (rev (mk_param_list l))
      ((VAR (LastV "enable" (TSimp TBool)))
       ::
       (ASSIGN (mk_seq_invar l))
       ::
       (DEFINE (LastD "output" (Case (mk_seq_trans l (pred l)))))
       ::nil).

  Compute (make_sequence 1).

   
MODULE bt_sequence_3(bt1, bt2, bt3)
VAR
  enable : boolean;
ASSIGN
  bt3.enable := bt2.output = succeeded;
  bt2.enable := bt1.output = succeeded;
  bt1.enable := enable;
DEFINE
  output := case
  bt2.output = running | bt2.output = failed : bt2.output;
  bt1.output = running | bt1.output = failed : bt1.output;
  TRUE : bt3.output;
  esac;

Altro approccio:
*)

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
    | 0 => boiler_TRUE
    | 1 => boiler_identity
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
    | 0 => boiler_TRUE
    | 1 => boiler_identity
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

(*  Compute (translate (make_fallback 3)). *)

  Definition make_parallel (n l: nat) :=
    match l with
    | 0 => boiler_TRUE
    | 1 => boiler_identity
    | S p =>
      Build_smv_module
        (nodeName (Parallel n) l)
        (cons "threshold" (mk_param_list l))
        ((VAR (LastV "enable" (TSimp TBool)))
         ::
         (ASSIGN (AddA (invar (Mod ("bt" ++ string_of_nat l) (Id "enable"))
                              (Qual (Id "enable")))
                       (mk_fb_invar p)))
         ::
         (DEFINE (LastD "output" (Case (mk_fb_trans l))))
         ::nil)
    end.


  Definition make_mod (t: modtype): smv_module :=
    match t with
    | Skmod => boiler_skill
    | TRUEmod => boiler_TRUE
    | Seqmod l => make_sequence l
    | Fbmod l => make_fallback l
    | Parmod n l => if Nat.eqb l 2 then
                      (if Nat.eqb n 1 then boiler_par1 else boiler_par2)
                    else boiler_TRUE  (* to be implemented *)
    | Notmod => boiler_not
    | Runmod => boiler_isRunning
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
      "main"
      nil
      ((VAR (AddV "tick_generator"
                  (TComp (TModPar "bt_tick_generator"
                                  (LastP (Simple (Qual (Id (rootName t)))))))
                  vars))
       ::nil).

  Definition make_spec (t: btree): list smv_module :=
    let needed := addmod t (empty_set modtype) in
    let modlist := make_mod_list needed in
    app modlist (boiler_tick_generator :: (make_main t) :: nil).

End BT_gen_spec.
  
(* Program extraction for the BT specification builder *)

Require Import Extraction.
Require ExtrOcamlBasic ExtrOcamlString.
Extract Inductive nat => "int" ["0" "succ"]
                               "(fun fO fS n -> if n=0 then fO () else fS (n-1))".
Extract Constant plus => "( + )".

Extraction "infra/btspec.ml" BT_bin_spec translate_spec.
Extraction "infra/btgspec.ml" BT_gen_spec translate_spec.
