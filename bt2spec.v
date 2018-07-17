Require Import bt micro_smv spec_extr.
Require Import List String.
Open Scope string_scope.

Module BT_bin_spec (X: BT_SIG).

  Include BT_binary X.

  Definition RootName (t: btree) :=
    match t with
    | Skill s => X.skillName s
    | TRUE => "BTSucc"
    | Node _ n _ _ => n
    | Dec _ n _ => n
    end.

  Definition bt_input_type :=
    (TEnum ("Runn"::"Fail"::"Succ"::nil)).

  Definition bt_output_type :=
    (TSimp (TEnum ("none"::"running"::"failed"::"succeeded"::nil))).

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
       (VAR (AddV "output" bt_output_type
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

  Definition boiler_sequence :=
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

  Definition boiler_fallback :=
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

  Definition boiler_par1 :=
    Build_smv_module
      "bt_parallel1"
      ("left_bt"::"right_bt"::nil)
      ((VAR (AddV "enable" (TSimp TBool)
                  (LastV "left_bt_stored_output" bt_output_type)))
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
                  (LastV "left_bt_stored_output" bt_output_type)))
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

  Definition nodename (k: nodeKind) :=
    match k with
    | Sequence => "bt_sequence"
    | Fallback => "bt_fallback"
    | Parallel1 => "bt_parallel1"
    | Parallel2 => "bt_parallel2"
    end.
  
  Definition decname (d: decKind) :=
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
           (TComp (TModPar (nodename k)
                           (AddP (Simple (Qual (Id (RootName t1))))
                                 (LastP (Simple (Qual (Id (RootName t2))))))))
           x
    | Dec d name t =>
      let x := make_vars t in
      AddV name
           (TComp (TModPar (decname d)
                           (LastP (Simple (Qual (Id (RootName t)))))))
           x
    end.

  Definition make_main (t: btree) :=
    let l := make_vars t in
    Build_smv_module
      "main"
      nil
      (cons (VAR (AddV "tick_generator"
                       (TComp (TModPar "bt_tick_generator"
                                       (LastP (Simple (Qual (Id (RootName t)))))))
                       l))
            nil).

  Definition make_spec (t: btree) :=
    boiler_tick_generator :: boiler_skill :: boiler_TRUE ::
    boiler_sequence :: boiler_fallback :: boiler_par1 :: boiler_par2 ::
    boiler_not :: boiler_isRunning :: (make_main t) :: nil.

End BT_bin_spec.





