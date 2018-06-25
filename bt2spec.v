Require Import bt micro_smv spec_extr.
Require Import List String.
Open Scope string_scope.

Module BT_bin_spec (X: BT_SIG).

  Include BT_binary X.

  Definition RootName (t: btree) :=
    match t with
    | Skill s => X.SkillName s
    | TRUE => "BTSucc"
    | node _ n _ _ => n
    | dec _ n _ => n
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

(*  Definition boilerP1 := *)

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

  
(*  Definition generate_name (k: NodeKind) (t1: btree) (t2: btree) :=
    match k with
    | Sequence => "seq" ++ (RootName t1) ++ (RootName t2)
    | Fallback => "fb" ++ (RootName t1) ++ (RootName t2)
    | Parallel1 => "par1" ++ (RootName t1) ++ (RootName t2)
    | Parallel2 => "par2" ++ (RootName t1) ++ (RootName t2)
    end.
  *)
  Definition nodename (k: NodeKind) :=
    match k with
    | Sequence => "bt_sequence"
    | Fallback => "bt_fallback"
    | Parallel1 => "bt_parallel1"
    | Parallel2 => "bt_parallel2"
    end.
  
  Definition decname (d: DecKind) :=
    match d with
    | Not => "bt_not"
    | isRunning => "bt_is_running"
    end.

  Fixpoint make_vars (t: btree): varlist :=
    match t with
    | Skill s => LastV (X.SkillName s) (TComp (TMod "bt_skill"))
    | TRUE => LastV "t" (TComp (TMod "bt_TRUE"))
    | node k name t1 t2 =>
      let x := varlist_app (make_vars t1) (make_vars t2) in
      AddV name
           (TComp (TModPar (nodename k)
                           (AddP (Simple (Qual (Id (RootName t1))))
                                 (LastP (Simple (Qual (Id (RootName t2))))))))
           x
    | dec d name t =>
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
    boiler_sequence :: boiler_fallback :: (* par1 par2 *)
    boiler_not :: boiler_isRunning :: (make_main t) :: nil.
  
End BT_bin_spec.

(* experiments *)

Inductive my_skills :=
  sk1 | sk2 | sk3 | sk4.
Definition my_names (x: my_skills) :=
  match x with
  | sk1 => "goto_kitchen"
  | sk2 => "find_bottle"
  | sk3 => "fetch_bottle"
  | sk4 => "ask_help"
  end.

Module ex_skills.

  Definition SkillSet := my_skills.
  Definition SkillName := my_names.

End ex_skills.

Module my_bt := BT_bin_spec ex_skills.

Import my_bt.

Definition ex1 := (Skill sk1).

Definition ex2 :=
  (node Sequence "prova" (Skill sk1)
        (node Sequence "prova2" (Skill sk2) (Skill sk3))).

Definition ex3 :=
  (node Fallback "fallback" (Skill sk3) (Skill sk4)).

Definition ex4 :=
  (node Sequence "myseq" (Skill sk1)
        (dec Not "nego" (node Parallel1 "para" (Skill sk2) (Skill sk3)))).

Definition sc1 :=
  (node Fallback "do_with_help"
        (node Sequence "go_and_fetch_bottle" (Skill sk1)
              (node Sequence "find_and_fetch_bottle" (Skill sk2) (Skill sk3)))
        (Skill sk4)).

Compute translate (make_main sc1).

Compute map translate (make_spec sc1).


