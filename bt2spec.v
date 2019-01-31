Require Import bt micro_smv spec_extr.
Require Import Arith List ListSet String.
Open Scope string_scope.

(* Utility functions to convert between nat and string *)

Definition string_of_digit (n: nat) :=
  (String (Ascii.ascii_of_nat (n + 48)) EmptyString).

Definition string_of_nat (n: nat) :=
  (fix rec_string_of_nat (i n: nat) (acc: string): string :=
     let d := string_of_digit (n mod 10) in
     let acc' := d ++ acc in
     match i with
     | 0 => acc'
     | S p => match n / 10 with
              | 0 => acc'
              | n' => rec_string_of_nat p n' acc'
              end
     end) n n "".

Fixpoint dlist_of_string (s: string): list (option nat) :=
  match s with
  | EmptyString => nil
  | String a rest =>
    let v := Ascii.nat_of_ascii a in
    (if andb (48 <=? v) (v <=? 57) then (Some (v - 48)) else None)
      :: (dlist_of_string rest)
  end.

Definition nat_of_dlist (dl: list (option nat)): option nat :=
  match dl with
  | nil => None
  | l' => (fix loop (l: list (option nat)) (i acc: nat): option nat :=
             match l with
             | nil => Some acc
             | maybe_digit :: rest =>
               match maybe_digit with
               | None => None
               | Some d => loop rest (i - 1) (acc + d * (10 ^ i))
               end
             end) l' ((List.length l') - 1) 0
  end.

Definition nat_of_string (s: string) := nat_of_dlist (dlist_of_string s).

(* Some micro-SMV types *)

Definition bt_input_type :=
  (TEnum ("Runn"::"Fail"::"Succ"::nil)).

Definition bt_output_type :=
  (TEnum ("none"::"disabled"::"running"::"failed"::"succeeded"::nil)).

Definition bt_action_type :=
  (TEnum ("no"::"enable"::"disable"::nil)).

Definition bt_seq_state :=
  (TEnum ("initial"::"enabling_left"::"enabling_right"::"return_left"::
          "return_right"::"disabling_left"::"disabling_right"::nil)).


(* Boilerplate modules *)

Definition bp_tick_generator :=
  Build_smv_module
    "bt_tick_generator"
    ("top_level_bt"::nil)
    None
    None
    None
    (Some (AddA (init (Mod "top_level_bt" (Id "enable"))
                      (BConst smvT))
                (LastA (next (Mod "top_level_bt" (Id "enable"))
                             (Neg (Equal (Qual (Mod "top_level_bt"
                                                    (Id "output")))
                                         (SConst "none"))))))).

Definition bp_skill_autonomous :=
  (* This module is useful for autonomous generation of an SMV specification.
     When used with OCRA, the following (simpler) module is sufficient: input
     variables and transitions are supplied by the main module. *)
  Build_smv_module
    "bt_skill"
    nil
    (Some (AddV "output" (TSimp bt_output_type)
                (LastV "enable" (TSimp TBool))))
    (Some (LastI "input" bt_input_type))
    None
    (Some (AddA (init (Id "output") (SConst "none"))
                (LastA
                   (next (Id "output")
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
                                                             (SConst "succeeded")))))))))).

Definition bp_skill :=
  Build_smv_module
    "bt_skill"
    nil
    (Some (AddV "output" (TSimp bt_output_type)
                (LastV "enable" (TSimp TBool))))
    None
    None
    None.

Definition bp_TRUE :=
  Build_smv_module
    "bt_TRUE"
    nil
    (Some (LastV "enable" (TSimp TBool)))
    None
    (Some (LastD "output" (SConst "succeeded")))
    None.

Definition bp_not :=
  Build_smv_module
    "bt_not"
    ("child_bt"::nil)
    (Some (LastV "enable" (TSimp TBool)))
    None
    (Some (LastD "output"
                 (Case
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
    (Some (LastA (invar (Mod "child_bt" (Id "enable"))
                        (Qual (Id "enable"))))).
    
Definition bp_isRunning := 
  Build_smv_module
    "bt_isRunning"
    ("child_bt"::nil)
    (Some (LastV "enable" (TSimp TBool)))
    None
    (Some (LastD "output"
                 (Case
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
    (Some (LastA (invar (Mod "child_bt" (Id "enable"))
                        (Qual (Id "enable"))))).

(* Binary-branching implementation *)

Module BT_bin_spec (X: BT_SIG).

  Include BT_binary X.

  (* Possible SMV modules to be generated *)
  Inductive modtype :=
    Skmod | TRUEmod | Seqmod | Fbmod | Par1mod | Par2mod | Notmod | Runmod.
  
  Theorem modtype_dec: forall x y:modtype, {x = y} + {x <> y}.
    decide equality.
  Defined.

  (* Definition of module names *)
  
  Definition rootName (t: btree) :=
    match t with
    | Skill s => X.skillName s
    | TRUE => "BTSucc"
    | Node _ n _ _ => n
    | Dec _ n _ => n
    end.

  Definition nodeName (k: nodeKind) :=
    match k with
    | Sequence => "SEQUENCE_NODE"
    | Fallback => "FALLBACK_NODE"
    | Parallel1 => "PARALLEL1_NODE"
    | Parallel2 => "PARALLEL2_NODE"
    end.

  Definition decName (d: decKind) :=
    match d with
    | Not => "NOT_NODE"
    | IsRunning => "ISRUNNING_NODE"
    end.

  (* Boilerplate modules specific for the binary case *)

  Definition bp_bin_seq :=
    Build_smv_module
      (nodeName Sequence)
      ("visit"::"from_left_bt"::"from_right_bt"::nil)
      (Some (AddV "to_left_bt" (TSimp bt_action_type)
                  (AddV "to_right_bt" (TSimp bt_action_type)
                        (AddV "output" (TSimp bt_output_type)
                              (AddV "cached_left" (TSimp bt_output_type)
                                    (LastV "state" (TSimp bt_seq_state)))))))
      None
      None
      (Some (AddA (init (Id "to_left_bt") (SConst "no"))
                  (AddA (init (Id "to_right_bt") (SConst "no"))
                        (AddA (init (Id "output") (SConst "none"))
                              (AddA (init (Id "cached_left") (SConst "none"))
                                    (AddA (init (Id "state") (SConst "initial"))
            (AddA (next (Id "to_left_bt")
                        (Case
                        (AddCexp (And (Equal (Qual (Id "state"))
                                             (SConst "initial"))
                                      (Equal (Qual (Id "visit"))
                                             (SConst "enable")))
                                 (SConst "enable")
                                 (AddCexp (And (Equal (Qual (Id "state"))
                                                      (SConst "initial"))
                                               (Equal (Qual (Id "visit"))
                                                      (SConst "disable")))
                                          (SConst "disable")
                                          (AddCexp (And (Equal (Qual (Id "state"))
                                                               (SConst "enabling_left"))
                                                        (Equal (Qual (Id "from_left_bt"))
                                                               (SConst "none")))
                                                   (SConst "enable")
                                                   (AddCexp (And (Equal (Qual (Id "state"))
                                                                        (SConst "disabling_left"))
                                                                 (Neg (Equal (Qual (Id "from_left_bt"))
                                                                             (SConst "disabled"))))
                                                            (SConst "disable")
                                                            (Cexp (BConst smvT) (SConst "no"))))))))
            (AddA (next (Id "to_right_bt")
                        (Case
                        (AddCexp (And (Equal (Qual (Id "state"))
                                             (SConst "enabling_left"))
                                      (Equal (Qual (Id "from_left_bt"))
                                             (SConst "succeeded")))
                                 (SConst "enable")
                                 (AddCexp (And (Equal (Qual (Id "state"))
                                                      (SConst "enabling_left"))
                                               (Paren (Or (Equal (Qual (Id "from_left_bt"))
                                                                 (SConst "running"))
                                                          (Equal (Qual (Id "from_left_bt"))
                                                                 (SConst "failed")))))
                                          (SConst "disable")
                                          (AddCexp (And (Equal (Qual (Id "state"))
                                                               (SConst "enabling_right"))
                                                        (Equal (Qual (Id "from_left_bt"))
                                                               (SConst "none")))
                                                   (SConst "enable")
                                                   (AddCexp (And (Equal (Qual (Id "state"))
                                                                        (SConst "disabling_right"))
                                                                 (Neg (Equal (Qual (Id "from_right_bt"))
                                                                             (SConst "disabled"))))
                                                            (SConst "disable")
                                                            (Cexp (BConst smvT) (SConst "no"))))))))
            (AddA (next (Id "output")
                        (Case
                        (AddCexp (And (Equal (Qual (Id "state"))
                                             (SConst "enabling_right"))
                                      (Neg (Equal (Qual (Id "from_right_bt"))
                                                  (SConst "none"))))
                                 (SConst "from_right_bt")
                                 (AddCexp (And (Equal (Qual (Id "state"))
                                                      (SConst "disabling_right"))
                                               (Equal (Qual (Id "from_right_bt"))
                                                      (SConst "disabled")))
                                          (SConst "cached_left")
                                          (Cexp (BConst smvT) (SConst "none"))))))
            (AddA (next (Id "cached_left")
                        (Case
                        (AddCexp (And (Equal (Qual (Id "state"))
                                             (SConst "enabling_left"))
                                      (Paren (Or (Equal (Qual (Id "from_left_bt"))
                                                        (SConst "running"))
                                                 (Equal (Qual (Id "from_left_bt"))
                                                        (SConst "failed")))))
                                 (SConst "from_left_bt")
                                 (AddCexp (And (Equal (Qual (Id "state"))
                                                      (SConst "disabling_left"))
                                               (Equal (Qual (Id "from_left_bt"))
                                                      (SConst "disabled")))
                                          (SConst "from_left_bt")
                                          (AddCexp (And (Equal (Qual (Id "state"))
                                                               (SConst "disabling_right"))
                                                        (Neg (Equal (Qual (Id "from_right_bt"))
                                                                    (SConst "disabled"))))
                                                   (SConst "cached_left")
                                                   (Cexp (BConst smvT) (SConst "none")))))))
                  (LastA (next (Id "state")
                         (Case
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "initial"))
                                       (Equal (Qual (Id "visit"))
                                              (SConst "enable")))
                                  (SConst "enabling_left")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "initial"))
                                       (Equal (Qual (Id "visit"))
                                              (SConst "disable")))
                                  (SConst "disabling_left")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "enabling_left"))
                                       (Equal (Qual (Id "from_left_bt"))
                                              (SConst "succeeded")))
                                  (SConst "enabling_right")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "enabling_left"))
                                       (Equal (Qual (Id "from_left_bt"))
                                              (SConst "none")))
                                  (SConst "enabling_left")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "enabling_left"))
                                       (Paren (Or (Equal (Qual (Id "from_left_bt"))
                                                         (SConst "running"))
                                                  (Equal (Qual (Id "from_left_bt"))
                                                         (SConst "failed")))))
                                  (SConst "disabling_right")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "enabling_right"))
                                       (Equal (Qual (Id "from_right_bt"))
                                              (SConst "none")))
                                  (SConst "enabling_right")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "enabling_right"))
                                       (Neg (Equal (Qual (Id "from_right_bt"))
                                                   (SConst "none"))))
                                  (SConst "return_right")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "disabling_right"))
                                       (Neg (Equal (Qual (Id "from_right_bt"))
                                                   (SConst "disabled"))))
                                  (SConst "disabling_right")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "disabling_right"))
                                       (Equal (Qual (Id "from_right_bt"))
                                              (SConst "disabled")))
                                  (SConst "return_left")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "disabling_left"))
                                       (Neg (Equal (Qual (Id "from_left_bt"))
                                                   (SConst "disabled"))))
                                  (SConst "disabling_left")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "disabling_left"))
                                       (Equal (Qual (Id "from_left_bt"))
                                              (SConst "disabled")))
                                  (SConst "disabling_right")
                         (Cexp (BConst smvT) (SConst "initial")))))))))))))))))))))))))).

  Definition bp_bin_fb :=
    Build_smv_module
      (nodeName Fallback)
      ("visit"::"from_left_bt"::"from_right_bt"::nil)
      (Some (AddV "to_left_bt" (TSimp bt_action_type)
                  (AddV "to_right_bt" (TSimp bt_action_type)
                        (AddV "output" (TSimp bt_output_type)
                              (AddV "cached_left" (TSimp bt_output_type)
                                    (LastV "state" (TSimp bt_seq_state)))))))
      None
      None
      (Some (AddA (init (Id "to_left_bt") (SConst "no"))
                  (AddA (init (Id "to_right_bt") (SConst "no"))
                        (AddA (init (Id "output") (SConst "none"))
                              (AddA (init (Id "cached_left") (SConst "none"))
                                    (AddA (init (Id "state") (SConst "initial"))
            (AddA (next (Id "to_left_bt")
                        (Case
                        (AddCexp (And (Equal (Qual (Id "state"))
                                             (SConst "initial"))
                                      (Equal (Qual (Id "visit"))
                                             (SConst "enable")))
                                 (SConst "enable")
                                 (AddCexp (And (Equal (Qual (Id "state"))
                                                      (SConst "initial"))
                                               (Equal (Qual (Id "visit"))
                                                      (SConst "disable")))
                                          (SConst "disable")
                                          (AddCexp (And (Equal (Qual (Id "state"))
                                                               (SConst "enabling_left"))
                                                        (Equal (Qual (Id "from_left_bt"))
                                                               (SConst "none")))
                                                   (SConst "enable")
                                                   (AddCexp (And (Equal (Qual (Id "state"))
                                                                        (SConst "disabling_left"))
                                                                 (Neg (Equal (Qual (Id "from_left_bt"))
                                                                             (SConst "disabled"))))
                                                            (SConst "disable")
                                                            (Cexp (BConst smvT) (SConst "no"))))))))
            (AddA (next (Id "to_right_bt")
                        (Case
                        (AddCexp (And (Equal (Qual (Id "state"))
                                             (SConst "enabling_left"))
                                      (Equal (Qual (Id "from_left_bt"))
                                             (SConst "failed")))
                                 (SConst "enable")
                                 (AddCexp (And (Equal (Qual (Id "state"))
                                                      (SConst "enabling_left"))
                                               (Paren (Or (Equal (Qual (Id "from_left_bt"))
                                                                 (SConst "running"))
                                                          (Equal (Qual (Id "from_left_bt"))
                                                                 (SConst "succeeded")))))
                                          (SConst "disable")
                                          (AddCexp (And (Equal (Qual (Id "state"))
                                                               (SConst "enabling_right"))
                                                        (Equal (Qual (Id "from_right_bt"))
                                                               (SConst "none")))
                                                   (SConst "enable")
                                                   (AddCexp (And (Equal (Qual (Id "state"))
                                                                        (SConst "disabling_right"))
                                                                 (Neg (Equal (Qual (Id "from_right_bt"))
                                                                             (SConst "disabled"))))
                                                            (SConst "disable")
                                                            (Cexp (BConst smvT) (SConst "no"))))))))
            (AddA (next (Id "output")
                        (Case
                        (AddCexp (And (Equal (Qual (Id "state"))
                                             (SConst "enabling_right"))
                                      (Neg (Equal (Qual (Id "from_right_bt"))
                                                  (SConst "none"))))
                                 (SConst "from_right_bt")
                                 (AddCexp (And (Equal (Qual (Id "state"))
                                                      (SConst "disabling_right"))
                                               (Equal (Qual (Id "from_right_bt"))
                                                      (SConst "disabled")))
                                          (SConst "cached_left")
                                          (Cexp (BConst smvT) (SConst "none"))))))
            (AddA (next (Id "cached_left")
                        (Case
                        (AddCexp (And (Equal (Qual (Id "state"))
                                             (SConst "enabling_left"))
                                      (Paren (Or (Equal (Qual (Id "from_left_bt"))
                                                        (SConst "running"))
                                                 (Equal (Qual (Id "from_left_bt"))
                                                        (SConst "succeeded")))))
                                 (SConst "from_left_bt")
                                 (AddCexp (And (Equal (Qual (Id "state"))
                                                      (SConst "disabling_left"))
                                               (Equal (Qual (Id "from_left_bt"))
                                                      (SConst "disabled")))
                                          (SConst "from_left_bt")
                                          (AddCexp (And (Equal (Qual (Id "state"))
                                                               (SConst "disabling_right"))
                                                        (Neg (Equal (Qual (Id "from_right_bt"))
                                                                    (SConst "disabled"))))
                                                   (SConst "cached_left")
                                                   (Cexp (BConst smvT) (SConst "none")))))))
                  (LastA (next (Id "state")
                         (Case
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "initial"))
                                       (Equal (Qual (Id "visit"))
                                              (SConst "enable")))
                                  (SConst "enabling_left")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "initial"))
                                       (Equal (Qual (Id "visit"))
                                              (SConst "disable")))
                                  (SConst "disabling_left")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "enabling_left"))
                                       (Equal (Qual (Id "from_left_bt"))
                                              (SConst "failed")))
                                  (SConst "enabling_right")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "enabling_left"))
                                       (Equal (Qual (Id "from_left_bt"))
                                              (SConst "none")))
                                  (SConst "enabling_left")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "enabling_left"))
                                       (Paren (Or (Equal (Qual (Id "from_left_bt"))
                                                         (SConst "running"))
                                                  (Equal (Qual (Id "from_left_bt"))
                                                         (SConst "succeeded")))))
                                  (SConst "disabling_right")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "enabling_right"))
                                       (Equal (Qual (Id "from_right_bt"))
                                              (SConst "none")))
                                  (SConst "enabling_right")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "enabling_right"))
                                       (Neg (Equal (Qual (Id "from_right_bt"))
                                                   (SConst "none"))))
                                  (SConst "return_right")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "disabling_right"))
                                       (Neg (Equal (Qual (Id "from_right_bt"))
                                                   (SConst "disabled"))))
                                  (SConst "disabling_right")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "disabling_right"))
                                       (Equal (Qual (Id "from_right_bt"))
                                              (SConst "disabled")))
                                  (SConst "return_left")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "disabling_left"))
                                       (Neg (Equal (Qual (Id "from_left_bt"))
                                                   (SConst "disabled"))))
                                  (SConst "disabling_left")
                         (AddCexp (And (Equal (Qual (Id "state"))
                                              (SConst "disabling_left"))
                                       (Equal (Qual (Id "from_left_bt"))
                                              (SConst "disabled")))
                                  (SConst "disabling_right")
                         (Cexp (BConst smvT) (SConst "initial")))))))))))))))))))))))))).
  
  Definition bp_par1 :=
    Build_smv_module
      (nodeName Parallel1)
      ("left_bt"::"right_bt"::nil)
      (Some (LastV "enable" (TSimp TBool)))
      None
      (Some (AddD "true_output_count"
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
      (Some (AddA (invar (Mod "left_bt" (Id "enable"))
                         (Qual (Id "enable")))
                  (LastA (invar (Mod "right_bt" (Id "enable"))
                                (Qual (Id "enable")))))).

  Definition bp_par2 :=
    Build_smv_module
      (nodeName Parallel2)
      ("left_bt"::"right_bt"::nil)
      (Some (LastV "enable" (TSimp TBool)))
      None
      (Some (AddD "true_output_count"
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
      (Some (AddA (invar (Mod "left_bt" (Id "enable"))
                         (Qual (Id "enable")))
                  (LastA (invar (Mod "right_bt" (Id "enable"))
                                (Qual (Id "enable")))))).

  (* This function scans a BT compiling a list of the needed modules *)
  Fixpoint addmod (t: btree) (s: ListSet.set modtype) :=
    match t with
    | Skill _ => set_add modtype_dec Skmod s
    | TRUE => set_add modtype_dec TRUEmod s
    | Node k _ t1 t2 =>
      let nodemod := match k with
                     | Sequence => Seqmod
                     | Fallback => Fbmod
                     | Parallel1 => Par1mod
                     | Parallel2 => Par2mod
                     end in
      let left_modules := addmod t1 s in
      let right_modules := addmod t2 s in
      set_add modtype_dec nodemod
              (set_union modtype_dec left_modules right_modules)
    | Dec k _ t' =>
      let decmod := match k with
                    | Not => Notmod
                    | IsRunning => Runmod
                    end in
      set_add modtype_dec decmod (addmod t' s)
    end.

  (* This function returns a list of the names of all the inner nodes of a BT,
     together with its kind. It is needed for the OSS file generation. *)
  Fixpoint inlist (t: btree) (s: list (identifier * string)) :=
    match t with
    | Skill _ => s
    | TRUE => s
    | Node k n t1 t2 =>
      let s' := inlist t1 s in
      let s'' := inlist t2 s' in
      (pair n (nodeName k)) :: s''
    | Dec k n t' =>
      let decmod := match k with
                    | Not => Notmod
                    | IsRunning => Runmod
                    end in
      (pair n (decName k)) :: (inlist t' s)
    end.
  
  (* Functions to generate the SMV specification *)

  Definition make_mod (t: modtype) (aut:bool): smv_module :=
    match t with
    | Skmod => if aut then bp_skill_autonomous else bp_skill
    | TRUEmod => bp_TRUE
    | Seqmod => bp_bin_seq
    | Fbmod => bp_bin_fb
    | Par1mod => bp_par1
    | Par2mod => bp_par2
    | Notmod => bp_not
    | Runmod => bp_isRunning
    end.
  
  Fixpoint make_mod_list (l: list modtype) (aut: bool): list smv_module :=
    match l with
    | nil => nil
    | m :: rest =>
      (* D5.3 workflow: skills are implemented independently *)
      match m with
      | Skmod => (make_mod_list rest aut)
      | _ => cons (make_mod m aut) (make_mod_list rest aut)
      end
    end.

  Fixpoint make_vars (t: btree): varlist :=
    match t with
    | Skill s => LastV (X.skillName s) (TComp (TMod "bt_skill"))
    | TRUE => LastV "t" (TComp (TMod "bt_TRUE"))
    | Node k name t1 t2 =>
      let x := varlist_app (make_vars t1) (make_vars t2) in
      AddV name
           (TComp (TModPar (nodeName k)
                           (AddP (Qual (Id (rootName t1)))
                                 (LastP (Qual (Id (rootName t2)))))))
           x
    | Dec d name t =>
      let x := make_vars t in
      AddV name
           (TComp (TModPar (decName d)
                           (LastP (Qual (Id (rootName t))))))
           x
    end.

  Definition make_main (t: btree) (modname: string) :=
    Build_smv_module
      modname
      nil
      (Some (varlist_rev
               (AddV "tick_generator"
                     (TComp (TModPar "bt_tick_generator"
                                     (LastP (Qual (Id (rootName t))))))
                     (make_vars t))))
      None
      None
      None.

  Definition make_spec (t: btree): list smv_module :=
    let needed := addmod t (empty_set modtype) in
    let modlist := make_mod_list needed true in
    app modlist (bp_tick_generator :: (make_main t "main") :: nil).

  (* Modules for OCRA inteface *)

  Fixpoint mkop (lst: list X.skillSet) :=
    match lst with
    | nil => nil
    | s :: rest => cons ("from_" ++ (X.skillName s)) (mkop rest)
    end.

  Definition build_parameters (p: identifier) (t1 t2: btree) :=
    match t1 with
    | Skill s1 =>
      match t2 with
      | Skill s2 =>           (* skill, skill *)
        (AddP (Qual (Id p))
              (AddP (Qual (Id ("from_" ++ X.skillName s1)))
                    (LastP (Qual (Id ("from_" ++ X.skillName s2))))))
      | TRUE => LastP (Qual (Id "dummy"))         (* TBD *)
      | Node k2 n2 _ _ =>     (* skill, node *)
        (AddP (Qual (Id p))
              (AddP (Qual (Id ("from_" ++ X.skillName s1)))
                    (LastP (Qual (Mod n2 (Id "output"))))))
      | Dec k2 _ _ => LastP (Qual (Id "dummy"))   (* TBD *)
      end
    | TRUE => LastP (Qual (Id "dummy"))           (* TBD *)
    | Node k1 n1 _ _ =>
      match t2 with
      | Skill s2 =>           (* node, skill *)
        (AddP (Qual (Id p))
              (AddP (Qual (Mod n1 (Id "output")))
                    (LastP (Qual (Id ("from_" ++ X.skillName s2))))))
      | TRUE => LastP (Qual (Id "dummy"))         (* TBD *)
      | Node k2 n2 _ _ =>     (* node, node *)
        (AddP (Qual (Id p))
              (AddP (Qual (Mod n1 (Id "output")))
                    (LastP (Qual (Mod n2 (Id "output"))))))
      | Dec k2 _ _ => LastP (Qual (Id "dummy"))   (* TBD *)
      end
    | Dec k1 _ _ => LastP (Qual (Id "dummy"))     (* TBD *)
    end.
    
  Fixpoint mkov (t: btree) (l: option varlist) (parent: identifier) :=
    match t with
    | Skill s => l
    | TRUE => l
    | Node k name t1 t2 =>
      match k with
      | Sequence =>
        let parameters := build_parameters parent t1 t2 in
        let newlist :=
            let vl_left := mkov t1 l (name ++ ".to_left_bt") in
            let vl_right := mkov t2 l (name ++ ".to_right_bt") in
            match vl_left, vl_right with
            | Some vl, Some vl' => Some (varlist_app vl vl')
            | Some _, None => vl_left
            | None, _ => vl_right
            end in
        match newlist with
        | Some vl =>
          (Some (AddV name
                      (TComp (TModPar (nodeName Sequence) parameters))
                      vl))
        | None =>
          (Some (LastV name
                       (TComp (TModPar (nodeName Sequence) parameters))))
        end
      | Fallback =>
        let parameters := build_parameters parent t1 t2 in
        let newlist :=
            let vl_left := mkov t1 l (name ++ ".to_left_bt") in
            let vl_right := mkov t2 l (name ++ ".to_right_bt") in
            match vl_left, vl_right with
            | Some vl, Some vl' => Some (varlist_app vl vl')
            | Some _, None => vl_left
            | None, _ => vl_right
            end in
        match newlist with
        | Some vl =>
          (Some (AddV name
                      (TComp (TModPar (nodeName Fallback) parameters))
                      vl))
        | None =>
          (Some (LastV name
                       (TComp (TModPar (nodeName Fallback) parameters))))
        end
      | Parallel1 => None  (* TBD *)
      | Parallel2 => None  (* TBD *)
      end
    | Dec k _ t' => None  (* TBD *)
    end.

  Inductive direction := From_left | From_right.

  Fixpoint mkod (t: btree) (d: deflist) (parent: identifier) (dir: direction) :=
    match t with
    | Skill s =>
      (AddD ("to_" ++ X.skillName s)
            (Qual (Mod parent
                       (Id (match dir with
                            | From_left => "to_left_bt"
                            | From_right => "to_right_bt"
                            end))))
            d)
    | TRUE => d
    | Node _ n t1 t2 =>
      let dl_left := mkod t1 d n From_left in
      mkod t2 dl_left n From_right
    | Dec k _ t' => d
    end.

(*    (LastD "pippo" (Qual (Id "pluto"))).*)

  Definition ocra_bt_fsm (t: btree) :=
    Build_smv_module
      "BT_FSM"
      ("visit" :: (mkop (sklist t)))
      (mkov t None "visit")
      None
      (match t with
       | Skill s => None        (* TBD *)
       | TRUE => None           (* TBD *)
       | Node _ n t1 t2 =>
         let dl_left := mkod t1
                             (LastD "output" (Qual (Mod n (Id "output"))))
                             n
                             From_left in
         let dl_tot := mkod t2
                            dl_left
                            n
                            From_right in
         Some dl_tot
       | Dec _ n t' => None     (* TBD *)
       end)
      None.

  Fixpoint mkparomain (l: list X.skillSet) :=
    match l with
    | nil => (* will never happen *)
      LastP (Qual (Id ""))
    | s :: nil =>
      LastP (Qual (Id ("from_" ++ (X.skillName s))))
    | s :: rest =>
      AddP (Qual (Id ("from_" ++ (X.skillName s))))
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
      (Some (AddV "BT_FSM_inst" (TComp (TModPar "BT_FSM"
                                                (AddP (Qual (Id "visit"))
                                                      (mkparomain (sklist t)))))
                  (AddV "visit" (TSimp bt_action_type)
                        (mkvaromain (sklist t)))))
      None
      (Some (AddD "output" (Qual (Mod "BT_FSM_inst" (Id "output")))
                  (mkdefomain (sklist t))))
      None.

  Definition make_spec_ocra (t: btree): list smv_module :=
    let needed := addmod t (empty_set modtype) in
    let modlist := make_mod_list needed false in
    app modlist ((ocra_bt_fsm t) :: (ocra_main t) :: nil).

End BT_bin_spec.

(* Arbitrary-branching implementation *)

Module BT_gen_spec (X: BT_SIG).

  Include BT_general X.

  (* Possible SMV modules to be generated *)
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
      (Some (LastV "enable" (TSimp TBool)))
      None
      (Some (LastD "output" (Qual (Mod "bt" (Id "output")))))
      (Some (LastA (invar (Mod "bt" (Id "enable"))
                          (Qual (Id "enable"))))).
  
  Definition rootName (t: btree) :=
    match t with
    | Skill s => X.skillName s
    | TRUE => "BTSucc"
    | Node _ n _ => n
    | Dec _ n _ => n
    end.

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
        (Some (LastV "enable" (TSimp TBool)))
        None
        (Some (LastD "output" (Case (mk_seq_trans l))))
        (Some (AddA (invar (Mod ("bt" ++ string_of_nat l) (Id "enable"))
                           (Qual (Id "enable")))
                    (mk_seq_invar p)))
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
        (Some (LastV "enable" (TSimp TBool)))
        None
        (Some (LastD "output" (Case (mk_fb_trans l))))
        (Some (AddA (invar (Mod ("bt" ++ string_of_nat l) (Id "enable"))
                           (Qual (Id "enable")))
                    (mk_fb_invar p)))
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
               (Some (LastV "enable" (TSimp TBool)))
               None
               (Some (LastD "output" (SConst "succeeded")))
               (Some (LastA (invar (Mod "bt" (Id "enable"))
                                   (Qual (Id "enable")))))
           else bp_identity (nodeName (Parallel 1) 1)
    | S p =>
      Build_smv_module
        (nodeName (Parallel n) l)
        (mk_param_list l)
        (Some (LastV "enable" (TSimp TBool)))
        None
        (Some (AddD "true_output_count"
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
        (Some (mk_par_invar (S p)))
    end.

  Definition make_mod (t: modtype) (aut: bool): smv_module :=
    match t with
    | Skmod => if aut then bp_skill_autonomous else bp_skill
    | TRUEmod => bp_TRUE
    | Seqmod l => make_sequence l
    | Fbmod l => make_fallback l
    | Parmod n l => make_parallel n l
    | Notmod => bp_not
    | Runmod => bp_isRunning
    end.

  Fixpoint make_mod_list (l: list modtype) (aut: bool): list smv_module :=
    match l with
    | nil => nil
    | m :: rest => cons (make_mod m aut) (make_mod_list rest aut)
    end.

  (* Functions to generate the main module *)

  Fixpoint make_paramlist (f: btforest) :=
    match f with
    | Child t => (LastP (Qual (Id (rootName t))))
    | Add t1 rest => (AddP (Qual (Id (rootName t1)))
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
                           (LastP (Qual (Id (rootName t))))))
           vars
    end
  with make_vars_f (f: btforest) :=
         match f with
         | Child t => (make_vars t)
         | Add t1 rest => varlist_app (make_vars t1) (make_vars_f rest)
         end.

  Definition make_main (t: btree) (modname: string) :=
    Build_smv_module
      modname
      nil
      (Some (varlist_rev
               (AddV "tick_generator"
                     (TComp (TModPar "bt_tick_generator"
                                     (LastP (Qual (Id (rootName t))))))
                     (make_vars t))))
      None
      None
      None.

  Definition make_spec (t: btree): list smv_module :=
    let needed := addmod t (empty_set modtype) in
    let modlist := make_mod_list needed true in
    app modlist (bp_tick_generator :: (make_main t "main") :: nil).


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
      (Some (mkov (sklist t)))
      None
      None
      (Some (mkot (sklist t))).

  Fixpoint mkparomain (l: list X.skillSet) :=
    match l with
    | nil => (* will never happen *)
      LastP (Qual (Id ""))
    | s :: nil =>
      LastP (Qual (Id ("from_" ++ (X.skillName s))))
    | s :: rest =>
      AddP (Qual (Id ("from_" ++ (X.skillName s))))
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
      (Some (AddV "BT_FSM_inst" (TComp (TModPar "BT_FSM"
                                                (mkparomain (sklist t))))
                  (mkvaromain (sklist t))))
      None
      (Some (mkdefomain (sklist t)))
      None.
  
  Definition make_spec_ocra (t: btree): list smv_module :=
    let needed := addmod t (empty_set modtype) in
    let modlist := make_mod_list needed false in
    app modlist (bp_tick_generator :: (make_main t "bt_main")
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
