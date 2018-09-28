(* Definition of the FSM data type *)

Require Import String ListSet List Arith Bool.
Require Import bt micro_smv spec_extr bt2spec.
Open Scope string_scope.

(* These functions are (inexplicably) missing from Coq's standard libraries, so
   we define them here. *)

Set Implicit Arguments.
Definition list_index (A: Type) (Aeq_dec: forall (x y : A), {x = y} + {x <> y})
           (l: list A) (a: A): option nat :=
  (fix scan_list (l': list A) (i: nat): option nat :=
     match l' with
     | nil => None
     | x :: rest =>
        match Aeq_dec x a with
        | left _ => Some i
        | right _ => scan_list rest (S i)
        end
    end) l 0.
Definition string_equal (s1 s2: string) :=
  match string_dec s1 s2 with
  | left _ => true
  | right _ => false
  end.
Unset Implicit Arguments.

(* This function produces a list of all the possible values for a variable
   of the given (simple) type. *)
Definition poss_val (ty: simp_type_spec): list symbolic_constant :=
  match ty with
  | TBool => "TRUE"::"FALSE"::nil
  | TEnum scl => scl
  end.

(* This function produces a list containing all the variable identifiers
   used in a smv_module *)
Definition idlist (m: smv_module): list identifier :=
  match vars m with
  | None => nil
  | Some vl =>
    (fix scan (v: varlist) :=
       match v with
       | LastV id ty => cons id nil
       | AddV id ty rest => cons id (scan rest)
       end) vl
  end.

Section Microsmv_execution.

  Variable m: smv_module.
  
  (* A state is an assignment of a value to each variable. Rather than using
     a function type, it seems more convenient to define a state directly as
     a list of symbolic constants, representing the value of each variable
     defined in a module. *)

  Definition state := list symbolic_constant.  (* of length = #vars *)

  (* Functions for generating the state space of a module *)
  Definition ss_single_var (ty: type_spec): set state :=
    match ty with
    | TSimp s => map (fun x => cons x nil)
                     (poss_val s)
    | TComp _ => nil (* to be handled later... *)
    end.

  Fixpoint make_ss (vl: varlist): set state :=
    match vl with
    | LastV _ ty => ss_single_var ty
    | AddV _ ty rest =>
      match ty with
      | TSimp s => flat_map (fun st => map (fun z => (cons z st))
                                           (poss_val s))
                            (make_ss rest)
      | TComp _ => nil (* to be handled later... *)
      end
    end.

  (*Compute make_ss (AddV "v1" (TSimp TBool)
    (AddV "v2" (TSimp (TEnum ("a"::"b"::nil)))
    (LastV "v3" (TSimp (TEnum ("1"::"2"::"3"::nil)))))).*)

  Definition make_state_space: set state :=
    match vars m with
    | None => nil
    | Some vl => make_ss vl
    end.

  (* The input alphabet of the FSM is derived from the possible values of
     input variables, plus the special string "epsilon" (we assume that
     this particular string does not appear as a symbolic constant). *)

  Definition inputs := list symbolic_constant.  (* of length = #ivars *)

  Fixpoint make_ss_ivar (il: ivarlist): list symbolic_constant :=
    match il with
    | LastI _ t => cons "epsilon" (poss_val t)
    | AddI _ t rest => app (poss_val t) (make_ss_ivar rest)
    end.
  (* NOTE: this may be incorrect; we probably need a tuple of values, one for each input variable in the module *)

  Definition make_isym: list symbolic_constant :=
    match ivars m with
    | None => nil
    | Some il => make_ss_ivar il
    end.

  (*Compute make_ss_ivar (LastI "input" bt_input_type).*)

  (* Definition of initial states *)

  Definition add_init_cons (c: assign_cons) (res: list (identifier * sexp)) :=
    match c with
    | init qid exp =>
      match qid with
      | Id id => cons (pair id exp) res
      | Mod id1 id2 => cons (pair id1 exp) res (* to be fixed later... *)
      end
    | _ => res
    end.

  Definition extract_init: list (identifier * sexp)%type :=
    match assigns m with
    | None => nil
    | Some acl =>
      (fix scan_for_init (al: asslist) :=
         match al with
         | LastA x => add_init_cons x nil
         | AddA x rest => add_init_cons x (scan_for_init rest)
         end) acl
    end.

  (* The next function evaluates a simple expression on a state.
     Returns None in case of an error (e.g. the given state is ill-formed,
     type mismatch, etc) *)

  Definition sc_neg (a: symbolic_constant) :=
    match a with
    | "TRUE" => (Some "FALSE")
    | "FALSE" => (Some "TRUE")
    | _ => None
    end.

  Definition sc_and (a b: symbolic_constant) :=
    match a,b with
    | "TRUE", "TRUE" => (Some "TRUE")
    | "FALSE", "TRUE" => (Some "FALSE")
    | "TRUE", "FALSE" => (Some "FALSE")
    | "FALSE", "FALSE" => (Some "FALSE")
    | _,_ => None
    end.

  Definition sc_or (a b: symbolic_constant) :=
    match a,b with
    | "TRUE", "TRUE" => (Some "TRUE")
    | "FALSE", "TRUE" => (Some "TRUE")
    | "TRUE", "FALSE" => (Some "TRUE")
    | "FALSE", "FALSE" => (Some "FALSE")
    | _,_ => None
    end.

  Fixpoint eval (s: sexp) (x: state): option symbolic_constant :=
    let vars := idlist m in
    match s with
    (* base cases *)
    | BConst bc => match bc with
                   | smvT => Some "TRUE"
                   | smvF => Some "FALSE"
                   end
    | SConst sc => Some sc
    | Qual qid => match qid with
                  | Id id => match list_index string_dec vars id with
                             | None => None
                             | Some i => nth_error x i
                             end
                  | Mod modname id => None (* to be implemented *)
                  end
    (* recursive cases *)
    | Paren s' => eval s' x
    (* for Neg, And, Or we assume that the results are boolean values *)
    | Neg s' => match eval s' x with
                | Some sc => sc_neg sc
                | None => None
                end
    | And s1 s2 => match eval s1 x, eval s2 x with
                   | Some a, Some b => sc_and a b
                   | _, _ => None
                   end
    | Or s1 s2 => match eval s1 x, eval s2 x with
                  | Some a, Some b => sc_or a b
                  | _, _ => None
                  end
    | Equal s1 s2 => match eval s1 x, eval s2 x with
                     | Some a, Some b =>
                       if string_equal a b then Some "TRUE" else Some "FALSE"
                     | _, _ => None
                     end
    (* for Less, Sum we assume that the results are strings representing
       positive integer values *)
    | Less s1 s2 =>
      match eval s1 x, eval s2 x with
      | Some a, Some b =>
        let val_a := nat_of_string a in
        let val_b := nat_of_string b in
        match val_a, val_b with
        | Some v1, Some v2 => if v1 <? v2 then Some "TRUE" else Some "FALSE"
        | _, _ => None
        end
      | _, _ => None
      end
    | Sum s1 s2 =>
      match eval s1 x, eval s2 x with
      | Some a, Some b =>
        let val_a := nat_of_string a in
        let val_b := nat_of_string b in
        match val_a, val_b with
        | Some v1, Some v2 => Some (string_of_nat (v1 + v2))
        | _, _ => None
        end
      | _, _ => None
      end
    | Count slist =>
      let reslist := eval_all slist x in
      (fix rec_count (l: list (option symbolic_constant)) (acc: nat) :=
         match l with
         | nil => Some (string_of_nat acc)
         | maybe_sc :: rest =>
           match maybe_sc with
           | None => None
           | Some sc => match sc with
                        | "TRUE" => rec_count rest (acc + 1)
                        | "FALSE" => rec_count rest acc
                        | _ => None
                        end
           end
         end) reslist 0
    | Case scp => None     (* TBI *)
    end
  with
  eval_all (sl: sexplist) (x: state): list (option symbolic_constant) :=
    match sl with
    | Sexp s => (eval s x) :: nil
    | AddSexp s rest => (eval s x) :: eval_all rest x
    end.

(* some tests:
  Compute eval (Neg (BConst smvF)) nil.
  Compute eval (And (BConst smvT) (BConst smvT)) nil.
  Compute eval (And (BConst smvT) (BConst smvF)) nil.
  Compute eval (Or (BConst smvT) (BConst smvT)) nil.
  Compute eval (Or (BConst smvT) (BConst smvF)) nil.
  Compute eval (Equal (SConst "ready") (SConst "ready")) nil.
  Compute eval (Equal (SConst "ready") (BConst smvT)) nil.
  Compute eval (Less (SConst "ready") (SConst "0")) nil.
  Compute eval (Less (SConst "10") (SConst "7")) nil.
  Compute eval (Less (SConst "0") (SConst "1")) nil.
  Compute eval (Sum (SConst "2") (SConst "2")) nil.
  Compute eval (Sum (BConst smvT) (SConst "1")) nil.
  Compute eval (Count (AddSexp (BConst smvF) (Sexp (BConst smvT)))) nil.
  Compute eval (Count (AddSexp (BConst smvT) (AddSexp (SConst "a") (Sexp (BConst smvT))))) nil.
*)

  Definition is_initial (x: state): bool :=
    let init_cons := extract_init in   (* list (identifier * sexp) *)
    let exps :=
        (fix iter (idl: list identifier) (acc: list (option sexp)): list (option sexp) :=
           match idl with
           | nil => rev acc
           | id :: rest => match find (fun z => string_equal (fst z) id)
                                      init_cons with
                           | None => iter rest (None :: acc)
                           | Some a => iter rest (Some (snd a) :: acc)
                           end
           end) (idlist m) nil in
    (fix iter2 (conditions: list (option sexp)) (values: state): bool :=
       match conditions, values with
       | nil, nil => true
       | maybe_cond :: rest_of_conds, value :: rest_of_values =>
         match maybe_cond with
         | None => iter2 rest_of_conds rest_of_values
         | Some cond => match eval cond x with
                        | None => false   (* not clear what to do here... *)
                        | Some v => if string_equal v value then
                                      iter2 rest_of_conds rest_of_values
                                    else
                                      false
                        end
         end
       | _ , _ => false   (* will never happen *)
       end) exps x.

(*  Definition there_is_transition (x1: state) (i: inputs) (x2: state): bool :=
    true.
*)


  (* The FSM corresponding to the module m is ... *)





  (* An execution of the fsm z is ... *)


End Microsmv_execution.

(*** Examples ***)

(* The easiest possible FSM: one bit state, single transition *)
Definition inverter :=
  Build_smv_module
    "main"
    nil
    (Some (LastV "b0" (TSimp TBool)))
    None
    None
    (Some (AddA (init (Id "b0")
                      (BConst smvF))
                (LastA (next (Id "b0")
                             (Simple (Neg (Qual (Id "b0")))))))).

Compute translate inverter.
Compute make_state_space inverter.


(* Example of non-deterministic dynamics, from the NuSMV manual *)
Definition ex1 :=
  Build_smv_module
    "main"
    nil
    (Some (AddV "state" (TSimp (TEnum ("ready"::"busy"::nil)))
                (LastV "request" (TSimp TBool))))
    None
    None
    (Some (AddA (init (Id "state") (SConst "ready"))
                (LastA (next (Id "state")
                             (Simple (Case
                                        (AddCexp (And (Equal (Qual (Id "state")) (SConst "ready"))
                                                      (Equal (Qual (Id "request")) (BConst smvT)))
                                                 (SConst "busy")
                                                 (Cexp (BConst smvT)
                                                       (SConst "ready"))))))))).

Compute make_state_space ex1.
Compute translate ex1.

(* A 6-hour clock *)
Definition clock :=
  Build_smv_module
    "main"
    nil
    (Some
       (LastV "hour"
              (TSimp (TEnum ("1"::"2"::"3"::"4"::"5"::"6"::nil)))))
    (Some (LastI "enable" TBool))
    None
    (Some
       (AddA (init (Id "enable")
                   (BConst smvT))
             (AddA (init (Id "hour")
                         (SConst "6"))
                   (LastA (next (Id "hour")
                                (Simple
                                   (Case
                                      (AddCexp
                                         (And (Qual (Id "enable"))
                                              (Equal (Qual (Id "hour"))
                                                     (SConst "6")))
                                         (SConst "1")
                                         (AddCexp
                                            (Qual (Id "enable"))
                                            (Sum (Qual (Id "hour"))
                                                 (SConst "1"))
                                            (Cexp
                                               (BConst smvT)
                                               (Qual (Id "hour")))))))))))).

Compute make_state_space clock.






(* dead code

(* adds every element of l to the set s *)
Fixpoint add_all (l: list string) (s: set string): set string :=
  match l with
  | nil => s
  | cons x l' => set_add string_dec x (add_all l' s)
  end.

(* produces the set of all possible values of a variable of type ty *)
Fixpoint pv (ty: simp_type_spec): set string :=
  match ty with
  | TBool => set_add string_dec "TRUE"
                     (set_add string_dec "FALSE"
                              (empty_set string))
  | TEnum scl => add_all scl (empty_set string)
  end.


Definition zex := list string.
Definition zex_dec : forall (a b: zex), {a = b} + {a <> b}.
  repeat decide equality. 
Defined.

Definition sspace_of_single_var (id: identifier) (ty: type_spec): set zex :=
  match ty with
  | TSimp s => set_map zex_dec
                       (fun st => cons st nil)
                       (pv s)
  | TComp _ => empty_set zex (* to be handled later... *)
  end.

Compute sspace_of_single_var "b0" (TSimp TBool).
(* ("TRUE" :: nil) :: ("FALSE" :: nil) :: nil *)

Fixpoint make_ss (vl: varlist): set zex :=
  match vl with
  | LastV id ty => (sspace_of_single_var id ty)
  | AddV id ty rest =>
    match ty with
    | TSimp s => set_map

      (pv s)
    | TComp _ => empty_set zex (* to be handled later... *)
    end        
  end.

Fixpoint make_ss_ivar (il: ivarlist) :=
  match il with
  | LastI id st => cons (pair id (pv st)) nil
  | AddI id st rest => cons (pair id (pv st))
                            (make_ss_ivar rest)
  end.



Definition make_state_space (m: smv_module) :=
  match vars m with
  | None => nil
  | Some vl => make_ss vl
  end.

Compute make_state_space inverter.
Compute make_state_space ex1.
Compute make_state_space clock.

*)
