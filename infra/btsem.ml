
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val sub : int -> int -> int **)

let rec sub n m =
  (fun fO fS n -> if n=0 then fO () else fS (n-1))
    (fun _ -> n)
    (fun k ->
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n)
      (fun l -> sub k l)
      m)
    n

module Nat =
 struct
  (** val leb : int -> int -> bool **)

  let rec leb n m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun m' -> leb n' m')
        m)
      n

  (** val ltb : int -> int -> bool **)

  let ltb n m =
    leb (succ n) m
 end

module type BT_SIG =
 sig
  type skillSet

  val skillName : skillSet -> char list
 end

module BT_gen_semantics =
 functor (X:BT_SIG) ->
 struct
  type nodeKind =
  | Sequence
  | Fallback
  | Parallel of int

  (** val nodeKind_rect : 'a1 -> 'a1 -> (int -> 'a1) -> nodeKind -> 'a1 **)

  let nodeKind_rect f f0 f1 = function
  | Sequence -> f
  | Fallback -> f0
  | Parallel x -> f1 x

  (** val nodeKind_rec : 'a1 -> 'a1 -> (int -> 'a1) -> nodeKind -> 'a1 **)

  let nodeKind_rec f f0 f1 = function
  | Sequence -> f
  | Fallback -> f0
  | Parallel x -> f1 x

  type decKind =
  | Not
  | IsRunning

  (** val decKind_rect : 'a1 -> 'a1 -> decKind -> 'a1 **)

  let decKind_rect f f0 = function
  | Not -> f
  | IsRunning -> f0

  (** val decKind_rec : 'a1 -> 'a1 -> decKind -> 'a1 **)

  let decKind_rec f f0 = function
  | Not -> f
  | IsRunning -> f0

  type btree =
  | Skill of X.skillSet
  | TRUE
  | Node of nodeKind * char list * btforest
  | Dec of decKind * char list * btree
  and btforest =
  | Child of btree
  | Add of btree * btforest

  (** val btree_rect :
      (X.skillSet -> 'a1) -> 'a1 -> (nodeKind -> char list -> btforest ->
      'a1) -> (decKind -> char list -> btree -> 'a1 -> 'a1) -> btree -> 'a1 **)

  let rec btree_rect f f0 f1 f2 = function
  | Skill s -> f s
  | TRUE -> f0
  | Node (n, s, b0) -> f1 n s b0
  | Dec (d, s, b0) -> f2 d s b0 (btree_rect f f0 f1 f2 b0)

  (** val btree_rec :
      (X.skillSet -> 'a1) -> 'a1 -> (nodeKind -> char list -> btforest ->
      'a1) -> (decKind -> char list -> btree -> 'a1 -> 'a1) -> btree -> 'a1 **)

  let rec btree_rec f f0 f1 f2 = function
  | Skill s -> f s
  | TRUE -> f0
  | Node (n, s, b0) -> f1 n s b0
  | Dec (d, s, b0) -> f2 d s b0 (btree_rec f f0 f1 f2 b0)

  (** val btforest_rect :
      (btree -> 'a1) -> (btree -> btforest -> 'a1 -> 'a1) -> btforest -> 'a1 **)

  let rec btforest_rect f f0 = function
  | Child b0 -> f b0
  | Add (b0, b1) -> f0 b0 b1 (btforest_rect f f0 b1)

  (** val btforest_rec :
      (btree -> 'a1) -> (btree -> btforest -> 'a1 -> 'a1) -> btforest -> 'a1 **)

  let rec btforest_rec f f0 = function
  | Child b0 -> f b0
  | Add (b0, b1) -> f0 b0 b1 (btforest_rec f f0 b1)

  (** val len : btforest -> int **)

  let rec len = function
  | Child _ -> succ 0
  | Add (_, rest) -> succ (len rest)

  (** val sklist : btree -> X.skillSet list **)

  let rec sklist = function
  | Skill s -> s :: []
  | TRUE -> []
  | Node (_, _, f) -> skl_forest f
  | Dec (_, _, t0) -> sklist t0

  (** val skl_forest : btforest -> X.skillSet list **)

  and skl_forest = function
  | Child t -> sklist t
  | Add (t, tl) -> app (sklist t) (skl_forest tl)

  (** val normalize : btree -> btree **)

  let rec normalize = function
  | Node (k, n, f) ->
    (match k with
     | Parallel _ -> Node (k, n, (normalize_forest f))
     | _ ->
       (match f with
        | Child t0 -> t0
        | Add (_, _) -> Node (k, n, (normalize_forest f))))
  | Dec (k, n, t0) ->
    (match k with
     | Not ->
       (match t0 with
        | Dec (d, _, t') ->
          (match d with
           | Not -> t'
           | IsRunning -> Dec (Not, n, (normalize t0)))
        | _ -> Dec (Not, n, (normalize t0)))
     | IsRunning -> Dec (k, n, (normalize t0)))
  | x -> x

  (** val normalize_forest : btforest -> btforest **)

  and normalize_forest = function
  | Child t -> Child (normalize t)
  | Add (t, ts) -> Add ((normalize t), (normalize_forest ts))

  type return_enum =
  | Runn
  | Fail
  | Succ

  (** val return_enum_rect : 'a1 -> 'a1 -> 'a1 -> return_enum -> 'a1 **)

  let return_enum_rect f f0 f1 = function
  | Runn -> f
  | Fail -> f0
  | Succ -> f1

  (** val return_enum_rec : 'a1 -> 'a1 -> 'a1 -> return_enum -> 'a1 **)

  let return_enum_rec f f0 f1 = function
  | Runn -> f
  | Fail -> f0
  | Succ -> f1

  type skills_input = X.skillSet -> return_enum

  (** val countSucc : return_enum list -> int **)

  let rec countSucc = function
  | [] -> 0
  | head :: tail ->
    (match head with
     | Succ -> succ (countSucc tail)
     | _ -> countSucc tail)

  (** val countFail : return_enum list -> int **)

  let rec countFail = function
  | [] -> 0
  | head :: tail ->
    (match head with
     | Fail -> succ (countFail tail)
     | _ -> countFail tail)

  (** val tick : btree -> skills_input -> return_enum **)

  let rec tick t input_f =
    match t with
    | Skill s -> input_f s
    | TRUE -> Succ
    | Node (k, _, f) ->
      (match k with
       | Sequence -> tick_sequence f input_f
       | Fallback -> tick_fallback f input_f
       | Parallel n ->
         let results = tick_all f input_f in
         if Nat.leb n (countSucc results)
         then Succ
         else if Nat.ltb (sub (len f) n) (countFail results)
              then Fail
              else Runn)
    | Dec (k, _, t0) ->
      (match k with
       | Not ->
         (match tick t0 input_f with
          | Runn -> Runn
          | Fail -> Succ
          | Succ -> Fail)
       | IsRunning -> (match tick t0 input_f with
                       | Runn -> Succ
                       | _ -> Fail))

  (** val tick_sequence : btforest -> skills_input -> return_enum **)

  and tick_sequence f input_f =
    match f with
    | Child t -> tick t input_f
    | Add (t1, rest) ->
      (match tick t1 input_f with
       | Succ -> tick_sequence rest input_f
       | x -> x)

  (** val tick_fallback : btforest -> skills_input -> return_enum **)

  and tick_fallback f input_f =
    match f with
    | Child t -> tick t input_f
    | Add (t1, rest) ->
      (match tick t1 input_f with
       | Fail -> tick_fallback rest input_f
       | x -> x)

  (** val tick_all : btforest -> skills_input -> return_enum list **)

  and tick_all f input_f =
    match f with
    | Child t -> (tick t input_f) :: []
    | Add (t1, rest) -> (tick t1 input_f) :: (tick_all rest input_f)
 end
