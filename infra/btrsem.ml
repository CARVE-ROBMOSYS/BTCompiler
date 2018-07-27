
(** val add : int -> int -> int **)

let rec add = ( + )

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

(** val hd : 'a1 -> 'a1 list -> 'a1 **)

let hd default = function
| [] -> default
| x :: _ -> x

(** val tl : 'a1 list -> 'a1 list **)

let tl = function
| [] -> []
| _ :: m -> m

module type BT_SIG =
 sig
  type skillSet

  val skillName : skillSet -> char list
 end

module BT_gen_rsem =
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

  let btree_rect f f0 f1 f2 =
    let rec f3 = function
    | Skill s -> f s
    | TRUE -> f0
    | Node (n, s, b0) -> f1 n s b0
    | Dec (d, s, b0) -> f2 d s b0 (f3 b0)
    in f3

  (** val btree_rec :
      (X.skillSet -> 'a1) -> 'a1 -> (nodeKind -> char list -> btforest ->
      'a1) -> (decKind -> char list -> btree -> 'a1 -> 'a1) -> btree -> 'a1 **)

  let btree_rec f f0 f1 f2 =
    let rec f3 = function
    | Skill s -> f s
    | TRUE -> f0
    | Node (n, s, b0) -> f1 n s b0
    | Dec (d, s, b0) -> f2 d s b0 (f3 b0)
    in f3

  (** val btforest_rect :
      (btree -> 'a1) -> (btree -> btforest -> 'a1 -> 'a1) -> btforest -> 'a1 **)

  let btforest_rect f f0 =
    let rec f1 = function
    | Child b0 -> f b0
    | Add (b0, b1) -> f0 b0 b1 (f1 b1)
    in f1

  (** val btforest_rec :
      (btree -> 'a1) -> (btree -> btforest -> 'a1 -> 'a1) -> btforest -> 'a1 **)

  let btforest_rec f f0 =
    let rec f1 = function
    | Child b0 -> f b0
    | Add (b0, b1) -> f0 b0 b1 (f1 b1)
    in f1

  (** val len : btforest -> int **)

  let rec len = function
  | Child _ -> succ 0
  | Add (_, rest) -> succ (len rest)

  (** val count_skills : btree -> int **)

  let rec count_skills = function
  | Skill _ -> succ 0
  | TRUE -> 0
  | Node (_, _, f) -> cs_forest f
  | Dec (_, _, t0) -> count_skills t0

  (** val cs_forest : btforest -> int **)

  and cs_forest = function
  | Child t -> count_skills t
  | Add (t, tl0) -> add (count_skills t) (cs_forest tl0)

  (** val normalize : btree -> btree **)

  let rec normalize = function
  | Skill s -> Skill s
  | TRUE -> TRUE
  | Node (k, n, f) ->
    (match k with
     | Sequence ->
       (match f with
        | Child t0 -> t0
        | Add (_, _) -> Node (k, n, (normalize_forest f)))
     | Fallback ->
       (match f with
        | Child t0 -> t0
        | Add (_, _) -> Node (k, n, (normalize_forest f)))
     | Parallel _ -> Node (k, n, (normalize_forest f)))
  | Dec (k, n, t0) ->
    (match k with
     | Not ->
       (match t0 with
        | Skill _ -> Dec (Not, n, (normalize t0))
        | TRUE -> Dec (Not, n, (normalize t0))
        | Node (_, _, _) -> Dec (Not, n, (normalize t0))
        | Dec (d, _, t') ->
          (match d with
           | Not -> t'
           | IsRunning -> Dec (Not, n, (normalize t0))))
     | IsRunning -> Dec (k, n, (normalize t0)))

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

  type skills_reset = X.skillSet -> bool

  (** val countSucc : return_enum list -> int **)

  let rec countSucc = function
  | [] -> 0
  | head :: tail ->
    (match head with
     | Runn -> countSucc tail
     | Fail -> countSucc tail
     | Succ -> succ (countSucc tail))

  (** val countFail : return_enum list -> int **)

  let rec countFail = function
  | [] -> 0
  | head :: tail ->
    (match head with
     | Runn -> countFail tail
     | Fail -> succ (countFail tail)
     | Succ -> countFail tail)

  (** val reset_bt : btree -> skills_reset -> bool **)

  let rec reset_bt t reset_f =
    match t with
    | Skill s -> reset_f s
    | TRUE -> true
    | Node (_, _, f) -> reset_forest f reset_f
    | Dec (_, _, t0) -> reset_bt t0 reset_f

  (** val reset_forest : btforest -> skills_reset -> bool **)

  and reset_forest f reset_f =
    match f with
    | Child t -> reset_bt t reset_f
    | Add (t1, rest) ->
      let x = reset_bt t1 reset_f in (&&) x (reset_forest rest reset_f)

  (** val reset_running :
      btforest -> return_enum list -> skills_reset -> bool **)

  let rec reset_running f l reset_f =
    match f with
    | Child t ->
      (match hd Fail l with
       | Runn -> reset_bt t reset_f
       | Fail -> true
       | Succ -> true)
    | Add (t1, rest) ->
      let x =
        match hd Fail l with
        | Runn -> reset_bt t1 reset_f
        | Fail -> true
        | Succ -> true
      in
      (&&) x (reset_running rest (tl l) reset_f)

  (** val tick : btree -> skills_input -> skills_reset -> return_enum **)

  let rec tick t input_f reset_f =
    match t with
    | Skill s -> input_f s
    | TRUE -> Succ
    | Node (k, _, f) ->
      (match k with
       | Sequence -> tick_sequence f input_f reset_f
       | Fallback -> tick_fallback f input_f reset_f
       | Parallel n ->
         let results = tick_all f input_f reset_f in
         if Nat.leb n (countSucc results)
         then let b = reset_running f results reset_f in
              if b then Succ else Fail
         else if Nat.ltb (sub (len f) n) (countFail results)
              then let b = reset_running f results reset_f in
                   if b then Fail else Fail
              else Runn)
    | Dec (k, _, t0) ->
      (match k with
       | Not ->
         (match tick t0 input_f reset_f with
          | Runn -> Runn
          | Fail -> Succ
          | Succ -> Fail)
       | IsRunning ->
         (match tick t0 input_f reset_f with
          | Runn -> Succ
          | Fail -> Fail
          | Succ -> Fail))

  (** val tick_sequence :
      btforest -> skills_input -> skills_reset -> return_enum **)

  and tick_sequence f input_f reset_f =
    match f with
    | Child t -> tick t input_f reset_f
    | Add (t1, rest) ->
      (match tick t1 input_f reset_f with
       | Runn -> let b = reset_forest rest reset_f in if b then Runn else Fail
       | Fail -> let b = reset_forest rest reset_f in if b then Fail else Fail
       | Succ -> tick_sequence rest input_f reset_f)

  (** val tick_fallback :
      btforest -> skills_input -> skills_reset -> return_enum **)

  and tick_fallback f input_f reset_f =
    match f with
    | Child t -> tick t input_f reset_f
    | Add (t1, rest) ->
      (match tick t1 input_f reset_f with
       | Runn -> let b = reset_forest rest reset_f in if b then Runn else Fail
       | Fail -> tick_fallback rest input_f reset_f
       | Succ -> let b = reset_forest rest reset_f in if b then Succ else Fail)

  (** val tick_all :
      btforest -> skills_input -> skills_reset -> return_enum list **)

  and tick_all f input_f reset_f =
    match f with
    | Child t -> (tick t input_f reset_f) :: []
    | Add (t1, rest) ->
      (tick t1 input_f reset_f) :: (tick_all rest input_f reset_f)
 end
