
val add : int -> int -> int

val sub : int -> int -> int

module Nat :
 sig
  val leb : int -> int -> bool

  val ltb : int -> int -> bool
 end

module type BT_SIG =
 sig
  type skillSet

  val skillName : skillSet -> char list
 end

module BT_gen_rsem :
 functor (X:BT_SIG) ->
 sig
  type nodeKind =
  | Sequence
  | Fallback
  | Parallel of int

  val nodeKind_rect : 'a1 -> 'a1 -> (int -> 'a1) -> nodeKind -> 'a1

  val nodeKind_rec : 'a1 -> 'a1 -> (int -> 'a1) -> nodeKind -> 'a1

  type decKind =
  | Not
  | IsRunning

  val decKind_rect : 'a1 -> 'a1 -> decKind -> 'a1

  val decKind_rec : 'a1 -> 'a1 -> decKind -> 'a1

  type btree =
  | Skill of X.skillSet
  | TRUE
  | Node of nodeKind * char list * btforest
  | Dec of decKind * char list * btree
  and btforest =
  | Child of btree
  | Add of btree * btforest

  val btree_rect :
    (X.skillSet -> 'a1) -> 'a1 -> (nodeKind -> char list -> btforest -> 'a1)
    -> (decKind -> char list -> btree -> 'a1 -> 'a1) -> btree -> 'a1

  val btree_rec :
    (X.skillSet -> 'a1) -> 'a1 -> (nodeKind -> char list -> btforest -> 'a1)
    -> (decKind -> char list -> btree -> 'a1 -> 'a1) -> btree -> 'a1

  val btforest_rect :
    (btree -> 'a1) -> (btree -> btforest -> 'a1 -> 'a1) -> btforest -> 'a1

  val btforest_rec :
    (btree -> 'a1) -> (btree -> btforest -> 'a1 -> 'a1) -> btforest -> 'a1

  val len : btforest -> int

  val count_skills : btree -> int

  val cs_forest : btforest -> int

  val normalize : btree -> btree

  val normalize_forest : btforest -> btforest

  type return_enum =
  | Runn
  | Fail
  | Succ

  val return_enum_rect : 'a1 -> 'a1 -> 'a1 -> return_enum -> 'a1

  val return_enum_rec : 'a1 -> 'a1 -> 'a1 -> return_enum -> 'a1

  type skills_input = X.skillSet -> return_enum

  type skills_reset = X.skillSet -> bool

  val countSucc : return_enum list -> int

  val countFail : return_enum list -> int

  val reset : btree -> skills_reset -> bool

  val reset_forest : btforest -> skills_reset -> bool

  val tick : btree -> skills_input -> skills_reset -> return_enum

  val tick_sequence : btforest -> skills_input -> skills_reset -> return_enum

  val tick_fallback : btforest -> skills_input -> skills_reset -> return_enum

  val tick_all : btforest -> skills_input -> skills_reset -> return_enum list
 end
