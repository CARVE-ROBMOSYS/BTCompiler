
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

(** val add : int -> int -> int **)

let rec add = ( + )

module Nat =
 struct
  (** val sub : int -> int -> int **)

  let rec sub n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> n0)
      (fun k ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> n0)
        (fun l -> sub k l)
        m)
      n0

  (** val eqb : int -> int -> bool **)

  let rec eqb n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun m' -> eqb n' m')
        m)
      n0

  (** val leb : int -> int -> bool **)

  let rec leb n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> true)
      (fun n' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun m' -> leb n' m')
        m)
      n0

  (** val ltb : int -> int -> bool **)

  let ltb n0 m =
    leb (succ n0) m

  (** val divmod : int -> int -> int -> int -> int * int **)

  let rec divmod x y q u =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> (q, u))
      (fun x' ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> divmod x' y (succ q) y)
        (fun u' -> divmod x' y q u')
        u)
      x

  (** val div : int -> int -> int **)

  let div x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> y)
      (fun y' -> fst (divmod x y' 0 y'))
      y

  (** val modulo : int -> int -> int **)

  let modulo x y =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> y)
      (fun y' -> sub y' (snd (divmod x y' 0 y')))
      y

  (** val eq_dec : int -> int -> bool **)

  let rec eq_dec n0 m =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun n1 ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> false)
        (fun m0 -> eq_dec n1 m0)
        m)
      n0
 end

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val of_succ_nat : int -> positive **)

  let rec of_succ_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> XH)
      (fun x -> succ (of_succ_nat x))
      n0
 end

module N =
 struct
  (** val of_nat : int -> n **)

  let of_nat n0 =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> N0)
      (fun n' -> Npos (Pos.of_succ_nat n'))
      n0
 end

(** val zero : char **)

let zero = '\000'

(** val one : char **)

let one = '\001'

(** val shift : bool -> char -> char **)

let shift = fun b c -> Char.chr (((Char.code c) lsl 1) land 255 + if b then 1 else 0)

(** val ascii_of_pos : positive -> char **)

let ascii_of_pos =
  let rec loop n0 p =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> zero)
      (fun n' ->
      match p with
      | XI p' -> shift true (loop n' p')
      | XO p' -> shift false (loop n' p')
      | XH -> one)
      n0
  in loop (succ (succ (succ (succ (succ (succ (succ (succ 0))))))))

(** val ascii_of_N : n -> char **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : int -> char **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

(** val append : char list -> char list -> char list **)

let rec append s1 s2 =
  match s1 with
  | [] -> s2
  | c::s1' -> c::(append s1' s2)

(** val concat : char list -> char list list -> char list **)

let rec concat sep = function
| [] -> []
| x :: xs ->
  (match xs with
   | [] -> x
   | _ :: _ -> append x (append sep (concat sep xs)))

module type BT_SIG =
 sig
  type skillSet

  val skillName : skillSet -> char list
 end

type symbolic_constant = char list

type identifier = char list

type bool_constant =
| SmvF
| SmvT

type qualid =
| Id of identifier
| Mod of identifier * qualid

type sexp =
| BConst of bool_constant
| SConst of symbolic_constant
| Qual of qualid
| Paren of sexp
| Neg of sexp
| And of sexp * sexp
| Or of sexp * sexp
| Equal of sexp * sexp
| Less of sexp * sexp
| Sum of sexp * sexp
| Count of sexplist
| Case of scexp
and sexplist =
| Sexp of sexp
| AddSexp of sexp * sexplist
and scexp =
| Cexp of sexp * sexp
| AddCexp of sexp * sexp * scexp

type nexp =
| Simple of sexp
| Basic of sexp

type simp_type_spec =
| TBool
| TEnum of symbolic_constant list

type param_list =
| LastP of nexp
| AddP of nexp * param_list

type mod_type_spec =
| TMod of identifier
| TModPar of identifier * param_list

type type_spec =
| TSimp of simp_type_spec
| TComp of mod_type_spec

type varlist =
| LastV of identifier * type_spec
| AddV of identifier * type_spec * varlist

type ivarlist =
| LastI of identifier * simp_type_spec
| AddI of identifier * simp_type_spec * ivarlist

type deflist =
| LastD of identifier * sexp
| AddD of identifier * sexp * deflist

type assign_cons =
| Invar of qualid * sexp
| Init of qualid * sexp
| Next of qualid * nexp

type asslist =
| LastA of assign_cons
| AddA of assign_cons * asslist

type smv_module = { name : identifier; params : identifier list;
                    vars : varlist option; ivars : ivarlist option;
                    defs : deflist option; assigns : asslist option }

(** val name : smv_module -> identifier **)

let name x = x.name

(** val params : smv_module -> identifier list **)

let params x = x.params

(** val vars : smv_module -> varlist option **)

let vars x = x.vars

(** val ivars : smv_module -> ivarlist option **)

let ivars x = x.ivars

(** val defs : smv_module -> deflist option **)

let defs x = x.defs

(** val assigns : smv_module -> asslist option **)

let assigns x = x.assigns

type smv_spec = smv_module list

(** val varlist_app : varlist -> varlist -> varlist **)

let rec varlist_app a b =
  match a with
  | LastV (v, t) -> AddV (v, t, b)
  | AddV (v, t, c) -> AddV (v, t, (varlist_app c b))

(** val newline : char list **)

let newline =
  '\n'::[]

(** val translate_qualid : qualid -> identifier **)

let rec translate_qualid = function
| Id i -> i
| Mod (m, q') -> append m (append ('.'::[]) (translate_qualid q'))

(** val translate_sexp : sexp -> char list **)

let rec translate_sexp = function
| BConst bc ->
  (match bc with
   | SmvF -> 'F'::('A'::('L'::('S'::('E'::[]))))
   | SmvT -> 'T'::('R'::('U'::('E'::[]))))
| SConst sc -> sc
| Qual q -> translate_qualid q
| Paren e' -> append ('('::[]) (append (translate_sexp e') (')'::[]))
| Neg e' -> append ('!'::('('::[])) (append (translate_sexp e') (')'::[]))
| And (e', e'') ->
  append (translate_sexp e')
    (append (' '::('&'::(' '::[]))) (translate_sexp e''))
| Or (e', e'') ->
  append (translate_sexp e')
    (append (' '::('|'::(' '::[]))) (translate_sexp e''))
| Equal (e', e'') ->
  append (translate_sexp e')
    (append (' '::('='::(' '::[]))) (translate_sexp e''))
| Less (e', e'') ->
  append (translate_sexp e')
    (append (' '::('<'::(' '::[]))) (translate_sexp e''))
| Sum (e', e'') ->
  append (translate_sexp e')
    (append (' '::('+'::(' '::[]))) (translate_sexp e''))
| Count lst ->
  append ('c'::('o'::('u'::('n'::('t'::('('::[]))))))
    (append (translate_sexplist lst) (')'::[]))
| Case ce ->
  append ('c'::('a'::('s'::('e'::[]))))
    (append newline
      (append (translate_cexp ce) ('e'::('s'::('a'::('c'::[]))))))

(** val translate_sexplist : sexplist -> char list **)

and translate_sexplist = function
| Sexp e -> translate_sexp e
| AddSexp (e, rest) ->
  append (translate_sexp e)
    (append (','::(' '::[])) (translate_sexplist rest))

(** val translate_cexp : scexp -> char list **)

and translate_cexp = function
| Cexp (e1, e2) ->
  append (translate_sexp e1)
    (append (' '::(':'::(' '::[])))
      (append (translate_sexp e2) (append (';'::[]) newline)))
| AddCexp (e1, e2, rest) ->
  append (translate_sexp e1)
    (append (' '::(':'::(' '::[])))
      (append (translate_sexp e2)
        (append (';'::[]) (append newline (translate_cexp rest)))))

(** val translate_nexp : nexp -> char list **)

let translate_nexp = function
| Simple e' -> translate_sexp e'
| Basic e' ->
  append ('n'::('e'::('x'::('t'::('('::[])))))
    (append (translate_sexp e') (')'::[]))

(** val translate_simp_type_spec : simp_type_spec -> char list **)

let translate_simp_type_spec = function
| TBool -> 'b'::('o'::('o'::('l'::('e'::('a'::('n'::[]))))))
| TEnum values ->
  append ('{'::(' '::[]))
    (append (concat (','::(' '::[])) values) (' '::('}'::[])))

(** val translate_param_list : param_list -> char list **)

let rec translate_param_list = function
| LastP e -> translate_nexp e
| AddP (e, pl') ->
  append (translate_nexp e)
    (append (','::(' '::[])) (translate_param_list pl'))

(** val translate_mod_type_spec : mod_type_spec -> identifier **)

let rec translate_mod_type_spec = function
| TMod i -> i
| TModPar (i, pl) ->
  append i (append ('('::[]) (append (translate_param_list pl) (')'::[])))

(** val translate_type_spec : type_spec -> char list **)

let translate_type_spec = function
| TSimp sts -> translate_simp_type_spec sts
| TComp mts -> translate_mod_type_spec mts

(** val translate_varlist : varlist -> char list **)

let rec translate_varlist = function
| LastV (id, ty) ->
  append id
    (append (' '::(':'::(' '::[])))
      (append (translate_type_spec ty) (append (';'::[]) newline)))
| AddV (id, ty, rest) ->
  append id
    (append (' '::(':'::(' '::[])))
      (append (translate_type_spec ty)
        (append (';'::[]) (append newline (translate_varlist rest)))))

(** val translate_ivarlist : ivarlist -> char list **)

let rec translate_ivarlist = function
| LastI (id, ty) ->
  append id
    (append (' '::(':'::(' '::[])))
      (append (translate_simp_type_spec ty) (append (';'::[]) newline)))
| AddI (id, ty, rest) ->
  append id
    (append (' '::(':'::(' '::[])))
      (append (translate_simp_type_spec ty)
        (append (';'::[]) (append newline (translate_ivarlist rest)))))

(** val translate_deflist : deflist -> char list **)

let rec translate_deflist = function
| LastD (id, e) ->
  append id
    (append (' '::(':'::('='::(' '::[]))))
      (append (translate_sexp e) (append (';'::[]) newline)))
| AddD (id, e, rest) ->
  append id
    (append (' '::(':'::('='::(' '::[]))))
      (append (translate_sexp e)
        (append (';'::[]) (append newline (translate_deflist rest)))))

(** val translate_assign_cons : assign_cons -> char list **)

let translate_assign_cons = function
| Invar (q, e) ->
  append (translate_qualid q)
    (append (' '::(':'::('='::(' '::[]))))
      (append (translate_sexp e) (append (';'::[]) newline)))
| Init (q, e) ->
  append ('i'::('n'::('i'::('t'::('('::[])))))
    (append (translate_qualid q)
      (append (')'::(' '::(':'::('='::(' '::[])))))
        (append (translate_sexp e) (append (';'::[]) newline))))
| Next (q, ne) ->
  append ('n'::('e'::('x'::('t'::('('::[])))))
    (append (translate_qualid q)
      (append (')'::(' '::(':'::('='::(' '::[])))))
        (append (translate_nexp ne) (append (';'::[]) newline))))

(** val translate_asslist : asslist -> char list **)

let rec translate_asslist = function
| LastA c -> translate_assign_cons c
| AddA (c, rest) -> append (translate_assign_cons c) (translate_asslist rest)

(** val translate : smv_module -> char list **)

let translate m =
  append ('M'::('O'::('D'::('U'::('L'::('E'::(' '::[])))))))
    (append m.name
      (append ('('::[])
        (append (concat (','::(' '::[])) m.params)
          (append (')'::[])
            (append newline
              (append
                (match m.vars with
                 | Some vl ->
                   append ('V'::('A'::('R'::[])))
                     (append newline (translate_varlist vl))
                 | None -> [])
                (append
                  (match m.ivars with
                   | Some il ->
                     append ('I'::('V'::('A'::('R'::[]))))
                       (append newline (translate_ivarlist il))
                   | None -> [])
                  (append
                    (match m.defs with
                     | Some dl ->
                       append ('D'::('E'::('F'::('I'::('N'::('E'::[]))))))
                         (append newline (translate_deflist dl))
                     | None -> [])
                    (append
                      (match m.assigns with
                       | Some al ->
                         append ('A'::('S'::('S'::('I'::('G'::('N'::[]))))))
                           (append newline (translate_asslist al))
                       | None -> []) newline)))))))))

(** val translate_spec : smv_spec -> char list **)

let rec translate_spec = function
| [] -> []
| m :: rest -> append (translate m) (translate_spec rest)

type 'a set = 'a list

(** val empty_set : 'a1 set **)

let empty_set =
  []

(** val set_add : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_add aeq_dec a = function
| [] -> a :: []
| a1 :: x1 -> if aeq_dec a a1 then a1 :: x1 else a1 :: (set_add aeq_dec a x1)

(** val bt_output_type : simp_type_spec **)

let bt_output_type =
  TEnum
    (('n'::('o'::('n'::('e'::[])))) :: (('r'::('u'::('n'::('n'::('i'::('n'::('g'::[]))))))) :: (('f'::('a'::('i'::('l'::('e'::('d'::[])))))) :: (('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[]))))))))) :: []))))

(** val bt_action_type : simp_type_spec **)

let bt_action_type =
  TEnum
    (('E'::('n'::('a'::('b'::('l'::('e'::[])))))) :: (('R'::('e'::('s'::('e'::('t'::[]))))) :: []))

(** val bp_tick_generator : smv_module **)

let bp_tick_generator =
  { name =
    ('b'::('t'::('_'::('t'::('i'::('c'::('k'::('_'::('g'::('e'::('n'::('e'::('r'::('a'::('t'::('o'::('r'::[])))))))))))))))));
    params =
    (('t'::('o'::('p'::('_'::('l'::('e'::('v'::('e'::('l'::('_'::('b'::('t'::[])))))))))))) :: []);
    vars = None; ivars = None; defs = None; assigns = (Some (AddA ((Init
    ((Mod
    (('t'::('o'::('p'::('_'::('l'::('e'::('v'::('e'::('l'::('_'::('b'::('t'::[])))))))))))),
    (Id ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (BConst SmvT))),
    (LastA (Next ((Mod
    (('t'::('o'::('p'::('_'::('l'::('e'::('v'::('e'::('l'::('_'::('b'::('t'::[])))))))))))),
    (Id ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Simple (Neg (Equal
    ((Qual (Mod
    (('t'::('o'::('p'::('_'::('l'::('e'::('v'::('e'::('l'::('_'::('b'::('t'::[])))))))))))),
    (Id ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
    ('n'::('o'::('n'::('e'::[]))))))))))))))) }

(** val bp_skill : smv_module **)

let bp_skill =
  { name = ('b'::('t'::('_'::('s'::('k'::('i'::('l'::('l'::[]))))))));
    params = []; vars = (Some (AddV
    (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (TSimp bt_output_type),
    (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp TBool))))));
    ivars = None; defs = None; assigns = None }

(** val bp_TRUE : smv_module **)

let bp_TRUE =
  { name = ('b'::('t'::('_'::('T'::('R'::('U'::('E'::[]))))))); params = [];
    vars = (Some (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp
    TBool)))); ivars = None; defs = (Some (LastD
    (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (SConst
    ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))));
    assigns = None }

(** val bp_not : smv_module **)

let bp_not =
  { name = ('b'::('t'::('_'::('n'::('o'::('t'::[])))))); params =
    (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))) :: []);
    vars = (Some (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp
    TBool)))); ivars = None; defs = (Some (LastD
    (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case (AddCexp ((Equal
    ((Qual (Mod (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))),
    (Id ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
    ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))), (SConst
    ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))),
    (AddCexp ((Equal ((Qual (Mod
    (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))), (Id
    ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
    ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))),
    (SConst ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))), (Cexp ((BConst
    SmvT), (Qual (Mod
    (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))), (Id
    ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))))))))))))); assigns =
    (Some (LastA (Invar ((Mod
    (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))), (Id
    ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
    ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))))) }

(** val bp_isRunning : smv_module **)

let bp_isRunning =
  { name =
    ('b'::('t'::('_'::('i'::('s'::('R'::('u'::('n'::('n'::('i'::('n'::('g'::[]))))))))))));
    params =
    (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))) :: []);
    vars = (Some (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp
    TBool)))); ivars = None; defs = (Some (LastD
    (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case (AddCexp ((Equal
    ((Qual (Mod (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))),
    (Id ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
    ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))))), (SConst
    ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))),
    (AddCexp ((Equal ((Qual (Mod
    (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))), (Id
    ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
    ('n'::('o'::('n'::('e'::[]))))))), (SConst
    ('n'::('o'::('n'::('e'::[]))))), (Cexp ((BConst SmvT), (SConst
    ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))))))))); assigns = (Some
    (LastA (Invar ((Mod
    (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))), (Id
    ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
    ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))))) }

type modtype =
| Skmod
| TRUEmod
| Seqmod of int
| Fbmod of int
| Parmod of int * int
| Notmod
| Runmod

(** val modtype_dec : modtype -> modtype -> bool **)

let modtype_dec x y =
  match x with
  | Skmod -> (match y with
              | Skmod -> true
              | _ -> false)
  | TRUEmod -> (match y with
                | TRUEmod -> true
                | _ -> false)
  | Seqmod x0 -> (match y with
                  | Seqmod n0 -> Nat.eq_dec x0 n0
                  | _ -> false)
  | Fbmod x0 -> (match y with
                 | Fbmod n0 -> Nat.eq_dec x0 n0
                 | _ -> false)
  | Parmod (x0, x1) ->
    (match y with
     | Parmod (n1, n2) -> if Nat.eq_dec x0 n1 then Nat.eq_dec x1 n2 else false
     | _ -> false)
  | Notmod -> (match y with
               | Notmod -> true
               | _ -> false)
  | Runmod -> (match y with
               | Runmod -> true
               | _ -> false)

(** val bp_identity : char list -> smv_module **)

let bp_identity name0 =
  { name = name0; params = (('b'::('t'::[])) :: []); vars = (Some (LastV
    (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp TBool)))); ivars =
    None; defs = (Some (LastD (('o'::('u'::('t'::('p'::('u'::('t'::[])))))),
    (Qual (Mod (('b'::('t'::[])), (Id
    ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))); assigns = (Some
    (LastA (Invar ((Mod (('b'::('t'::[])), (Id
    ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
    ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))))) }

module BT_gen_spec =
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
  | Node (n0, s, b0) -> f1 n0 s b0
  | Dec (d, s, b0) -> f2 d s b0 (btree_rect f f0 f1 f2 b0)

  (** val btree_rec :
      (X.skillSet -> 'a1) -> 'a1 -> (nodeKind -> char list -> btforest ->
      'a1) -> (decKind -> char list -> btree -> 'a1 -> 'a1) -> btree -> 'a1 **)

  let rec btree_rec f f0 f1 f2 = function
  | Skill s -> f s
  | TRUE -> f0
  | Node (n0, s, b0) -> f1 n0 s b0
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
  | Node (k, n0, f) ->
    (match k with
     | Parallel _ -> Node (k, n0, (normalize_forest f))
     | _ ->
       (match f with
        | Child t0 -> t0
        | Add (_, _) -> Node (k, n0, (normalize_forest f))))
  | Dec (k, n0, t0) ->
    (match k with
     | Not ->
       (match t0 with
        | Dec (d, _, t') ->
          (match d with
           | Not -> t'
           | IsRunning -> Dec (Not, n0, (normalize t0)))
        | _ -> Dec (Not, n0, (normalize t0)))
     | IsRunning -> Dec (k, n0, (normalize t0)))
  | x -> x

  (** val normalize_forest : btforest -> btforest **)

  and normalize_forest = function
  | Child t -> Child (normalize t)
  | Add (t, ts) -> Add ((normalize t), (normalize_forest ts))

  (** val rootName : btree -> char list **)

  let rootName = function
  | Skill s -> X.skillName s
  | TRUE -> 'B'::('T'::('S'::('u'::('c'::('c'::[])))))
  | Node (_, n0, _) -> n0
  | Dec (_, n0, _) -> n0

  (** val string_of_nat : int -> char list **)

  let string_of_nat n0 =
    if Nat.ltb n0 (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
         0))))))))))
    then (ascii_of_nat
           (add n0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
             (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
             (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
             (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
             (succ (succ (succ (succ (succ (succ (succ (succ (succ
             0))))))))))))))))))))))))))))))))))))))))))))))))))::[]
    else if Nat.ltb n0 (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
              (succ
              0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         then let q =
                Nat.div n0 (succ (succ (succ (succ (succ (succ (succ (succ
                  (succ (succ 0))))))))))
              in
              let r =
                Nat.modulo n0 (succ (succ (succ (succ (succ (succ (succ (succ
                  (succ (succ 0))))))))))
              in
              (ascii_of_nat
                (add q (succ (succ (succ (succ (succ (succ (succ (succ (succ
                  (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                  (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                  (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                  (succ (succ (succ (succ (succ (succ (succ (succ (succ
                  0))))))))))))))))))))))))))))))))))))))))))))))))))::(
              (ascii_of_nat
                (add r (succ (succ (succ (succ (succ (succ (succ (succ (succ
                  (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                  (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                  (succ (succ (succ (succ (succ (succ (succ (succ (succ (succ
                  (succ (succ (succ (succ (succ (succ (succ (succ (succ
                  0))))))))))))))))))))))))))))))))))))))))))))))))))::[])
         else '1'::('0'::('0'::[]))

  (** val nodeName : nodeKind -> int -> char list **)

  let nodeName k n0 =
    match k with
    | Sequence ->
      append
        ('b'::('t'::('_'::('s'::('e'::('q'::('u'::('e'::('n'::('c'::('e'::('_'::[]))))))))))))
        (string_of_nat n0)
    | Fallback ->
      append
        ('b'::('t'::('_'::('f'::('a'::('l'::('l'::('b'::('a'::('c'::('k'::('_'::[]))))))))))))
        (string_of_nat n0)
    | Parallel t ->
      append
        (append
          ('b'::('t'::('_'::('p'::('a'::('r'::('a'::('l'::('l'::('e'::('l'::[])))))))))))
          (string_of_nat t)) (append ('_'::[]) (string_of_nat n0))

  (** val decName : decKind -> char list **)

  let decName = function
  | Not -> 'b'::('t'::('_'::('n'::('o'::('t'::[])))))
  | IsRunning ->
    'b'::('t'::('_'::('i'::('s'::('_'::('r'::('u'::('n'::('n'::('i'::('n'::('g'::[]))))))))))))

  (** val addmod : btree -> modtype set -> modtype set **)

  let rec addmod t s =
    match t with
    | Skill _ -> set_add modtype_dec Skmod s
    | TRUE -> set_add modtype_dec TRUEmod s
    | Node (k, _, f) ->
      let l = len f in
      addmod_f f
        (set_add modtype_dec
          (match k with
           | Sequence -> Seqmod l
           | Fallback -> Fbmod l
           | Parallel n0 -> Parmod (n0, l)) s)
    | Dec (k, _, t') ->
      addmod t'
        (set_add modtype_dec
          (match k with
           | Not -> Notmod
           | IsRunning -> Runmod) s)

  (** val addmod_f : btforest -> modtype set -> modtype set **)

  and addmod_f f s =
    match f with
    | Child t -> addmod t s
    | Add (t1, rest) -> addmod_f rest (addmod t1 s)

  (** val mk_param_list : int -> char list list **)

  let rec mk_param_list l =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> [])
      (fun p ->
      (append ('b'::('t'::[])) (string_of_nat l)) :: (mk_param_list p))
      l

  (** val mk_seq_invar : int -> asslist **)

  let rec mk_seq_invar l =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> LastA (Invar ((Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))), (BConst
      SmvF))))
      (fun p ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> LastA (Invar ((Mod (('b'::('t'::('1'::[]))), (Id
        ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Equal ((Qual (Mod
        (('b'::('t'::('2'::[]))), (Id
        ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
        ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))))))
        (fun _ -> AddA ((Invar ((Mod
        ((append ('b'::('t'::[])) (string_of_nat (succ p))), (Id
        ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Equal ((Qual (Mod
        ((append ('b'::('t'::[])) (string_of_nat (succ (succ p)))), (Id
        ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
        ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))))),
        (mk_seq_invar p)))
        p)
      l

  (** val mk_seq_trans : int -> scexp **)

  let rec mk_seq_trans l =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Cexp ((BConst SmvT), (BConst SmvT)))
      (fun p ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Cexp ((BConst SmvT), (Qual (Mod (('b'::('t'::('1'::[]))),
        (Id ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))
        (fun _ -> AddCexp ((Or ((Equal ((Qual (Mod
        ((append ('b'::('t'::[])) (string_of_nat l)), (Id
        ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
        ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))))), (Equal ((Qual
        (Mod ((append ('b'::('t'::[])) (string_of_nat l)), (Id
        ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
        ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))), (Qual (Mod
        ((append ('b'::('t'::[])) (string_of_nat l)), (Id
        ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (mk_seq_trans p)))
        p)
      l

  (** val make_sequence : int -> smv_module **)

  let make_sequence l =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> bp_TRUE)
      (fun p ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> bp_identity (nodeName Sequence (succ 0)))
        (fun _ -> { name = (nodeName Sequence l); params = (mk_param_list l);
        vars = (Some (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))),
        (TSimp TBool)))); ivars = None; defs = (Some (LastD
        (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case
        (mk_seq_trans l))))); assigns = (Some (AddA ((Invar ((Mod
        ((append ('b'::('t'::[])) (string_of_nat l)), (Id
        ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
        ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))),
        (mk_seq_invar p)))) })
        p)
      l

  (** val mk_fb_invar : int -> asslist **)

  let rec mk_fb_invar l =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> LastA (Invar ((Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))), (BConst
      SmvF))))
      (fun p ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> LastA (Invar ((Mod (('b'::('t'::('1'::[]))), (Id
        ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Equal ((Qual (Mod
        (('b'::('t'::('2'::[]))), (Id
        ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
        ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))))
        (fun _ -> AddA ((Invar ((Mod
        ((append ('b'::('t'::[])) (string_of_nat (succ p))), (Id
        ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Equal ((Qual (Mod
        ((append ('b'::('t'::[])) (string_of_nat (succ (succ p)))), (Id
        ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
        ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))), (mk_fb_invar p)))
        p)
      l

  (** val mk_fb_trans : int -> scexp **)

  let rec mk_fb_trans l =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Cexp ((BConst SmvT), (BConst SmvT)))
      (fun p ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Cexp ((BConst SmvT), (Qual (Mod (('b'::('t'::('1'::[]))),
        (Id ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))
        (fun _ -> AddCexp ((Or ((Equal ((Qual (Mod
        ((append ('b'::('t'::[])) (string_of_nat l)), (Id
        ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
        ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))))), (Equal ((Qual
        (Mod ((append ('b'::('t'::[])) (string_of_nat l)), (Id
        ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
        ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))))),
        (Qual (Mod ((append ('b'::('t'::[])) (string_of_nat l)), (Id
        ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (mk_fb_trans p)))
        p)
      l

  (** val make_fallback : int -> smv_module **)

  let make_fallback l =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> bp_TRUE)
      (fun p ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> bp_identity (nodeName Fallback (succ 0)))
        (fun _ -> { name = (nodeName Fallback l); params = (mk_param_list l);
        vars = (Some (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))),
        (TSimp TBool)))); ivars = None; defs = (Some (LastD
        (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case
        (mk_fb_trans l))))); assigns = (Some (AddA ((Invar ((Mod
        ((append ('b'::('t'::[])) (string_of_nat l)), (Id
        ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
        ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))),
        (mk_fb_invar p)))) })
        p)
      l

  (** val mk_par_invar : int -> asslist **)

  let rec mk_par_invar l =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> LastA (Invar ((Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))), (BConst
      SmvF))))
      (fun p ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> LastA (Invar ((Mod (('b'::('t'::('1'::[]))), (Id
        ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
        ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))))
        (fun _ -> AddA ((Invar ((Mod
        ((append ('b'::('t'::[])) (string_of_nat (succ p))), (Id
        ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
        ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))), (mk_par_invar p)))
        p)
      l

  (** val mk_countlist : int -> char list -> sexplist **)

  let rec mk_countlist l res =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> Sexp (BConst SmvF))
      (fun p ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> Sexp (Equal ((Qual (Mod
        ((append ('b'::('t'::[])) (string_of_nat l)), (Id
        ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
        res))))
        (fun _ -> AddSexp ((Equal ((Qual (Mod
        ((append ('b'::('t'::[])) (string_of_nat l)), (Id
        ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst res))),
        (mk_countlist p res)))
        p)
      l

  (** val make_parallel : int -> int -> smv_module **)

  let make_parallel n0 l =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> bp_TRUE)
      (fun p ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ ->
        if Nat.eqb n0 0
        then { name =
               ('p'::('a'::('r'::('a'::('l'::('l'::('e'::('l'::('_'::('0'::('_'::('1'::[]))))))))))));
               params = (('b'::('t'::[])) :: []); vars = (Some (LastV
               (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp
               TBool)))); ivars = None; defs = (Some (LastD
               (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (SConst
               ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))));
               assigns = (Some (LastA (Invar ((Mod (('b'::('t'::[])), (Id
               ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
               ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))))) }
        else bp_identity (nodeName (Parallel (succ 0)) (succ 0)))
        (fun _ -> { name = (nodeName (Parallel n0) l); params =
        (mk_param_list l); vars = (Some (LastV
        (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp TBool))));
        ivars = None; defs = (Some (AddD
        (('t'::('r'::('u'::('e'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))),
        (Count
        (mk_countlist l
          ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[]))))))))))),
        (AddD
        (('f'::('a'::('i'::('l'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))),
        (Count
        (mk_countlist l ('f'::('a'::('i'::('l'::('e'::('d'::[])))))))),
        (LastD (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case (AddCexp
        ((Less ((SConst (string_of_nat n0)), (Sum ((Qual (Id
        ('t'::('r'::('u'::('e'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))))),
        (SConst ('1'::[])))))), (SConst
        ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))),
        (AddCexp ((Less ((SConst (string_of_nat l)), (Sum ((Qual (Id
        ('f'::('a'::('i'::('l'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))))),
        (SConst (string_of_nat n0)))))), (SConst
        ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))), (Cexp ((BConst SmvT),
        (SConst
        ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[]))))))))))))))))))))));
        assigns = (Some (mk_par_invar (succ p))) })
        p)
      l

  (** val make_mod : modtype -> smv_module **)

  let make_mod = function
  | Skmod -> bp_skill
  | TRUEmod -> bp_TRUE
  | Seqmod l -> make_sequence l
  | Fbmod l -> make_fallback l
  | Parmod (n0, l) -> make_parallel n0 l
  | Notmod -> bp_not
  | Runmod -> bp_isRunning

  (** val make_mod_list : modtype list -> smv_module list **)

  let rec make_mod_list = function
  | [] -> []
  | m :: rest -> (make_mod m) :: (make_mod_list rest)

  (** val make_paramlist : btforest -> param_list **)

  let rec make_paramlist = function
  | Child t -> LastP (Simple (Qual (Id (rootName t))))
  | Add (t1, rest) ->
    AddP ((Simple (Qual (Id (rootName t1)))), (make_paramlist rest))

  (** val make_vars : btree -> varlist **)

  let rec make_vars = function
  | Skill s ->
    LastV ((X.skillName s), (TComp (TMod
      ('b'::('t'::('_'::('s'::('k'::('i'::('l'::('l'::[])))))))))))
  | TRUE ->
    LastV (('t'::[]), (TComp (TMod
      ('b'::('t'::('_'::('T'::('R'::('U'::('E'::[]))))))))))
  | Node (k, name0, f) ->
    let params0 = make_paramlist f in
    let vars0 = make_vars_f f in
    AddV (name0, (TComp (TModPar ((nodeName k (len f)), params0))), vars0)
  | Dec (d, name0, t0) ->
    let vars0 = make_vars t0 in
    AddV (name0, (TComp (TModPar ((decName d), (LastP (Simple (Qual (Id
    (rootName t0)))))))), vars0)

  (** val make_vars_f : btforest -> varlist **)

  and make_vars_f = function
  | Child t -> make_vars t
  | Add (t1, rest) -> varlist_app (make_vars t1) (make_vars_f rest)

  (** val make_main : btree -> smv_module **)

  let make_main t =
    let vars0 = make_vars t in
    { name = ('b'::('t'::('_'::('m'::('a'::('i'::('n'::[]))))))); params =
    []; vars = (Some (AddV
    (('t'::('i'::('c'::('k'::('_'::('g'::('e'::('n'::('e'::('r'::('a'::('t'::('o'::('r'::[])))))))))))))),
    (TComp (TModPar
    (('b'::('t'::('_'::('t'::('i'::('c'::('k'::('_'::('g'::('e'::('n'::('e'::('r'::('a'::('t'::('o'::('r'::[]))))))))))))))))),
    (LastP (Simple (Qual (Id (rootName t)))))))), vars0))); ivars = None;
    defs = None; assigns = None }

  (** val mkop : X.skillSet list -> char list list **)

  let rec mkop = function
  | [] -> []
  | s :: rest ->
    (append ('f'::('r'::('o'::('m'::('_'::[]))))) (X.skillName s)) :: 
      (mkop rest)

  (** val mkov : X.skillSet list -> varlist **)

  let rec mkov = function
  | [] ->
    LastV
      (('b'::('t'::('_'::('m'::('a'::('i'::('n'::('_'::('i'::('n'::('s'::('t'::[])))))))))))),
      (TComp (TMod ('b'::('t'::('_'::('m'::('a'::('i'::('n'::[]))))))))))
  | s :: rest ->
    AddV ((append ('t'::('o'::('_'::[]))) (X.skillName s)), (TSimp
      bt_action_type), (mkov rest))

  (** val mkot : X.skillSet list -> asslist **)

  let rec mkot = function
  | [] ->
    LastA (Invar ((Id
      ('b'::('t'::('_'::('m'::('a'::('i'::('n'::('_'::('i'::('n'::('s'::('t'::[]))))))))))))),
      (BConst SmvF)))
  | s :: rest ->
    (match rest with
     | [] ->
       AddA ((Invar ((Mod
         (('b'::('t'::('_'::('m'::('a'::('i'::('n'::('_'::('i'::('n'::('s'::('t'::[])))))))))))),
         (Mod ((X.skillName s), (Id
         ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))), (Qual (Id
         (append ('f'::('r'::('o'::('m'::('_'::[]))))) (X.skillName s)))))),
         (LastA (Invar ((Id
         (append ('t'::('o'::('_'::[]))) (X.skillName s))), (Case (AddCexp
         ((Equal ((Qual (Mod
         (('b'::('t'::('_'::('m'::('a'::('i'::('n'::('_'::('i'::('n'::('s'::('t'::[])))))))))))),
         (Mod ((X.skillName s), (Id
         ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))))), (BConst SmvT))),
         (SConst ('E'::('n'::('a'::('b'::('l'::('e'::[]))))))), (Cexp ((Equal
         ((Qual (Mod
         (('b'::('t'::('_'::('m'::('a'::('i'::('n'::('_'::('i'::('n'::('s'::('t'::[])))))))))))),
         (Mod ((X.skillName s), (Id
         ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))))), (BConst SmvF))),
         (SConst ('R'::('e'::('s'::('e'::('t'::[])))))))))))))))
     | _ :: _ ->
       AddA ((Invar ((Mod
         (('b'::('t'::('_'::('m'::('a'::('i'::('n'::('_'::('i'::('n'::('s'::('t'::[])))))))))))),
         (Mod ((X.skillName s), (Id
         ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))), (Qual (Id
         (append ('f'::('r'::('o'::('m'::('_'::[]))))) (X.skillName s)))))),
         (AddA ((Invar ((Id
         (append ('t'::('o'::('_'::[]))) (X.skillName s))), (Case (AddCexp
         ((Equal ((Qual (Mod
         (('b'::('t'::('_'::('m'::('a'::('i'::('n'::('_'::('i'::('n'::('s'::('t'::[])))))))))))),
         (Mod ((X.skillName s), (Id
         ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))))), (BConst SmvT))),
         (SConst ('E'::('n'::('a'::('b'::('l'::('e'::[]))))))), (Cexp ((Equal
         ((Qual (Mod
         (('b'::('t'::('_'::('m'::('a'::('i'::('n'::('_'::('i'::('n'::('s'::('t'::[])))))))))))),
         (Mod ((X.skillName s), (Id
         ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))))), (BConst SmvF))),
         (SConst ('R'::('e'::('s'::('e'::('t'::[]))))))))))))), (mkot rest)))))

  (** val ocra_bt_fsm : btree -> smv_module **)

  let ocra_bt_fsm t =
    { name = ('B'::('T'::('_'::('F'::('S'::('M'::[])))))); params =
      (mkop (sklist t)); vars = (Some (mkov (sklist t))); ivars = None;
      defs = None; assigns = (Some (mkot (sklist t))) }

  (** val mkparomain : X.skillSet list -> param_list **)

  let rec mkparomain = function
  | [] -> LastP (Simple (Qual (Id [])))
  | s :: rest ->
    (match rest with
     | [] ->
       LastP (Simple (Qual (Id
         (append ('f'::('r'::('o'::('m'::('_'::[]))))) (X.skillName s)))))
     | _ :: _ ->
       AddP ((Simple (Qual (Id
         (append ('f'::('r'::('o'::('m'::('_'::[]))))) (X.skillName s))))),
         (mkparomain rest)))

  (** val mkvaromain : X.skillSet list -> varlist **)

  let rec mkvaromain = function
  | [] -> LastV ([], (TSimp bt_output_type))
  | s :: rest ->
    (match rest with
     | [] ->
       LastV ((append ('f'::('r'::('o'::('m'::('_'::[]))))) (X.skillName s)),
         (TSimp bt_output_type))
     | _ :: _ ->
       AddV ((append ('f'::('r'::('o'::('m'::('_'::[]))))) (X.skillName s)),
         (TSimp bt_output_type), (mkvaromain rest)))

  (** val mkdefomain : X.skillSet list -> deflist **)

  let rec mkdefomain = function
  | [] -> LastD ([], (Qual (Id [])))
  | s :: rest ->
    (match rest with
     | [] ->
       LastD ((append ('t'::('o'::('_'::[]))) (X.skillName s)), (Qual (Mod
         (('B'::('T'::('_'::('F'::('S'::('M'::('_'::('i'::('n'::('s'::('t'::[]))))))))))),
         (Id (append ('t'::('o'::('_'::[]))) (X.skillName s)))))))
     | _ :: _ ->
       AddD ((append ('t'::('o'::('_'::[]))) (X.skillName s)), (Qual (Mod
         (('B'::('T'::('_'::('F'::('S'::('M'::('_'::('i'::('n'::('s'::('t'::[]))))))))))),
         (Id (append ('t'::('o'::('_'::[]))) (X.skillName s)))))),
         (mkdefomain rest)))

  (** val ocra_main : btree -> smv_module **)

  let ocra_main t =
    { name = ('m'::('a'::('i'::('n'::[])))); params = []; vars = (Some (AddV
      (('B'::('T'::('_'::('F'::('S'::('M'::('_'::('i'::('n'::('s'::('t'::[]))))))))))),
      (TComp (TModPar (('B'::('T'::('_'::('F'::('S'::('M'::[])))))),
      (mkparomain (sklist t))))), (mkvaromain (sklist t))))); ivars = None;
      defs = (Some (mkdefomain (sklist t))); assigns = None }

  (** val make_spec : btree -> smv_module list **)

  let make_spec t =
    let needed = addmod t empty_set in
    let modlist = make_mod_list needed in
    app modlist
      (bp_tick_generator :: ((make_main t) :: ((ocra_bt_fsm t) :: ((ocra_main
                                                                    t) :: []))))
 end
