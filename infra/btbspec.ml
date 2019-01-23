
(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | [] -> m
  | a :: l1 -> a :: (app l1 m)

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

type simp_type_spec =
| TBool
| TEnum of symbolic_constant list

type param_list =
| LastP of sexp
| AddP of sexp * param_list

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
| Next of qualid * sexp

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
  | AddV (v, t, rest) -> AddV (v, t, (varlist_app rest b))

(** val varlist_rev : varlist -> varlist **)

let rec varlist_rev = function
| LastV (v, t) -> LastV (v, t)
| AddV (v, t, rest) -> varlist_app (varlist_rev rest) (LastV (v, t))

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

(** val translate_simp_type_spec : simp_type_spec -> char list **)

let translate_simp_type_spec = function
| TBool -> 'b'::('o'::('o'::('l'::('e'::('a'::('n'::[]))))))
| TEnum values ->
  append ('{'::(' '::[]))
    (append (concat (','::(' '::[])) values) (' '::('}'::[])))

(** val translate_param_list : param_list -> char list **)

let rec translate_param_list = function
| LastP e -> translate_sexp e
| AddP (e, pl') ->
  append (translate_sexp e)
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
        (append (translate_sexp ne) (append (';'::[]) newline))))

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

(** val set_union : ('a1 -> 'a1 -> bool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_union aeq_dec x = function
| [] -> x
| a1 :: y1 -> set_add aeq_dec a1 (set_union aeq_dec x y1)

(** val bt_input_type : simp_type_spec **)

let bt_input_type =
  TEnum
    (('R'::('u'::('n'::('n'::[])))) :: (('F'::('a'::('i'::('l'::[])))) :: (('S'::('u'::('c'::('c'::[])))) :: [])))

(** val bt_output_type : simp_type_spec **)

let bt_output_type =
  TEnum
    (('n'::('o'::('n'::('e'::[])))) :: (('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[])))))))) :: (('r'::('u'::('n'::('n'::('i'::('n'::('g'::[]))))))) :: (('f'::('a'::('i'::('l'::('e'::('d'::[])))))) :: (('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[]))))))))) :: [])))))

(** val bt_action_type : simp_type_spec **)

let bt_action_type =
  TEnum
    (('n'::('o'::[])) :: (('e'::('n'::('a'::('b'::('l'::('e'::[])))))) :: (('d'::('i'::('s'::('a'::('b'::('l'::('e'::[]))))))) :: [])))

(** val bt_seq_state : simp_type_spec **)

let bt_seq_state =
  TEnum
    (('i'::('n'::('i'::('t'::('i'::('a'::('l'::[]))))))) :: (('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[]))))))))))))) :: (('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))) :: (('r'::('e'::('t'::('u'::('r'::('n'::('_'::('l'::('e'::('f'::('t'::[]))))))))))) :: (('r'::('e'::('t'::('u'::('r'::('n'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))) :: (('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))) :: (('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))))) :: [])))))))

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
    (Id ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Neg (Equal ((Qual
    (Mod
    (('t'::('o'::('p'::('_'::('l'::('e'::('v'::('e'::('l'::('_'::('b'::('t'::[])))))))))))),
    (Id ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
    ('n'::('o'::('n'::('e'::[])))))))))))))) }

(** val bp_skill_autonomous : smv_module **)

let bp_skill_autonomous =
  { name = ('b'::('t'::('_'::('s'::('k'::('i'::('l'::('l'::[]))))))));
    params = []; vars = (Some (AddV
    (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (TSimp bt_output_type),
    (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp TBool))))));
    ivars = (Some (LastI (('i'::('n'::('p'::('u'::('t'::[]))))),
    bt_input_type))); defs = None; assigns = (Some (AddA ((Init ((Id
    ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))), (SConst
    ('n'::('o'::('n'::('e'::[]))))))), (LastA (Next ((Id
    ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))), (Case (AddCexp ((Neg (Qual
    (Id ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (SConst
    ('n'::('o'::('n'::('e'::[]))))), (AddCexp ((Equal ((Qual (Id
    ('i'::('n'::('p'::('u'::('t'::[]))))))), (SConst
    ('R'::('u'::('n'::('n'::[]))))))), (SConst
    ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))), (AddCexp ((Equal
    ((Qual (Id ('i'::('n'::('p'::('u'::('t'::[]))))))), (SConst
    ('F'::('a'::('i'::('l'::[]))))))), (SConst
    ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))), (Cexp ((Equal ((Qual (Id
    ('i'::('n'::('p'::('u'::('t'::[]))))))), (SConst
    ('S'::('u'::('c'::('c'::[]))))))), (SConst
    ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[]))))))))))))))))))))))))) }

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

module BT_bin_spec =
 functor (X:BT_SIG) ->
 struct
  type nodeKind =
  | Sequence
  | Fallback
  | Parallel1
  | Parallel2

  (** val nodeKind_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> nodeKind -> 'a1 **)

  let nodeKind_rect f f0 f1 f2 = function
  | Sequence -> f
  | Fallback -> f0
  | Parallel1 -> f1
  | Parallel2 -> f2

  (** val nodeKind_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> nodeKind -> 'a1 **)

  let nodeKind_rec f f0 f1 f2 = function
  | Sequence -> f
  | Fallback -> f0
  | Parallel1 -> f1
  | Parallel2 -> f2

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
  | Node of nodeKind * char list * btree * btree
  | Dec of decKind * char list * btree

  (** val btree_rect :
      (X.skillSet -> 'a1) -> 'a1 -> (nodeKind -> char list -> btree -> 'a1 ->
      btree -> 'a1 -> 'a1) -> (decKind -> char list -> btree -> 'a1 -> 'a1)
      -> btree -> 'a1 **)

  let rec btree_rect f f0 f1 f2 = function
  | Skill s -> f s
  | TRUE -> f0
  | Node (n, s, b0, b1) ->
    f1 n s b0 (btree_rect f f0 f1 f2 b0) b1 (btree_rect f f0 f1 f2 b1)
  | Dec (d, s, b0) -> f2 d s b0 (btree_rect f f0 f1 f2 b0)

  (** val btree_rec :
      (X.skillSet -> 'a1) -> 'a1 -> (nodeKind -> char list -> btree -> 'a1 ->
      btree -> 'a1 -> 'a1) -> (decKind -> char list -> btree -> 'a1 -> 'a1)
      -> btree -> 'a1 **)

  let rec btree_rec f f0 f1 f2 = function
  | Skill s -> f s
  | TRUE -> f0
  | Node (n, s, b0, b1) ->
    f1 n s b0 (btree_rec f f0 f1 f2 b0) b1 (btree_rec f f0 f1 f2 b1)
  | Dec (d, s, b0) -> f2 d s b0 (btree_rec f f0 f1 f2 b0)

  (** val sklist : btree -> X.skillSet list **)

  let rec sklist = function
  | Skill s -> s :: []
  | TRUE -> []
  | Node (_, _, t1, t2) -> app (sklist t1) (sklist t2)
  | Dec (_, _, t0) -> sklist t0

  type modtype =
  | Skmod
  | TRUEmod
  | Seqmod
  | Fbmod
  | Par1mod
  | Par2mod
  | Notmod
  | Runmod

  (** val modtype_rect :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> modtype -> 'a1 **)

  let modtype_rect f f0 f1 f2 f3 f4 f5 f6 = function
  | Skmod -> f
  | TRUEmod -> f0
  | Seqmod -> f1
  | Fbmod -> f2
  | Par1mod -> f3
  | Par2mod -> f4
  | Notmod -> f5
  | Runmod -> f6

  (** val modtype_rec :
      'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> modtype -> 'a1 **)

  let modtype_rec f f0 f1 f2 f3 f4 f5 f6 = function
  | Skmod -> f
  | TRUEmod -> f0
  | Seqmod -> f1
  | Fbmod -> f2
  | Par1mod -> f3
  | Par2mod -> f4
  | Notmod -> f5
  | Runmod -> f6

  (** val modtype_dec : modtype -> modtype -> bool **)

  let modtype_dec x y =
    match x with
    | Skmod -> (match y with
                | Skmod -> true
                | _ -> false)
    | TRUEmod -> (match y with
                  | TRUEmod -> true
                  | _ -> false)
    | Seqmod -> (match y with
                 | Seqmod -> true
                 | _ -> false)
    | Fbmod -> (match y with
                | Fbmod -> true
                | _ -> false)
    | Par1mod -> (match y with
                  | Par1mod -> true
                  | _ -> false)
    | Par2mod -> (match y with
                  | Par2mod -> true
                  | _ -> false)
    | Notmod -> (match y with
                 | Notmod -> true
                 | _ -> false)
    | Runmod -> (match y with
                 | Runmod -> true
                 | _ -> false)

  (** val rootName : btree -> char list **)

  let rootName = function
  | Skill s -> X.skillName s
  | TRUE -> 'B'::('T'::('S'::('u'::('c'::('c'::[])))))
  | Node (_, n, _, _) -> n
  | Dec (_, n, _) -> n

  (** val nodeName : nodeKind -> char list **)

  let nodeName = function
  | Sequence ->
    'S'::('E'::('Q'::('U'::('E'::('N'::('C'::('E'::('_'::('N'::('O'::('D'::('E'::[]))))))))))))
  | Fallback ->
    'F'::('A'::('L'::('L'::('B'::('A'::('C'::('K'::('_'::('N'::('O'::('D'::('E'::[]))))))))))))
  | Parallel1 ->
    'P'::('A'::('R'::('A'::('L'::('L'::('E'::('L'::('1'::('_'::('N'::('O'::('D'::('E'::[])))))))))))))
  | Parallel2 ->
    'P'::('A'::('R'::('A'::('L'::('L'::('E'::('L'::('2'::('_'::('N'::('O'::('D'::('E'::[])))))))))))))

  (** val decName : decKind -> char list **)

  let decName = function
  | Not -> 'N'::('O'::('T'::('_'::('N'::('O'::('D'::('E'::[])))))))
  | IsRunning ->
    'I'::('S'::('R'::('U'::('N'::('N'::('I'::('N'::('G'::('_'::('N'::('O'::('D'::('E'::[])))))))))))))

  (** val bp_bin_seq : smv_module **)

  let bp_bin_seq =
    { name = (nodeName Sequence); params =
      (('v'::('i'::('s'::('i'::('t'::[]))))) :: (('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))) :: (('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))) :: [])));
      vars = (Some (AddV
      (('t'::('o'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))),
      (TSimp bt_action_type), (AddV
      (('t'::('o'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))),
      (TSimp bt_action_type), (AddV
      (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (TSimp bt_output_type),
      (AddV
      (('c'::('a'::('c'::('h'::('e'::('d'::('_'::('l'::('e'::('f'::('t'::[]))))))))))),
      (TSimp bt_output_type), (LastV (('s'::('t'::('a'::('t'::('e'::[]))))),
      (TSimp bt_seq_state)))))))))))); ivars = None; defs = None; assigns =
      (Some (AddA ((Init ((Id
      ('t'::('o'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))))))),
      (SConst ('n'::('o'::[]))))), (AddA ((Init ((Id
      ('t'::('o'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))))))),
      (SConst ('n'::('o'::[]))))), (AddA ((Init ((Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))), (SConst
      ('n'::('o'::('n'::('e'::[]))))))), (AddA ((Init ((Id
      ('c'::('a'::('c'::('h'::('e'::('d'::('_'::('l'::('e'::('f'::('t'::[])))))))))))),
      (SConst ('n'::('o'::('n'::('e'::[]))))))), (AddA ((Init ((Id
      ('s'::('t'::('a'::('t'::('e'::[])))))), (SConst
      ('i'::('n'::('i'::('t'::('i'::('a'::('l'::[])))))))))), (AddA ((Next
      ((Id
      ('t'::('o'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))))))),
      (Case (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('i'::('n'::('i'::('t'::('i'::('a'::('l'::[])))))))))), (Equal ((Qual
      (Id ('v'::('i'::('s'::('i'::('t'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))), (AddCexp ((And ((Equal
      ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('i'::('n'::('i'::('t'::('i'::('a'::('l'::[])))))))))), (Equal ((Qual
      (Id ('v'::('i'::('s'::('i'::('t'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::[])))))))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::[])))))))), (AddCexp ((And
      ((Equal ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('n'::('o'::('n'::('e'::[]))))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))), (AddCexp ((And ((Equal
      ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[]))))))))))))))))),
      (Neg (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[])))))))))))))),
      (SConst ('d'::('i'::('s'::('a'::('b'::('l'::('e'::[])))))))), (Cexp
      ((BConst SmvT), (SConst ('n'::('o'::[])))))))))))))))), (AddA ((Next
      ((Id
      ('t'::('o'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))))))),
      (Case (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))))),
      (SConst ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))), (AddCexp ((And
      ((Equal ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))))),
      (Paren (Or ((Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))))), (Equal
      ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('f'::('a'::('i'::('l'::('e'::('d'::[])))))))))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::[])))))))), (AddCexp ((And
      ((Equal ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('n'::('o'::('n'::('e'::[]))))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))), (AddCexp ((And ((Equal
      ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))))),
      (Neg (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[])))))))))))))),
      (SConst ('d'::('i'::('s'::('a'::('b'::('l'::('e'::[])))))))), (Cexp
      ((BConst SmvT), (SConst ('n'::('o'::[])))))))))))))))), (AddA ((Next
      ((Id ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))), (Case (AddCexp
      ((And ((Equal ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))),
      (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))))))),
      (Neg (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst ('n'::('o'::('n'::('e'::[])))))))))), (SConst
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[]))))))))))))),
      (SConst
      ('c'::('a'::('c'::('h'::('e'::('d'::('_'::('l'::('e'::('f'::('t'::[])))))))))))),
      (Cexp ((BConst SmvT), (SConst ('n'::('o'::('n'::('e'::[])))))))))))))),
      (AddA ((Next ((Id
      ('c'::('a'::('c'::('h'::('e'::('d'::('_'::('l'::('e'::('f'::('t'::[])))))))))))),
      (Case (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))))),
      (Paren (Or ((Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))))), (Equal
      ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('f'::('a'::('i'::('l'::('e'::('d'::[])))))))))))))), (SConst
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[]))))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[]))))))))))))),
      (SConst
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))))),
      (Neg (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[])))))))))))))),
      (SConst
      ('c'::('a'::('c'::('h'::('e'::('d'::('_'::('l'::('e'::('f'::('t'::[])))))))))))),
      (Cexp ((BConst SmvT), (SConst
      ('n'::('o'::('n'::('e'::[])))))))))))))))), (LastA (Next ((Id
      ('s'::('t'::('a'::('t'::('e'::[])))))), (Case (AddCexp ((And ((Equal
      ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('i'::('n'::('i'::('t'::('i'::('a'::('l'::[])))))))))), (Equal ((Qual
      (Id ('v'::('i'::('s'::('i'::('t'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('i'::('n'::('i'::('t'::('i'::('a'::('l'::[])))))))))), (Equal ((Qual
      (Id ('v'::('i'::('s'::('i'::('t'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::[])))))))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[]))))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))))),
      (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('n'::('o'::('n'::('e'::[]))))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))))),
      (Paren (Or ((Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))))), (Equal
      ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('f'::('a'::('i'::('l'::('e'::('d'::[])))))))))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst ('n'::('o'::('n'::('e'::[]))))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))))))),
      (Neg (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst ('n'::('o'::('n'::('e'::[])))))))))), (SConst
      ('r'::('e'::('t'::('u'::('r'::('n'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))))),
      (Neg (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[])))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[]))))))))))))),
      (SConst
      ('r'::('e'::('t'::('u'::('r'::('n'::('_'::('l'::('e'::('f'::('t'::[])))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[]))))))))))))))))),
      (Neg (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[])))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[]))))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[]))))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[]))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))),
      (Cexp ((BConst SmvT), (SConst
      ('i'::('n'::('i'::('t'::('i'::('a'::('l'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))) }

  (** val bp_bin_fb : smv_module **)

  let bp_bin_fb =
    { name = (nodeName Fallback); params =
      (('v'::('i'::('s'::('i'::('t'::[]))))) :: (('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))) :: (('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))) :: [])));
      vars = (Some (AddV
      (('t'::('o'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))),
      (TSimp bt_action_type), (AddV
      (('t'::('o'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))),
      (TSimp bt_action_type), (AddV
      (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (TSimp bt_output_type),
      (AddV
      (('c'::('a'::('c'::('h'::('e'::('d'::('_'::('l'::('e'::('f'::('t'::[]))))))))))),
      (TSimp bt_output_type), (LastV (('s'::('t'::('a'::('t'::('e'::[]))))),
      (TSimp bt_seq_state)))))))))))); ivars = None; defs = None; assigns =
      (Some (AddA ((Init ((Id
      ('t'::('o'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))))))),
      (SConst ('n'::('o'::[]))))), (AddA ((Init ((Id
      ('t'::('o'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))))))),
      (SConst ('n'::('o'::[]))))), (AddA ((Init ((Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))), (SConst
      ('n'::('o'::('n'::('e'::[]))))))), (AddA ((Init ((Id
      ('c'::('a'::('c'::('h'::('e'::('d'::('_'::('l'::('e'::('f'::('t'::[])))))))))))),
      (SConst ('n'::('o'::('n'::('e'::[]))))))), (AddA ((Init ((Id
      ('s'::('t'::('a'::('t'::('e'::[])))))), (SConst
      ('i'::('n'::('i'::('t'::('i'::('a'::('l'::[])))))))))), (AddA ((Next
      ((Id
      ('t'::('o'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))))))),
      (Case (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('i'::('n'::('i'::('t'::('i'::('a'::('l'::[])))))))))), (Equal ((Qual
      (Id ('v'::('i'::('s'::('i'::('t'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))), (AddCexp ((And ((Equal
      ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('i'::('n'::('i'::('t'::('i'::('a'::('l'::[])))))))))), (Equal ((Qual
      (Id ('v'::('i'::('s'::('i'::('t'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::[])))))))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::[])))))))), (AddCexp ((And
      ((Equal ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('n'::('o'::('n'::('e'::[]))))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))), (AddCexp ((And ((Equal
      ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[]))))))))))))))))),
      (Neg (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[])))))))))))))),
      (SConst ('d'::('i'::('s'::('a'::('b'::('l'::('e'::[])))))))), (Cexp
      ((BConst SmvT), (SConst ('n'::('o'::[])))))))))))))))), (AddA ((Next
      ((Id
      ('t'::('o'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))))))),
      (Case (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))), (AddCexp ((And ((Equal
      ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))))),
      (Paren (Or ((Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))))), (Equal
      ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[]))))))))))))))))),
      (SConst ('d'::('i'::('s'::('a'::('b'::('l'::('e'::[])))))))), (AddCexp
      ((And ((Equal ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))),
      (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst ('n'::('o'::('n'::('e'::[]))))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))), (AddCexp ((And ((Equal
      ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))))),
      (Neg (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[])))))))))))))),
      (SConst ('d'::('i'::('s'::('a'::('b'::('l'::('e'::[])))))))), (Cexp
      ((BConst SmvT), (SConst ('n'::('o'::[])))))))))))))))), (AddA ((Next
      ((Id ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))), (Case (AddCexp
      ((And ((Equal ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))),
      (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))))))),
      (Neg (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst ('n'::('o'::('n'::('e'::[])))))))))), (SConst
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[]))))))))))))),
      (SConst
      ('c'::('a'::('c'::('h'::('e'::('d'::('_'::('l'::('e'::('f'::('t'::[])))))))))))),
      (Cexp ((BConst SmvT), (SConst ('n'::('o'::('n'::('e'::[])))))))))))))),
      (AddA ((Next ((Id
      ('c'::('a'::('c'::('h'::('e'::('d'::('_'::('l'::('e'::('f'::('t'::[])))))))))))),
      (Case (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))))),
      (Paren (Or ((Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))))), (Equal
      ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[]))))))))))))))))),
      (SConst
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[]))))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[]))))))))))))),
      (SConst
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))))),
      (Neg (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[])))))))))))))),
      (SConst
      ('c'::('a'::('c'::('h'::('e'::('d'::('_'::('l'::('e'::('f'::('t'::[])))))))))))),
      (Cexp ((BConst SmvT), (SConst
      ('n'::('o'::('n'::('e'::[])))))))))))))))), (LastA (Next ((Id
      ('s'::('t'::('a'::('t'::('e'::[])))))), (Case (AddCexp ((And ((Equal
      ((Qual (Id ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('i'::('n'::('i'::('t'::('i'::('a'::('l'::[])))))))))), (Equal ((Qual
      (Id ('v'::('i'::('s'::('i'::('t'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('i'::('n'::('i'::('t'::('i'::('a'::('l'::[])))))))))), (Equal ((Qual
      (Id ('v'::('i'::('s'::('i'::('t'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::[])))))))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[]))))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('n'::('o'::('n'::('e'::[]))))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[])))))))))))))))),
      (Paren (Or ((Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))))), (Equal
      ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[]))))))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst ('n'::('o'::('n'::('e'::[]))))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('e'::('n'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))))))),
      (Neg (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst ('n'::('o'::('n'::('e'::[])))))))))), (SConst
      ('r'::('e'::('t'::('u'::('r'::('n'::('_'::('r'::('i'::('g'::('h'::('t'::[]))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))))),
      (Neg (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[])))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[]))))))))))))),
      (SConst
      ('r'::('e'::('t'::('u'::('r'::('n'::('_'::('l'::('e'::('f'::('t'::[])))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[]))))))))))))))))),
      (Neg (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[])))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[]))))))))))))))),
      (AddCexp ((And ((Equal ((Qual (Id
      ('s'::('t'::('a'::('t'::('e'::[]))))))), (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('l'::('e'::('f'::('t'::[]))))))))))))))))),
      (Equal ((Qual (Id
      ('f'::('r'::('o'::('m'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('e'::('d'::[]))))))))))))),
      (SConst
      ('d'::('i'::('s'::('a'::('b'::('l'::('i'::('n'::('g'::('_'::('r'::('i'::('g'::('h'::('t'::[])))))))))))))))),
      (Cexp ((BConst SmvT), (SConst
      ('i'::('n'::('i'::('t'::('i'::('a'::('l'::[]))))))))))))))))))))))))))))))))))))))))))))))))))))))) }

  (** val bp_par1 : smv_module **)

  let bp_par1 =
    { name = (nodeName Parallel1); params =
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))) :: (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))) :: []));
      vars = (Some (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))),
      (TSimp TBool)))); ivars = None; defs = (Some (AddD
      (('t'::('r'::('u'::('e'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))),
      (Count (AddSexp ((Equal ((Qual (Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))),
      (Sexp (Equal ((Qual (Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))))))),
      (AddD
      (('f'::('a'::('i'::('l'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))),
      (Count (AddSexp ((Equal ((Qual (Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))), (Sexp (Equal ((Qual
      (Mod (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))))), (LastD
      (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case (AddCexp ((Less
      ((SConst ('0'::[])), (Qual (Id
      ('t'::('r'::('u'::('e'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))))))),
      (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))),
      (AddCexp ((Less ((SConst ('1'::[])), (Qual (Id
      ('f'::('a'::('i'::('l'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))))))),
      (SConst ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))), (Cexp ((BConst
      SmvT), (SConst
      ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[]))))))))))))))))))))));
      assigns = (Some (AddA ((Invar ((Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))), (LastA (Invar ((Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))))))) }

  (** val bp_par2 : smv_module **)

  let bp_par2 =
    { name = (nodeName Parallel2); params =
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))) :: (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))) :: []));
      vars = (Some (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))),
      (TSimp TBool)))); ivars = None; defs = (Some (AddD
      (('t'::('r'::('u'::('e'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))),
      (Count (AddSexp ((Equal ((Qual (Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))),
      (Sexp (Equal ((Qual (Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))))))),
      (AddD
      (('f'::('a'::('i'::('l'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))),
      (Count (AddSexp ((Equal ((Qual (Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))), (Sexp (Equal ((Qual
      (Mod (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))))), (LastD
      (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case (AddCexp ((Less
      ((SConst ('1'::[])), (Qual (Id
      ('t'::('r'::('u'::('e'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))))))),
      (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))),
      (AddCexp ((Less ((SConst ('0'::[])), (Qual (Id
      ('f'::('a'::('i'::('l'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))))))),
      (SConst ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))), (Cexp ((BConst
      SmvT), (SConst
      ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[]))))))))))))))))))))));
      assigns = (Some (AddA ((Invar ((Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))), (LastA (Invar ((Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))))))) }

  (** val addmod : btree -> modtype set -> modtype set **)

  let rec addmod t s =
    match t with
    | Skill _ -> set_add modtype_dec Skmod s
    | TRUE -> set_add modtype_dec TRUEmod s
    | Node (k, _, t1, t2) ->
      let nodemod =
        match k with
        | Sequence -> Seqmod
        | Fallback -> Fbmod
        | Parallel1 -> Par1mod
        | Parallel2 -> Par2mod
      in
      let left_modules = addmod t1 s in
      let right_modules = addmod t2 s in
      set_add modtype_dec nodemod
        (set_union modtype_dec left_modules right_modules)
    | Dec (k, _, t') ->
      let decmod = match k with
                   | Not -> Notmod
                   | IsRunning -> Runmod in
      set_add modtype_dec decmod (addmod t' s)

  (** val make_mod : modtype -> bool -> smv_module **)

  let make_mod t aut =
    match t with
    | Skmod -> if aut then bp_skill_autonomous else bp_skill
    | TRUEmod -> bp_TRUE
    | Seqmod -> bp_bin_seq
    | Fbmod -> bp_bin_fb
    | Par1mod -> bp_par1
    | Par2mod -> bp_par2
    | Notmod -> bp_not
    | Runmod -> bp_isRunning

  (** val make_mod_list : modtype list -> bool -> smv_module list **)

  let rec make_mod_list l aut =
    match l with
    | [] -> []
    | m :: rest ->
      (match m with
       | Skmod -> make_mod_list rest aut
       | _ -> (make_mod m aut) :: (make_mod_list rest aut))

  (** val make_vars : btree -> varlist **)

  let rec make_vars = function
  | Skill s ->
    LastV ((X.skillName s), (TComp (TMod
      ('b'::('t'::('_'::('s'::('k'::('i'::('l'::('l'::[])))))))))))
  | TRUE ->
    LastV (('t'::[]), (TComp (TMod
      ('b'::('t'::('_'::('T'::('R'::('U'::('E'::[]))))))))))
  | Node (k, name0, t1, t2) ->
    let x = varlist_app (make_vars t1) (make_vars t2) in
    AddV (name0, (TComp (TModPar ((nodeName k), (AddP ((Qual (Id
    (rootName t1))), (LastP (Qual (Id (rootName t2))))))))), x)
  | Dec (d, name0, t0) ->
    let x = make_vars t0 in
    AddV (name0, (TComp (TModPar ((decName d), (LastP (Qual (Id
    (rootName t0))))))), x)

  (** val make_main : btree -> char list -> smv_module **)

  let make_main t modname =
    { name = modname; params = []; vars = (Some
      (varlist_rev (AddV
        (('t'::('i'::('c'::('k'::('_'::('g'::('e'::('n'::('e'::('r'::('a'::('t'::('o'::('r'::[])))))))))))))),
        (TComp (TModPar
        (('b'::('t'::('_'::('t'::('i'::('c'::('k'::('_'::('g'::('e'::('n'::('e'::('r'::('a'::('t'::('o'::('r'::[]))))))))))))))))),
        (LastP (Qual (Id (rootName t))))))), (make_vars t))))); ivars = None;
      defs = None; assigns = None }

  (** val make_spec : btree -> smv_module list **)

  let make_spec t =
    let needed = addmod t empty_set in
    let modlist = make_mod_list needed true in
    app modlist
      (bp_tick_generator :: ((make_main t ('m'::('a'::('i'::('n'::[]))))) :: []))

  (** val mkop : X.skillSet list -> char list list **)

  let rec mkop = function
  | [] -> []
  | s :: rest ->
    (append ('f'::('r'::('o'::('m'::('_'::[]))))) (X.skillName s)) :: 
      (mkop rest)

  (** val build_parameters : identifier -> btree -> btree -> param_list **)

  let build_parameters p t1 t2 =
    match t1 with
    | Skill s1 ->
      (match t2 with
       | Skill s2 ->
         AddP ((Qual (Id p)), (AddP ((Qual (Id
           (append ('f'::('r'::('o'::('m'::('_'::[]))))) (X.skillName s1)))),
           (LastP (Qual (Id
           (append ('f'::('r'::('o'::('m'::('_'::[]))))) (X.skillName s2))))))))
       | Node (_, n2, _, _) ->
         AddP ((Qual (Id p)), (AddP ((Qual (Id
           (append ('f'::('r'::('o'::('m'::('_'::[]))))) (X.skillName s1)))),
           (LastP (Qual (Mod (n2, (Id
           ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))
       | _ -> LastP (Qual (Id ('d'::('u'::('m'::('m'::('y'::[]))))))))
    | Node (_, n1, _, _) ->
      (match t2 with
       | Skill s2 ->
         AddP ((Qual (Id p)), (AddP ((Qual (Mod (n1, (Id
           ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (LastP (Qual (Id
           (append ('f'::('r'::('o'::('m'::('_'::[]))))) (X.skillName s2))))))))
       | Node (_, n2, _, _) ->
         AddP ((Qual (Id p)), (AddP ((Qual (Mod (n1, (Id
           ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (LastP (Qual
           (Mod (n2, (Id ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))
       | _ -> LastP (Qual (Id ('d'::('u'::('m'::('m'::('y'::[]))))))))
    | _ -> LastP (Qual (Id ('d'::('u'::('m'::('m'::('y'::[])))))))

  (** val mkov : btree -> varlist option -> identifier -> varlist option **)

  let rec mkov t l parent =
    match t with
    | Node (k, name0, t1, t2) ->
      (match k with
       | Sequence ->
         let parameters = build_parameters parent t1 t2 in
         let newlist =
           let vl_left =
             mkov t1 l
               (append name0
                 ('.'::('t'::('o'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))))))))
           in
           let vl_right =
             mkov t2 l
               (append name0
                 ('.'::('t'::('o'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))))))))
           in
           (match vl_left with
            | Some vl ->
              (match vl_right with
               | Some vl' -> Some (varlist_app vl vl')
               | None -> vl_left)
            | None -> vl_right)
         in
         (match newlist with
          | Some vl ->
            Some (AddV (name0, (TComp (TModPar ((nodeName Sequence),
              parameters))), vl))
          | None ->
            Some (LastV (name0, (TComp (TModPar ((nodeName Sequence),
              parameters))))))
       | Fallback ->
         let parameters = build_parameters parent t1 t2 in
         let newlist =
           let vl_left =
             mkov t1 l
               (append name0
                 ('.'::('t'::('o'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))))))))
           in
           let vl_right =
             mkov t2 l
               (append name0
                 ('.'::('t'::('o'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))))))))
           in
           (match vl_left with
            | Some vl ->
              (match vl_right with
               | Some vl' -> Some (varlist_app vl vl')
               | None -> vl_left)
            | None -> vl_right)
         in
         (match newlist with
          | Some vl ->
            Some (AddV (name0, (TComp (TModPar ((nodeName Fallback),
              parameters))), vl))
          | None ->
            Some (LastV (name0, (TComp (TModPar ((nodeName Fallback),
              parameters))))))
       | _ -> None)
    | Dec (_, _, _) -> None
    | _ -> l

  type direction =
  | From_left
  | From_right

  (** val direction_rect : 'a1 -> 'a1 -> direction -> 'a1 **)

  let direction_rect f f0 = function
  | From_left -> f
  | From_right -> f0

  (** val direction_rec : 'a1 -> 'a1 -> direction -> 'a1 **)

  let direction_rec f f0 = function
  | From_left -> f
  | From_right -> f0

  (** val mkod : btree -> deflist -> identifier -> direction -> deflist **)

  let rec mkod t d parent dir =
    match t with
    | Skill s ->
      AddD ((append ('t'::('o'::('_'::[]))) (X.skillName s)), (Qual (Mod
        (parent, (Id
        (match dir with
         | From_left ->
           't'::('o'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::[])))))))))
         | From_right ->
           't'::('o'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[]))))))))))))))),
        d)
    | Node (_, n, t1, t2) ->
      let dl_left = mkod t1 d n From_left in mkod t2 dl_left n From_right
    | _ -> d

  (** val ocra_bt_fsm : btree -> smv_module **)

  let ocra_bt_fsm t =
    { name = ('B'::('T'::('_'::('F'::('S'::('M'::[])))))); params =
      (('v'::('i'::('s'::('i'::('t'::[]))))) :: (mkop (sklist t))); vars =
      (mkov t None ('v'::('i'::('s'::('i'::('t'::[])))))); ivars = None;
      defs =
      (match t with
       | Node (_, n, t1, t2) ->
         let dl_left =
           mkod t1 (LastD (('o'::('u'::('t'::('p'::('u'::('t'::[])))))),
             (Qual (Mod (n, (Id
             ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))))) n From_left
         in
         let dl_tot = mkod t2 dl_left n From_right in Some dl_tot
       | _ -> None); assigns = None }

  (** val mkparomain : X.skillSet list -> param_list **)

  let rec mkparomain = function
  | [] -> LastP (Qual (Id []))
  | s :: rest ->
    (match rest with
     | [] ->
       LastP (Qual (Id
         (append ('f'::('r'::('o'::('m'::('_'::[]))))) (X.skillName s))))
     | _ :: _ ->
       AddP ((Qual (Id
         (append ('f'::('r'::('o'::('m'::('_'::[]))))) (X.skillName s)))),
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
      (TComp (TModPar (('B'::('T'::('_'::('F'::('S'::('M'::[])))))), (AddP
      ((Qual (Id ('v'::('i'::('s'::('i'::('t'::[]))))))),
      (mkparomain (sklist t))))))), (AddV
      (('v'::('i'::('s'::('i'::('t'::[]))))), (TSimp bt_action_type),
      (mkvaromain (sklist t))))))); ivars = None; defs = (Some (AddD
      (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Qual (Mod
      (('B'::('T'::('_'::('F'::('S'::('M'::('_'::('i'::('n'::('s'::('t'::[]))))))))))),
      (Id ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))),
      (mkdefomain (sklist t))))); assigns = None }

  (** val make_spec_ocra : btree -> smv_module list **)

  let make_spec_ocra t =
    let needed = addmod t empty_set in
    let modlist = make_mod_list needed false in
    app modlist ((ocra_bt_fsm t) :: ((ocra_main t) :: []))
 end
