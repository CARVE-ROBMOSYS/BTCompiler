
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

  (** val bp_bin_seq : smv_module **)

  let bp_bin_seq =
    { name =
      ('b'::('t'::('_'::('s'::('e'::('q'::('u'::('e'::('n'::('c'::('e'::[])))))))))));
      params =
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))) :: (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))) :: []));
      vars = (Some (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))),
      (TSimp TBool)))); ivars = None; defs = (Some (LastD
      (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case (AddCexp ((Equal
      ((Qual (Mod (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))),
      (Qual (Mod (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))),
      (Id ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (Cexp ((BConst
      SmvT), (Qual (Mod (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))),
      (Id ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))))))))))); assigns =
      (Some (AddA ((Invar ((Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))), (LastA (Invar ((Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Equal ((Qual (Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))))))))) }

  (** val bp_bin_fb : smv_module **)

  let bp_bin_fb =
    { name =
      ('b'::('t'::('_'::('f'::('a'::('l'::('l'::('b'::('a'::('c'::('k'::[])))))))))));
      params =
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))) :: (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))) :: []));
      vars = (Some (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))),
      (TSimp TBool)))); ivars = None; defs = (Some (LastD
      (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case (AddCexp ((Equal
      ((Qual (Mod (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))), (Qual (Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (Cexp ((BConst SmvT),
      (Qual (Mod (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))))))))))); assigns =
      (Some (AddA ((Invar ((Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))), (LastA (Invar ((Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Equal ((Qual (Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))))))) }

  (** val bp_par1 : smv_module **)

  let bp_par1 =
    { name =
      ('b'::('t'::('_'::('p'::('a'::('r'::('a'::('l'::('l'::('e'::('l'::('1'::[]))))))))))));
      params =
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
    { name =
      ('b'::('t'::('_'::('p'::('a'::('r'::('a'::('l'::('l'::('e'::('l'::('2'::[]))))))))))));
      params =
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

  (** val rootName : btree -> char list **)

  let rootName = function
  | Skill s -> X.skillName s
  | TRUE -> 'B'::('T'::('S'::('u'::('c'::('c'::[])))))
  | Node (_, n, _, _) -> n
  | Dec (_, n, _) -> n

  (** val nodeName : nodeKind -> char list **)

  let nodeName = function
  | Sequence ->
    'b'::('t'::('_'::('s'::('e'::('q'::('u'::('e'::('n'::('c'::('e'::[]))))))))))
  | Fallback ->
    'b'::('t'::('_'::('f'::('a'::('l'::('l'::('b'::('a'::('c'::('k'::[]))))))))))
  | Parallel1 ->
    'b'::('t'::('_'::('p'::('a'::('r'::('a'::('l'::('l'::('e'::('l'::('1'::[])))))))))))
  | Parallel2 ->
    'b'::('t'::('_'::('p'::('a'::('r'::('a'::('l'::('l'::('e'::('l'::('2'::[])))))))))))

  (** val decName : decKind -> char list **)

  let decName = function
  | Not -> 'b'::('t'::('_'::('n'::('o'::('t'::[])))))
  | IsRunning ->
    'b'::('t'::('_'::('i'::('s'::('_'::('r'::('u'::('n'::('n'::('i'::('n'::('g'::[]))))))))))))

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
    AddV (name0, (TComp (TModPar ((nodeName k), (AddP ((Simple (Qual (Id
    (rootName t1)))), (LastP (Simple (Qual (Id (rootName t2)))))))))), x)
  | Dec (d, name0, t0) ->
    let x = make_vars t0 in
    AddV (name0, (TComp (TModPar ((decName d), (LastP (Simple (Qual (Id
    (rootName t0)))))))), x)

  (** val make_main : btree -> smv_module **)

  let make_main t =
    let vars0 = make_vars t in
    { name = ('m'::('a'::('i'::('n'::[])))); params = []; vars = (Some (AddV
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
    bp_skill :: (bp_TRUE :: (bp_bin_seq :: (bp_bin_fb :: (bp_par1 :: (bp_par2 :: (bp_not :: (bp_isRunning :: (bp_tick_generator :: (
      (make_main t) :: ((ocra_bt_fsm t) :: ((ocra_main t) :: [])))))))))))
 end
