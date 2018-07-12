
(** val add : int -> int -> int **)

let rec add = ( + )

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
  type coq_SkillSet

  val coq_SkillName : coq_SkillSet -> char list
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

type smv_element =
| VAR of varlist
| IVAR of ivarlist
| DEFINE of deflist
| ASSIGN of asslist

type smv_module = { name : identifier; params : identifier list;
                    body : smv_element list }

(** val name : smv_module -> identifier **)

let name x = x.name

(** val params : smv_module -> identifier list **)

let params x = x.params

(** val body : smv_module -> smv_element list **)

let body x = x.body

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
  append (translate_sexp e') (append (' '::('&'::(' '::[]))) (translate_sexp e''))
| Equal (e', e'') ->
  append (translate_sexp e') (append (' '::('='::(' '::[]))) (translate_sexp e''))
| Less (e', e'') ->
  append (translate_sexp e') (append (' '::('<'::(' '::[]))) (translate_sexp e''))
| Sum (e', e'') ->
  append (translate_sexp e') (append (' '::('+'::(' '::[]))) (translate_sexp e''))
| Count lst ->
  append ('c'::('o'::('u'::('n'::('t'::('('::[]))))))
    (append (translate_sexplist lst) (')'::[]))
| Case ce ->
  append ('c'::('a'::('s'::('e'::[]))))
    (append newline (append (translate_cexp ce) ('e'::('s'::('a'::('c'::[]))))))

(** val translate_sexplist : sexplist -> char list **)

and translate_sexplist = function
| Sexp e -> translate_sexp e
| AddSexp (e, rest) ->
  append (translate_sexp e) (append (','::(' '::[])) (translate_sexplist rest))

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
  append ('n'::('e'::('x'::('t'::('('::[]))))) (append (translate_sexp e') (')'::[]))

(** val translate_simp_type_spec : simp_type_spec -> char list **)

let translate_simp_type_spec = function
| TBool -> 'b'::('o'::('o'::('l'::('e'::('a'::('n'::[]))))))
| TEnum values ->
  append ('{'::(' '::[])) (append (concat (','::(' '::[])) values) (' '::('}'::[])))

(** val translate_param_list : param_list -> char list **)

let rec translate_param_list = function
| LastP e -> translate_nexp e
| AddP (e, pl') ->
  append (translate_nexp e) (append (','::(' '::[])) (translate_param_list pl'))

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

(** val translate_smv_element : smv_element -> char list **)

let translate_smv_element = function
| VAR vl -> append ('V'::('A'::('R'::[]))) (append newline (translate_varlist vl))
| IVAR il ->
  append ('I'::('V'::('A'::('R'::[])))) (append newline (translate_ivarlist il))
| DEFINE dl ->
  append ('D'::('E'::('F'::('I'::('N'::('E'::[]))))))
    (append newline (translate_deflist dl))
| ASSIGN al ->
  append ('A'::('S'::('S'::('I'::('G'::('N'::[]))))))
    (append newline (translate_asslist al))

(** val translate_body : smv_element list -> char list **)

let rec translate_body = function
| [] -> []
| e :: rest -> append (translate_smv_element e) (translate_body rest)

(** val translate : smv_module -> char list **)

let translate m =
  append ('M'::('O'::('D'::('U'::('L'::('E'::(' '::[])))))))
    (append m.name
      (append ('('::[])
        (append (concat (','::(' '::[])) m.params)
          (append (')'::[])
            (append newline (append (translate_body m.body) newline))))))

(** val translate_spec : smv_spec -> char list **)

let rec translate_spec = function
| [] -> []
| m :: rest -> append (translate m) (translate_spec rest)

module BT_bin_spec =
 functor (X:BT_SIG) ->
 struct
  type coq_NodeKind =
  | Sequence
  | Fallback
  | Parallel1
  | Parallel2

  (** val coq_NodeKind_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_NodeKind -> 'a1 **)

  let coq_NodeKind_rect f f0 f1 f2 = function
  | Sequence -> f
  | Fallback -> f0
  | Parallel1 -> f1
  | Parallel2 -> f2

  (** val coq_NodeKind_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> coq_NodeKind -> 'a1 **)

  let coq_NodeKind_rec f f0 f1 f2 = function
  | Sequence -> f
  | Fallback -> f0
  | Parallel1 -> f1
  | Parallel2 -> f2

  type coq_DecKind =
  | Not
  | Coq_isRunning

  (** val coq_DecKind_rect : 'a1 -> 'a1 -> coq_DecKind -> 'a1 **)

  let coq_DecKind_rect f f0 = function
  | Not -> f
  | Coq_isRunning -> f0

  (** val coq_DecKind_rec : 'a1 -> 'a1 -> coq_DecKind -> 'a1 **)

  let coq_DecKind_rec f f0 = function
  | Not -> f
  | Coq_isRunning -> f0

  type btree =
  | Skill of X.coq_SkillSet
  | TRUE
  | Coq_node of coq_NodeKind * char list * btree * btree
  | Coq_dec of coq_DecKind * char list * btree

  (** val btree_rect :
      (X.coq_SkillSet -> 'a1) -> 'a1 -> (coq_NodeKind -> char list -> btree -> 'a1
      -> btree -> 'a1 -> 'a1) -> (coq_DecKind -> char list -> btree -> 'a1 -> 'a1)
      -> btree -> 'a1 **)

  let rec btree_rect f f0 f1 f2 = function
  | Skill s -> f s
  | TRUE -> f0
  | Coq_node (n, s, b0, b1) ->
    f1 n s b0 (btree_rect f f0 f1 f2 b0) b1 (btree_rect f f0 f1 f2 b1)
  | Coq_dec (d, s, b0) -> f2 d s b0 (btree_rect f f0 f1 f2 b0)

  (** val btree_rec :
      (X.coq_SkillSet -> 'a1) -> 'a1 -> (coq_NodeKind -> char list -> btree -> 'a1
      -> btree -> 'a1 -> 'a1) -> (coq_DecKind -> char list -> btree -> 'a1 -> 'a1)
      -> btree -> 'a1 **)

  let rec btree_rec f f0 f1 f2 = function
  | Skill s -> f s
  | TRUE -> f0
  | Coq_node (n, s, b0, b1) ->
    f1 n s b0 (btree_rec f f0 f1 f2 b0) b1 (btree_rec f f0 f1 f2 b1)
  | Coq_dec (d, s, b0) -> f2 d s b0 (btree_rec f f0 f1 f2 b0)

  (** val count_leaves : btree -> int **)

  let rec count_leaves = function
  | Coq_node (_, _, t1, t2) -> add (count_leaves t1) (count_leaves t2)
  | Coq_dec (_, _, t0) -> count_leaves t0
  | _ -> succ 0

  (** val coq_RootName : btree -> char list **)

  let coq_RootName = function
  | Skill s -> X.coq_SkillName s
  | TRUE -> 'B'::('T'::('S'::('u'::('c'::('c'::[])))))
  | Coq_node (_, n, _, _) -> n
  | Coq_dec (_, n, _) -> n

  (** val bt_input_type : simp_type_spec **)

  let bt_input_type =
    TEnum
      (('R'::('u'::('n'::('n'::[])))) :: (('F'::('a'::('i'::('l'::[])))) :: (('S'::('u'::('c'::('c'::[])))) :: [])))

  (** val bt_output_type : type_spec **)

  let bt_output_type =
    TSimp (TEnum
      (('n'::('o'::('n'::('e'::[])))) :: (('r'::('u'::('n'::('n'::('i'::('n'::('g'::[]))))))) :: (('f'::('a'::('i'::('l'::('e'::('d'::[])))))) :: (('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[]))))))))) :: [])))))

  (** val boiler_tick_generator : smv_module **)

  let boiler_tick_generator =
    { name =
      ('b'::('t'::('_'::('t'::('i'::('c'::('k'::('_'::('g'::('e'::('n'::('e'::('r'::('a'::('t'::('o'::('r'::[])))))))))))))))));
      params =
      (('t'::('o'::('p'::('_'::('l'::('e'::('v'::('e'::('l'::('_'::('b'::('t'::[])))))))))))) :: []);
      body = ((ASSIGN (AddA ((Init ((Mod
      (('t'::('o'::('p'::('_'::('l'::('e'::('v'::('e'::('l'::('_'::('b'::('t'::[])))))))))))),
      (Id ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (BConst SmvT))), (LastA
      (Next ((Mod
      (('t'::('o'::('p'::('_'::('l'::('e'::('v'::('e'::('l'::('_'::('b'::('t'::[])))))))))))),
      (Id ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Simple (Neg (Equal
      ((Qual (Mod
      (('t'::('o'::('p'::('_'::('l'::('e'::('v'::('e'::('l'::('_'::('b'::('t'::[])))))))))))),
      (Id ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('n'::('o'::('n'::('e'::[]))))))))))))))) :: []) }

  (** val boiler_skill : smv_module **)

  let boiler_skill =
    { name = ('b'::('t'::('_'::('s'::('k'::('i'::('l'::('l'::[])))))))); params =
      []; body = ((IVAR (LastI (('i'::('n'::('p'::('u'::('t'::[]))))),
      bt_input_type))) :: ((VAR (AddV (('o'::('u'::('t'::('p'::('u'::('t'::[])))))),
      bt_output_type, (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp
      TBool)))))) :: ((ASSIGN (AddA ((Init ((Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))), (SConst
      ('n'::('o'::('n'::('e'::[]))))))), (LastA (Next ((Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[]))))))), (Simple (Case (AddCexp ((Neg
      (Qual (Id ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (SConst
      ('n'::('o'::('n'::('e'::[]))))), (AddCexp ((Equal ((Qual (Id
      ('i'::('n'::('p'::('u'::('t'::[]))))))), (SConst
      ('R'::('u'::('n'::('n'::[]))))))), (SConst
      ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))), (AddCexp ((Equal ((Qual
      (Id ('i'::('n'::('p'::('u'::('t'::[]))))))), (SConst
      ('F'::('a'::('i'::('l'::[]))))))), (SConst
      ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))), (Cexp ((Equal ((Qual (Id
      ('i'::('n'::('p'::('u'::('t'::[]))))))), (SConst
      ('S'::('u'::('c'::('c'::[]))))))), (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))))))))))))))))) :: []))) }

  (** val boiler_TRUE : smv_module **)

  let boiler_TRUE =
    { name = ('b'::('t'::('_'::('T'::('R'::('U'::('E'::[]))))))); params = [];
      body = ((VAR (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp
      TBool)))) :: ((DEFINE (LastD (('o'::('u'::('t'::('p'::('u'::('t'::[])))))),
      (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[]))))))))))))) :: [])) }

  (** val boiler_sequence : smv_module **)

  let boiler_sequence =
    { name =
      ('b'::('t'::('_'::('s'::('e'::('q'::('u'::('e'::('n'::('c'::('e'::[])))))))))));
      params =
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))) :: (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))) :: []));
      body = ((VAR (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp
      TBool)))) :: ((ASSIGN (AddA ((Invar ((Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))), (LastA (Invar ((Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Equal ((Qual (Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))))))))) :: ((DEFINE
      (LastD (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case (AddCexp ((Equal
      ((Qual (Mod (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))), (Qual
      (Mod (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (Cexp ((BConst SmvT), (Qual
      (Mod (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))))))))))) :: []))) }

  (** val boiler_fallback : smv_module **)

  let boiler_fallback =
    { name =
      ('b'::('t'::('_'::('f'::('a'::('l'::('l'::('b'::('a'::('c'::('k'::[])))))))))));
      params =
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))) :: (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))) :: []));
      body = ((VAR (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp
      TBool)))) :: ((ASSIGN (AddA ((Invar ((Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))), (LastA (Invar ((Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Equal ((Qual (Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))))))) :: ((DEFINE (LastD
      (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case (AddCexp ((Equal ((Qual
      (Mod (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))), (Qual (Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (Cexp ((BConst SmvT), (Qual
      (Mod (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))))))))))) :: []))) }

  (** val boiler_par1 : smv_module **)

  let boiler_par1 =
    { name =
      ('b'::('t'::('_'::('p'::('a'::('r'::('a'::('l'::('l'::('e'::('l'::('1'::[]))))))))))));
      params =
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))) :: (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))) :: []));
      body = ((VAR (AddV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp
      TBool), (LastV
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('s'::('t'::('o'::('r'::('e'::('d'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))),
      bt_output_type))))) :: ((ASSIGN (AddA ((Invar ((Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))), (AddA ((Invar ((Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
      ('i'::('s'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('a'::('c'::('t'::('i'::('v'::('e'::[]))))))))))))))))))))),
      (AddA ((Init ((Id
      ('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('s'::('t'::('o'::('r'::('e'::('d'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))))))))))))))),
      (Qual (Id ('n'::('o'::('n'::('e'::[])))))))), (LastA (Next ((Id
      ('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('s'::('t'::('o'::('r'::('e'::('d'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))))))))))))))),
      (Simple (Case (AddCexp ((Qual (Id
      ('i'::('s'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('a'::('c'::('t'::('i'::('v'::('e'::[]))))))))))))))))))),
      (Qual (Mod (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (Cexp ((BConst SmvT), (Qual
      (Id
      ('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('s'::('t'::('o'::('r'::('e'::('d'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))))))))))))))))))))) :: ((DEFINE
      (AddD
      (('i'::('s'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('a'::('c'::('t'::('i'::('v'::('e'::[]))))))))))))))))),
      (Neg (Equal ((Qual (Mod (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))),
      (Id ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('n'::('o'::('n'::('e'::[])))))))), (AddD
      (('i'::('s'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::('_'::('a'::('c'::('t'::('i'::('v'::('e'::[])))))))))))))))))),
      (Neg (Equal ((Qual (Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('n'::('o'::('n'::('e'::[])))))))), (AddD
      (('t'::('r'::('u'::('e'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))),
      (Count (AddSexp ((Equal ((Qual (Id
      ('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('s'::('t'::('o'::('r'::('e'::('d'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))))),
      (SConst ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))),
      (Sexp (Equal ((Qual (Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))))))),
      (AddD
      (('r'::('u'::('n'::('n'::('i'::('n'::('g'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[])))))))))))))))))))),
      (Count (AddSexp ((Equal ((Qual (Id
      ('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('s'::('t'::('o'::('r'::('e'::('d'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))))),
      (SConst ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))))), (Sexp (Equal
      ((Qual (Mod (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))))))))), (LastD
      (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case (AddCexp ((And ((Qual (Id
      ('i'::('s'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::('_'::('a'::('c'::('t'::('i'::('v'::('e'::[])))))))))))))))))))),
      (Less ((SConst ('0'::[])), (Qual (Id
      ('t'::('r'::('u'::('e'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))))))))),
      (SConst ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))),
      (AddCexp ((And ((Qual (Id
      ('i'::('s'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::('_'::('a'::('c'::('t'::('i'::('v'::('e'::[])))))))))))))))))))),
      (Less ((Sum ((Qual (Id
      ('t'::('r'::('u'::('e'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))))),
      (Qual (Id
      ('r'::('u'::('n'::('n'::('i'::('n'::('g'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[])))))))))))))))))))))))),
      (SConst ('1'::[])))))), (SConst ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))),
      (AddCexp ((Qual (Id
      ('i'::('s'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::('_'::('a'::('c'::('t'::('i'::('v'::('e'::[])))))))))))))))))))),
      (SConst ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))), (Cexp ((BConst
      SmvT), (SConst ('n'::('o'::('n'::('e'::[]))))))))))))))))))))))))) :: []))) }

  (** val boiler_par2 : smv_module **)

  let boiler_par2 =
    { name =
      ('b'::('t'::('_'::('p'::('a'::('r'::('a'::('l'::('l'::('e'::('l'::('2'::[]))))))))))));
      params =
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))) :: (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))) :: []));
      body = ((VAR (AddV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp
      TBool), (LastV
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('s'::('t'::('o'::('r'::('e'::('d'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))),
      bt_output_type))))) :: ((ASSIGN (AddA ((Invar ((Mod
      (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))), (AddA ((Invar ((Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
      ('i'::('s'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('a'::('c'::('t'::('i'::('v'::('e'::[]))))))))))))))))))))),
      (AddA ((Init ((Id
      ('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('s'::('t'::('o'::('r'::('e'::('d'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))))))))))))))),
      (Qual (Id ('n'::('o'::('n'::('e'::[])))))))), (LastA (Next ((Id
      ('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('s'::('t'::('o'::('r'::('e'::('d'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))))))))))))))),
      (Simple (Case (AddCexp ((Qual (Id
      ('i'::('s'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('a'::('c'::('t'::('i'::('v'::('e'::[]))))))))))))))))))),
      (Qual (Mod (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (Cexp ((BConst SmvT), (Qual
      (Id
      ('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('s'::('t'::('o'::('r'::('e'::('d'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))))))))))))))))))))) :: ((DEFINE
      (AddD
      (('i'::('s'::('_'::('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('a'::('c'::('t'::('i'::('v'::('e'::[]))))))))))))))))),
      (Neg (Equal ((Qual (Mod (('l'::('e'::('f'::('t'::('_'::('b'::('t'::[]))))))),
      (Id ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('n'::('o'::('n'::('e'::[])))))))), (AddD
      (('i'::('s'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::('_'::('a'::('c'::('t'::('i'::('v'::('e'::[])))))))))))))))))),
      (Neg (Equal ((Qual (Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('n'::('o'::('n'::('e'::[])))))))), (AddD
      (('t'::('r'::('u'::('e'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))),
      (Count (AddSexp ((Equal ((Qual (Id
      ('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('s'::('t'::('o'::('r'::('e'::('d'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))))),
      (SConst ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))),
      (Sexp (Equal ((Qual (Mod
      (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))))))),
      (AddD
      (('r'::('u'::('n'::('n'::('i'::('n'::('g'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[])))))))))))))))))))),
      (Count (AddSexp ((Equal ((Qual (Id
      ('l'::('e'::('f'::('t'::('_'::('b'::('t'::('_'::('s'::('t'::('o'::('r'::('e'::('d'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::[]))))))))))))))))))))))),
      (SConst ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))))), (Sexp (Equal
      ((Qual (Mod (('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))))))))), (LastD
      (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case (AddCexp ((And ((Qual (Id
      ('i'::('s'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::('_'::('a'::('c'::('t'::('i'::('v'::('e'::[])))))))))))))))))))),
      (Less ((SConst ('1'::[])), (Qual (Id
      ('t'::('r'::('u'::('e'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))))))))),
      (SConst ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))),
      (AddCexp ((And ((Qual (Id
      ('i'::('s'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::('_'::('a'::('c'::('t'::('i'::('v'::('e'::[])))))))))))))))))))),
      (Less ((Sum ((Qual (Id
      ('t'::('r'::('u'::('e'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[]))))))))))))))))))),
      (Qual (Id
      ('r'::('u'::('n'::('n'::('i'::('n'::('g'::('_'::('o'::('u'::('t'::('p'::('u'::('t'::('_'::('c'::('o'::('u'::('n'::('t'::[])))))))))))))))))))))))),
      (SConst ('2'::[])))))), (SConst ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))),
      (AddCexp ((Qual (Id
      ('i'::('s'::('_'::('r'::('i'::('g'::('h'::('t'::('_'::('b'::('t'::('_'::('a'::('c'::('t'::('i'::('v'::('e'::[])))))))))))))))))))),
      (SConst ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))), (Cexp ((BConst
      SmvT), (SConst ('n'::('o'::('n'::('e'::[]))))))))))))))))))))))))) :: []))) }

  (** val boiler_not : smv_module **)

  let boiler_not =
    { name = ('b'::('t'::('_'::('n'::('o'::('t'::[])))))); params =
      (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))) :: []); body =
      ((VAR (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp
      TBool)))) :: ((ASSIGN (LastA (Invar ((Mod
      (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))))) :: ((DEFINE (LastD
      (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case (AddCexp ((Equal ((Qual
      (Mod (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))), (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))), (AddCexp
      ((Equal ((Qual (Mod
      (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))))), (SConst
      ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))), (Cexp ((BConst SmvT), (Qual
      (Mod (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))))))))))))) :: []))) }

  (** val boiler_isRunning : smv_module **)

  let boiler_isRunning =
    { name =
      ('b'::('t'::('_'::('i'::('s'::('R'::('u'::('n'::('n'::('i'::('n'::('g'::[]))))))))))));
      params = (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))) :: []);
      body = ((VAR (LastV (('e'::('n'::('a'::('b'::('l'::('e'::[])))))), (TSimp
      TBool)))) :: ((ASSIGN (LastA (Invar ((Mod
      (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))), (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[]))))))))), (Qual (Id
      ('e'::('n'::('a'::('b'::('l'::('e'::[])))))))))))) :: ((DEFINE (LastD
      (('o'::('u'::('t'::('p'::('u'::('t'::[])))))), (Case (AddCexp ((Equal ((Qual
      (Mod (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('r'::('u'::('n'::('n'::('i'::('n'::('g'::[])))))))))), (SConst
      ('s'::('u'::('c'::('c'::('e'::('e'::('d'::('e'::('d'::[])))))))))), (AddCexp
      ((Equal ((Qual (Mod
      (('c'::('h'::('i'::('l'::('d'::('_'::('b'::('t'::[])))))))), (Id
      ('o'::('u'::('t'::('p'::('u'::('t'::[])))))))))), (SConst
      ('n'::('o'::('n'::('e'::[]))))))), (SConst ('n'::('o'::('n'::('e'::[]))))),
      (Cexp ((BConst SmvT), (SConst
      ('f'::('a'::('i'::('l'::('e'::('d'::[]))))))))))))))))) :: []))) }

  (** val nodename : coq_NodeKind -> char list **)

  let nodename = function
  | Sequence ->
    'b'::('t'::('_'::('s'::('e'::('q'::('u'::('e'::('n'::('c'::('e'::[]))))))))))
  | Fallback ->
    'b'::('t'::('_'::('f'::('a'::('l'::('l'::('b'::('a'::('c'::('k'::[]))))))))))
  | Parallel1 ->
    'b'::('t'::('_'::('p'::('a'::('r'::('a'::('l'::('l'::('e'::('l'::('1'::[])))))))))))
  | Parallel2 ->
    'b'::('t'::('_'::('p'::('a'::('r'::('a'::('l'::('l'::('e'::('l'::('2'::[])))))))))))

  (** val decname : coq_DecKind -> char list **)

  let decname = function
  | Not -> 'b'::('t'::('_'::('n'::('o'::('t'::[])))))
  | Coq_isRunning ->
    'b'::('t'::('_'::('i'::('s'::('_'::('r'::('u'::('n'::('n'::('i'::('n'::('g'::[]))))))))))))

  (** val make_vars : btree -> varlist **)

  let rec make_vars = function
  | Skill s ->
    LastV ((X.coq_SkillName s), (TComp (TMod
      ('b'::('t'::('_'::('s'::('k'::('i'::('l'::('l'::[])))))))))))
  | TRUE ->
    LastV (('t'::[]), (TComp (TMod
      ('b'::('t'::('_'::('T'::('R'::('U'::('E'::[]))))))))))
  | Coq_node (k, name0, t1, t2) ->
    let x = varlist_app (make_vars t1) (make_vars t2) in
    AddV (name0, (TComp (TModPar ((nodename k), (AddP ((Simple (Qual (Id
    (coq_RootName t1)))), (LastP (Simple (Qual (Id (coq_RootName t2)))))))))), x)
  | Coq_dec (d, name0, t0) ->
    let x = make_vars t0 in
    AddV (name0, (TComp (TModPar ((decname d), (LastP (Simple (Qual (Id
    (coq_RootName t0)))))))), x)

  (** val make_main : btree -> smv_module **)

  let make_main t =
    let l = make_vars t in
    { name = ('m'::('a'::('i'::('n'::[])))); params = []; body = ((VAR (AddV
    (('t'::('i'::('c'::('k'::('_'::('g'::('e'::('n'::('e'::('r'::('a'::('t'::('o'::('r'::[])))))))))))))),
    (TComp (TModPar
    (('b'::('t'::('_'::('t'::('i'::('c'::('k'::('_'::('g'::('e'::('n'::('e'::('r'::('a'::('t'::('o'::('r'::[]))))))))))))))))),
    (LastP (Simple (Qual (Id (coq_RootName t)))))))), l))) :: []) }

  (** val make_spec : btree -> smv_module list **)

  let make_spec t =
    boiler_tick_generator :: (boiler_skill :: (boiler_TRUE :: (boiler_sequence :: (boiler_fallback :: (boiler_par1 :: (boiler_par2 :: (boiler_not :: (boiler_isRunning :: (
      (make_main t) :: [])))))))))
 end

type my_skills =
| Sk1
| Sk2
| Sk3
| Sk4

(** val my_names : my_skills -> char list **)

let my_names = function
| Sk1 ->
  'g'::('o'::('t'::('o'::('_'::('k'::('i'::('t'::('c'::('h'::('e'::('n'::[])))))))))))
| Sk2 ->
  'f'::('i'::('n'::('d'::('_'::('b'::('o'::('t'::('t'::('l'::('e'::[]))))))))))
| Sk3 ->
  'f'::('e'::('t'::('c'::('h'::('_'::('b'::('o'::('t'::('t'::('l'::('e'::[])))))))))))
| Sk4 -> 'a'::('s'::('k'::('_'::('h'::('e'::('l'::('p'::[])))))))

module Coq_ex_skills =
 struct
  type coq_SkillSet = my_skills

  (** val coq_SkillName : my_skills -> char list **)

  let coq_SkillName =
    my_names
 end

module Coq_bts1 = BT_bin_spec(Coq_ex_skills)

(** val sc1 : Coq_bts1.btree **)

let sc1 =
  Coq_bts1.Coq_node (Coq_bts1.Fallback,
    ('d'::('o'::('_'::('w'::('i'::('t'::('h'::('_'::('h'::('e'::('l'::('p'::[])))))))))))),
    (Coq_bts1.Coq_node (Coq_bts1.Sequence,
    ('g'::('o'::('_'::('a'::('n'::('d'::('_'::('f'::('e'::('t'::('c'::('h'::('_'::('b'::('o'::('t'::('t'::('l'::('e'::[]))))))))))))))))))),
    (Coq_bts1.Skill Sk1), (Coq_bts1.Coq_node (Coq_bts1.Sequence,
    ('f'::('i'::('n'::('d'::('_'::('a'::('n'::('d'::('_'::('f'::('e'::('t'::('c'::('h'::('_'::('b'::('o'::('t'::('t'::('l'::('e'::[]))))))))))))))))))))),
    (Coq_bts1.Skill Sk2), (Coq_bts1.Skill Sk3))))), (Coq_bts1.Skill Sk4))

                    (****** END OF GENERATED CODE ******)

let camlstring_of_coqstring (s: char list) =
  let r = Bytes.create (List.length s) in
  let rec fill pos = function
  | [] -> r
  | c :: s -> Bytes.set r pos c; fill (pos + 1) s
  in Bytes.to_string (fill 0 s)

let main() =
  print_string
    (camlstring_of_coqstring
       (concat [] (List.map translate (Coq_bts1.make_spec sc1))));
  exit 0
;;

main();;
