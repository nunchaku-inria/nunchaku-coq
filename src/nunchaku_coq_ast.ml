
(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Input AST} *)

module U = Nunchaku_coq_utils

module Nun_id : sig
  type t
  val of_string : string -> t 
  val of_coq_id : Names.Id.t -> t
  val of_coq_name : Names.Name.t -> t
  val pp : t U.Fmt.printer
  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
  val fresh : t -> Set.t -> t
end = struct
  type t = string
  let of_string s = s
  let of_coq_id = Names.string_of_id
  let of_coq_name = function
    | Names.Name.Anonymous -> of_string "_x"
    | Names.Name.Name id -> of_coq_id id
  module Set = Set.Make(String)
  module Map = Map.Make(String)

  let rec fresh id avoid =
    if Set.mem id avoid then
      fresh (id^"'") avoid
    else
      id

  (* adapt to Nunchaku's lexical conventions *)
  let sanitize (s:string) =
    let buf = Buffer.create (String.length s) in
    String.iter
      (function
        | '.' -> Buffer.add_char buf '_'
        | c -> Buffer.add_char buf c)
      s;
    Buffer.contents buf

  let pp out id = U.Fmt.string out (sanitize id)
end

module Builtin : sig
  type t =
    [ `Prop
    | `Type
    | `Not
    | `And
    | `Or
    | `True
    | `False
    | `Eq
    | `Equiv
    | `Imply
    | `Undefined of string
    | `Unitype
    ]

  val pp : t U.Fmt.printer
  val fixity : t -> [`Prefix | `Infix]
  val to_string : t -> string
end = struct
  type t =
    [ `Prop
    | `Type
    | `Not
    | `And
    | `Or
    | `True
    | `False
    | `Eq
    | `Equiv
    | `Imply
    | `Undefined of string
    | `Unitype
    ]

  let fixity : t -> [`Infix | `Prefix] = function
    | `Type
    | `True
    | `False
    | `Prop
    | `Not -> `Prefix
    | `And
    | `Or
    | `Imply
    | `Equiv
    | `Eq
    | `Unitype
    | `Undefined _ -> `Infix

  let to_string : t -> string = function
    | `Type -> "type"
    | `Prop -> "prop"
    | `Not -> "~"
    | `And -> "&&"
    | `Or -> "||"
    | `True -> "true"
    | `False -> "false"
    | `Eq -> "="
    | `Equiv -> "="
    | `Imply -> "=>"
    | `Undefined s -> "?_" ^ s
    | `Unitype -> "<unitype>"

  let pp out s = U.Fmt.string out (to_string s)
end

type id = Nun_id.t

type term = {
  term: term_node;
}
and term_node =
  | Builtin of Builtin.t
  | Var of var
  | AtVar of var  (* variable without implicit arguments *)
  | App of term * term list
  | Fun of typed_var * term
  | Let of var * term * term
  | Match of term * (var * var list * term) list
  | Ite of term * term * term
  | Forall of typed_var * term
  | Exists of typed_var * term
  | Mu of typed_var * term
  | TyArrow of ty * ty
  | TyForall of var * ty
  | Asserting of term * term list

(* we mix terms and types because it is hard to know, in
  [@cons a b c], which ones of [a, b, c] are types, and which ones
  are terms *)
and ty = term

and var = id

and typed_var = id * ty

let view t = t.term

(* mutual definitions of symbols, with a type and a list of axioms for each one *)
type rec_defs = (id * term * term list) list

(* specification of symbols with their types, as a list of axioms *)
type spec_defs = (id * term) list * term list

(* list of mutual type definitions (the type name, its argument variables,
   and its constructors that are (id args) *)
type mutual_types = (var * var list * (var * ty list) list) list

(* list of mutual (co) inductive predicates definitions. Each definition
    is the predicate, its type, and a list of clauses defining it *)
type mutual_preds = (var * ty * term list) list

type copy_wrt =
  | Wrt_nothing
  | Wrt_subset of term
  | Wrt_quotient of [`Partial | `Total] * term

type copy = {
  id: var; (* the new name *)
  copy_vars: var list; (* type variables *)
  of_: term; (* the definition *)
  wrt: copy_wrt; (* the optional predicate or relation *)
  abstract: var; (* abstract function *)
  concrete: var; (* concrete function *)
}

type attribute = string list
(** one attribute = list of strings separated by spaces *)

type statement_node =
  | Include of string * (string list) option (* file, list of symbols *)
  | Decl of var * ty * attribute list (* declaration of uninterpreted symbol *)
  | Axiom of term list (* axiom *)
  | Spec of spec_defs (* spec *)
  | Rec of rec_defs (* mutual rec *)
  | Data of mutual_types (* inductive type *)
  | Codata of mutual_types
  | Def of id * term  (* a=b, simple def *)
  | Pred of [`Wf | `Not_wf] * mutual_preds
  | Copred of [`Wf | `Not_wf] * mutual_preds
  | Copy of copy
  | Goal of term (* goal *)

type statement = {
  stmt_name: string option;
  stmt_value: statement_node;
}

type problem = statement list

let mk_term_ term = {term}

let builtin s = mk_term_ (Builtin s)
let var v = mk_term_ (Var v)
let at_var v = mk_term_ (AtVar v)
let rec app t l = match view t with
  | App (f, l1) -> app f (l1 @ l)
  | _ -> mk_term_ (App (t,l))
let fun_ v t = mk_term_ (Fun(v,t))
let let_ v t u = mk_term_ (Let (v,t,u))
let match_with t l = mk_term_ (Match (t,l))
let ite a b c = mk_term_ (Ite (a,b,c))
let ty_prop = builtin `Prop
let ty_type = builtin `Type
let true_ = builtin `True
let false_ = builtin `False
let not_ f = app (builtin `Not) [f]

(* apply [b], an infix operator, to [l], in an associative way *)
let rec app_infix_l f l = match l with
  | [] -> assert false
  | [t] -> t
  | a :: tl -> app f [a; app_infix_l f tl]

let and_ l = app_infix_l (builtin `And) l
let or_ l = app_infix_l (builtin `Or) l
let imply a b = app (builtin `Imply) [a;b]
let equiv a b = app (builtin `Equiv) [a;b]
let eq a b = app (builtin `Eq) [a;b]
let neq a b = not_ (eq a b)
let forall v t = mk_term_ (Forall (v, t))
let exists v t = mk_term_ (Exists (v, t))
let mu v t = mk_term_ (Mu (v,t))
let asserting t l = match l with
  | [] -> t
  | _::_ -> mk_term_ (Asserting (t,l))
let ty_arrow a b = mk_term_ (TyArrow (a,b))
let ty_forall v t = mk_term_ (TyForall (v,t))

let ty_forall_list = List.fold_right ty_forall
let ty_arrow_list = List.fold_right ty_arrow

let forall_list = List.fold_right forall
let exists_list = List.fold_right exists
let fun_list = List.fold_right fun_

let mk_stmt_ ?name st =
  {stmt_name=name; stmt_value=st }

let include_ ?name ?which f = mk_stmt_ ?name (Include(f,which))
let decl ?name ~attrs v t = mk_stmt_ ?name (Decl(v,t,attrs))
let axiom ?name l = mk_stmt_ ?name (Axiom l)
let spec ?name l = mk_stmt_ ?name (Spec l)
let rec_ ?name l = mk_stmt_ ?name (Rec l)
let def ?name a b = mk_stmt_ ?name (Def (a,b))
let data ?name l = mk_stmt_ ?name (Data l)
let codata ?name l = mk_stmt_ ?name (Codata l)
let pred ?name ~wf l = mk_stmt_ ?name (Pred (wf, l))
let copred ?name ~wf l = mk_stmt_ ?name (Copred (wf, l))
let copy ?name ~of_ ~wrt ~abstract ~concrete id vars =
  mk_stmt_ ?name (Copy {id; copy_vars=vars; of_; wrt; abstract; concrete })
let goal ?name t = mk_stmt_ ?name (Goal t)

let rec head t = match view t with
  | Var v | AtVar v -> v
  | Asserting (f,_)
  | App (f,_) -> head f
  | Builtin _ | TyArrow (_,_)
  | Fun (_,_) | Let _ | Match _ | Ite (_,_,_)
  | Forall (_,_) | Mu _ | Exists (_,_) | TyForall (_,_) ->
      invalid_arg "untypedAST.head"

let fpf = Format.fprintf

let rec unroll_if_ t = match view t with
  | Ite (a,b,c) ->
      let l, last = unroll_if_ c in
      (a,b) :: l, last
  | _ -> [], t

let pp_list_ ~sep p = U.Fmt.list ~start:"" ~stop:"" ~sep p

let pp_id = Nun_id.pp
let pp_var = Nun_id.pp

let rec pp_term out term = match view term with
  | Builtin s -> Builtin.pp out s
  | Var v -> pp_var out v
  | AtVar v -> fpf out "@@%a" Nun_id.pp v
  | App (f, [a;b]) ->
      begin match view f with
      | Builtin s when Builtin.fixity s = `Infix ->
          fpf out "@[<hv>%a@ @[<hv>%a@ %a@]@]"
            pp_term_inner a Builtin.pp s pp_term_inner b
      | _ ->
          fpf out "@[<2>%a@ %a@ %a@]" pp_term_inner f
            pp_term_inner a pp_term_inner b
      end
  | App (a, l) ->
      fpf out "@[<2>%a@ %a@]"
        pp_term_inner a (pp_list_ ~sep:" " pp_term_inner) l
  | Fun (v, t) ->
      fpf out "@[<2>fun %a.@ %a@]" pp_typed_var v pp_term t
  | Mu (v, t) ->
      fpf out "@[<2>mu %a.@ %a@]" pp_typed_var v pp_term t
  | Let (v,t,u) ->
      fpf out "@[<2>let %a :=@ %a in@ %a@]" pp_var v pp_term t pp_term u
  | Match (t,l) ->
      let pp_case out (id,vars,t) =
        fpf out "@[<hv2>| %a %a ->@ %a@]"
          pp_id id (pp_list_ ~sep:" " pp_var) vars pp_term t
      in
      fpf out "@[<hv2>match @[%a@] with@ %a end@]"
        pp_term t (pp_list_ ~sep:"" pp_case) l
  | Ite (a,b,c) ->
      (* special case to avoid deep nesting of ifs *)
      let pp_middle out (a,b) =
        fpf out "@[<2>else if@ @[%a@]@]@ @[<2>then@ @[%a@]@]" pp_term a pp_term b
      in
      let middle, last = unroll_if_ c in
      fpf out "@[<hv>@[<2>if@ @[%a@]@]@ @[<2>then@ %a@]@ %a@ @[<2>else@ %a@]@]"
        pp_term a pp_term b
        (pp_list_ ~sep:"" pp_middle) middle
        pp_term last
  | Forall (v, t) ->
      fpf out "@[<2>forall %a.@ %a@]" pp_typed_var v pp_term t
  | Exists (v, t) ->
      fpf out "@[<2>exists %a.@ %a@]" pp_typed_var v pp_term t
  | Asserting (_, []) -> assert false
  | Asserting (t, l) ->
      fpf out "@[<2>%a@ @[<2>asserting @[%a@]@]@]"
        pp_term_inner t (pp_list_ ~sep:" && " pp_term_inner) l
  | TyArrow (a, b) ->
      fpf out "@[<2>%a ->@ %a@]"
        pp_term_in_arrow a pp_term b
  | TyForall (v, t) ->
      fpf out "@[<2>pi %a:type.@ %a@]" pp_var v pp_term t
and pp_term_inner out term = match view term with
  | App _ | Fun _ | Let _ | Ite _ | Match _ | Asserting _
  | Forall _ | Exists _ | TyForall _ | Mu _ | TyArrow _ ->
      fpf out "(%a)" pp_term term
  | Builtin _ | AtVar _ | Var _ -> pp_term out term
and pp_term_in_arrow out t = match view t with
  | Builtin _
  | Var _ | AtVar _
  | App (_,_) -> pp_term out t
  | Let _ | Match _
  | Ite _
  | Forall (_,_)
  | Exists (_,_)
  | Mu _
  | Fun (_,_)
  | Asserting _
  | TyArrow (_,_)
  | TyForall (_,_) -> fpf out "@[(%a)@]" pp_term t

and pp_typed_var out (v,ty) =
  fpf out "(%a:%a)" pp_var v pp_term ty

let pp_rec_defs out l =
  let ppterms = pp_list_ ~sep:";" pp_term in
  let pp_case out (v,ty,l) =
    fpf out "@[<hv2>%a : %a :=@ %a@]" pp_var v pp_term ty ppterms l in
  fpf out "@[<hv>%a@]" (pp_list_ ~sep:" and " pp_case) l

let pp_spec_defs out (defined_l,l) =
  let ppterms = pp_list_ ~sep:";" pp_term in
  let pp_defined out (v,ty) = fpf out "@[%a : %a@]" pp_var v pp_term ty in
  let pp_defined_list out =
    fpf out "@[<hv>%a@]" (pp_list_ ~sep:" and " pp_defined)
  in
  fpf out "@[<v>%a :=@ %a@]" pp_defined_list defined_l ppterms l

let pp_ty_defs out l =
  let ppcons out (id,args) =
    fpf out "@[%a %a@]" pp_id id (pp_list_ ~sep:" " pp_term) args in
  let ppcons_l = pp_list_ ~sep:" | " ppcons in
  let pp_case out (id,ty_vars,l) =
    fpf out "@[<hv2>@[<h>%a %a@] :=@ %a@]"
      pp_id id (pp_list_ ~sep:" " pp_var) ty_vars ppcons_l l
  in
  fpf out "@[<hv>%a@]" (pp_list_ ~sep:" and " pp_case) l

let pp_wf out = function
  | `Wf -> fpf out "[wf]"
  | `Not_wf -> ()

let pp_mutual_preds out l =
  let pp_def out (p, ty, clauses) =
    fpf out "@[<hv2>@[%a@ : %a@] :=@ %a@]" pp_id p pp_term ty
      (pp_list_ ~sep:"; " pp_term) clauses
  in
  pp_list_ ~sep:" and " pp_def out l

let pp_attr out l = fpf out "@[%a@]" (pp_list_ ~sep:" " U.Fmt.string) l
let pp_attrs out = function
  | [] -> ()
  | l -> fpf out "@ [@[%a@]]" (pp_list_ ~sep:"," pp_attr) l

let pp_statement out st = match st.stmt_value with
  | Include (f, None) -> fpf out "@[include %s.@]" f
  | Include (f, Some l) -> fpf out "@[include (%a) from %s.@]"
      (pp_list_ ~sep:"," U.Fmt.string) l f
  | Decl (v, t, attrs) -> fpf out "@[val %a : %a%a.@]" pp_id v pp_term t pp_attrs attrs
  | Axiom l -> fpf out "@[axiom @[%a@].@]" (pp_list_ ~sep:";" pp_term) l
  | Spec l -> fpf out "@[spec %a.@]" pp_spec_defs l
  | Rec l -> fpf out "@[rec %a.@]" pp_rec_defs l
  | Def (a,b) ->
      fpf out "@[<2>axiom[def]@ %a@ = @[%a@].@]" pp_id a pp_term b
  | Data l -> fpf out "@[data %a.@]" pp_ty_defs l
  | Codata l -> fpf out "@[codata %a.@]" pp_ty_defs l
  | Goal t -> fpf out "@[goal %a.@]" pp_term t
  | Pred (k, preds) -> fpf out "@[pred%a %a.@]" pp_wf k pp_mutual_preds preds
  | Copy c ->
      let pp_wrt out = function
        | Wrt_nothing -> ()
        | Wrt_subset p -> fpf out "@[subset %a@]@," pp_term p
        | Wrt_quotient (`Total, r) -> fpf out "@[quotient %a@]@," pp_term r
        | Wrt_quotient (`Partial, r) -> fpf out "@[partial_quotient %a@]@," pp_term r
      in
      fpf out "@[<v2>@[<4>copy @[%a%a@] :=@ @[%a@]@]@,%aabstract = %a@,concrete = %a@]"
        pp_id c.id (pp_list_ ~sep:" " pp_id) c.copy_vars
        pp_term c.of_ pp_wrt c.wrt pp_id c.abstract pp_id c.concrete
  | Copred (k, preds) -> fpf out "@[copred%a %a.@]" pp_wf k pp_mutual_preds preds

let pp_statement_list out l =
  Format.fprintf out "@[<v>%a@]"
    (U.Fmt.list ~start:"" ~stop:"" ~sep:"" pp_statement) l
