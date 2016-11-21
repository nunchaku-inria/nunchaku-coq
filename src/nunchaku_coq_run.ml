
(** {1 The interface to Nunchaku} *)

(* inspiration from:
   https://github.com/mlasson/paramcoq/blob/master/src/parametricity.ml
   https://github.com/jpdeplaix/why3/blob/553cbabbffeb8116d9e7a3b4e95d2a2a5f9332f3/src/coq-tactic/why3tac.ml
   *)

module U = Nunchaku_coq_utils
module PV = Proofview

type coq_term = Term.constr

(** {2 Intermediate AST} *)
module Ast = struct
  type id = string

  type term =
    | Var of var
    | Const of id
    | App of term * term list
    | Fun of typed_var * term
    | Pi of typed_var * term
    | Builtin of builtin

  and ty = term
  and var = id
  and typed_var = id * ty

  and builtin =
    | B_true
    | B_false
    | B_and
    | B_or
    | B_not
    | B_imply
    | B_prop
    | B_type

  type statement =
    | Stmt_declare of id * ty
    | Stmt_define of id * ty * term
    | Stmt_goal of term

  type problem = statement list

  let var v = Var v
  let const c = Const c
  let app f l = match f, l with
    | _, [] -> f
    | App (f1,l1), _ -> App(f1, l1@l)
    | _ -> App (f,l)
  let fun_ v t = Fun (v,t)
  let pi v t = Pi (v,t)
  let builtin b = Builtin b
  let app_builtin b l = app (builtin b) l

  let true_ = builtin B_true
  let false_ = builtin B_false
  let imply a b = app_builtin B_imply [a;b]
  let and_ l = app_builtin B_and l
  let or_ l = app_builtin B_or l
  let not_ a = app_builtin B_not [a]
  let prop = builtin B_prop
  let type_ = builtin B_type

  let pp_id = U.Fmt.string
  let pp_var = pp_id

  let rec pp_term out = function
    | Var v -> pp_var out v
    | Const id -> pp_id out id
    | App (f, l) ->
      Format.fprintf out "(@[<hv2>%a@ %a@])"
        pp_term f (U.Fmt.list ~sep:" " pp_term) l
    | Fun (v,t) ->
      Format.fprintf out "(@[<2>fun %a@ %a@])" pp_typed_var v pp_term t
    | Pi (v,t) ->
      Format.fprintf out "(@[<2>pi %a@ %a@])" pp_typed_var v pp_term t
    | Builtin b -> pp_builtin out b
  and pp_ty out ty = pp_term out ty
  and pp_typed_var out (v,ty) = Format.fprintf out "(@[%a@ %a@])" pp_var v pp_ty ty
  and pp_builtin out = function
    | B_true -> U.Fmt.string out "true"
    | B_false -> U.Fmt.string out "false"
    | B_prop -> U.Fmt.string out "prop"
    | B_type -> U.Fmt.string out "type"
    | B_and -> U.Fmt.string out "and"
    | B_or -> U.Fmt.string out "or"
    | B_not -> U.Fmt.string out "not"
    | B_imply -> U.Fmt.string out "=>"

  let pp_statement out = function
    | Stmt_declare (id,ty) ->
      Format.fprintf out "(@[<2>decl %a@ : %a@])" pp_id id pp_ty ty
    | Stmt_define (id,ty,rhs) ->
      Format.fprintf out "(@[<2>def %a@ : %a@ := %a@])" pp_id id pp_ty ty pp_term rhs
    | Stmt_goal g -> Format.fprintf out "(@[goal %a@])" pp_term g
end

let get_problem (g:_ PV.Goal.t) : Ast.problem =
  assert false

exception Nunchaku_counter_ex

module N = PV.NonLogical

module Solve : sig
  type res =
    | Ok
    | Counter_ex of string
    | Unknown of string

  val call : Ast.problem -> res
  (** Call nunchaku on the given problem *)

  val return_res : res -> unit PV.tactic
  (** Return the result to Coq *)

  val timeout : int ref

  val tactic : Ast.problem -> unit PV.tactic
  (** The whole tactic *)
end = struct
  type res =
    | Ok
    | Counter_ex of string
    | Unknown of string

  let call pb =
    assert false (* TODO *)

  let return_res = function
    | Ok -> PV.tclUNIT ()
    | Unknown str ->
      PV.tclTHEN
        (PV.tclLIFT (N.print_debug (Pp.str "nunchaku returned `unknown`")))
        (PV.tclUNIT ())
    | Counter_ex str ->
      PV.tclTHEN
        (PV.tclLIFT (N.print_warning (Pp.str "Nunchaku found a counter-example")))
        (PV.tclZERO Nunchaku_counter_ex)

  let timeout : int ref = ref 10

  let tactic pb =
    let t1 = N.timeout !timeout (N.make (fun () -> call pb)) in
    PV.tclBIND (PV.tclLIFT t1) return_res
      
end

let call (): unit PV.tactic =
  PV.Goal.nf_enter
    (fun g ->
       let pb = get_problem g in
       Solve.tactic pb)


