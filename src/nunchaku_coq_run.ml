
(** {1 The interface to Nunchaku} *)

(* inspiration from:
   https://github.com/mlasson/paramcoq/blob/master/src/parametricity.ml
   https://github.com/jpdeplaix/why3/blob/553cbabbffeb8116d9e7a3b4e95d2a2a5f9332f3/src/coq-tactic/why3tac.ml
   *)

module U = Nunchaku_coq_utils
module PV = Proofview

type coq_term = Term.constr

let fpf = Format.fprintf

module Nun_id : sig
  type t
  val of_string : string -> t 
  val of_coq_id : Names.Id.t -> t
  val pp : t U.Fmt.printer
  module Set : Set.S with type elt = t
  module Map : Map.S with type key = t
end = struct
  type t = string
  let of_string s = s
  let of_coq_id = Names.string_of_id
  let pp = U.Fmt.string
  module Set = Set.Make(String)
  module Map = Map.Make(String)
end

(** {2 Intermediate AST} *)
module Ast = struct
  type id = Nun_id.t

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

  type statement = {
    st_id: int;
    st_view: statement_view;
  }
  and statement_view =
    | Stmt_declare of id * ty
    | Stmt_define of id * ty * term
    | Stmt_goal of term

  module St_set = Set.Make(struct
      type t = statement
      let compare a b = Pervasives.compare a.st_id b.st_id
    end)

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

  let ty_var_of_id id = Nun_id.of_coq_id id, type_
  let const_of_id id = const (Nun_id.of_coq_id id)

  let mk_st_ =
    let n = ref 0 in
    fun st_view -> incr n; {st_view; st_id= !n }

  let st_declare id ty = mk_st_ (Stmt_declare (id,ty))
  let st_define id ty rhs = mk_st_ (Stmt_define (id,ty,rhs))
  let st_goal g = mk_st_ (Stmt_goal g)

  let pp_id = Nun_id.pp
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

  let pp_statement out st = match st.st_view with
    | Stmt_declare (id,ty) ->
      Format.fprintf out "(@[<2>decl %a@ : %a@])" pp_id id pp_ty ty
    | Stmt_define (id,ty,rhs) ->
      Format.fprintf out "(@[<2>def %a@ : %a@ := %a@])" pp_id id pp_ty ty pp_term rhs
    | Stmt_goal g -> Format.fprintf out "(@[goal %a@])" pp_term g
end

(** {2 Debug Output}

    We optionally write to a file.
    TODO: use environment variable instead? Or pure Coq options? *)

let log_active = true (* if true, {!Log.output} will write to some file *)

module Log : sig
  val output : string -> unit
  val outputf : ('a, Format.formatter, unit, unit, unit, unit) format6 -> 'a
end = struct
  let output =
    if log_active then (
      let oc = open_out "/tmp/nunchaku_coq.log" in
      fun s ->
        output_string oc s; output_char oc '\n'; flush oc
    ) else (fun _ -> ())

  let outputf msg = U.Fmt.ksprintf msg ~f:output
end

(** {2 Problem Extraction}

    This converts the given Coq goal into some problem that roughly looks
    like what Nunchaku will accept. *)

module Extract : sig
  val problem_of_goal : [`NF] PV.Goal.t -> Ast.problem
end = struct
  let string_of_globname (n:Globnames.global_reference): string =
    let module G = Globnames in
    begin match n with
      | G.ConstRef c -> Names.string_of_con c
      | G.VarRef v -> "(var " ^ Names.Id.to_string v ^ ")"
      | G.IndRef (inds,i) ->
        Printf.sprintf "(ind_%d in %s)" i (Names.string_of_mind inds)
      | G.ConstructRef ((inds,i),n) ->
        Printf.sprintf "(cstor_%d in (ind_%d in %s))" n i (Names.string_of_mind inds)
    end

  let string_of_name (n:Names.Name.t): string = match n with
    | Names.Name.Anonymous -> "<anonymous>"
    | Names.Name.Name id -> Names.string_of_id id

  let l_of_refset_env set =
    Globnames.Refset_env.fold (fun x l-> string_of_globname x::l) set []

  let l_of_map1 m =
    Globnames.Refmap_env.fold
      (fun x l acc-> (string_of_globname x,l_of_refset_env l)::acc) m []

  type map2 = 
    (Names.Label.t *
       (Names.Name.t * Constr.t option * Constr.t) list *
       Constr.t)
      list Globnames.Refmap_env.t

  let l_of_map2 (m:map2) =
    Globnames.Refmap_env.fold
      (fun x l acc-> (string_of_globname x,l)::acc) m []

  let pp_name out l = U.Fmt.string out (string_of_name l)
  let pp_triple out (x,args,ret) =
    Format.fprintf out "(@[%s (%a) %a@])"
      (Names.string_of_label x)
      U.Fmt.(list (triple pp_name (option U.pp_term) U.pp_term)) args
      U.pp_term ret

  (* print raw data from [Assumptions.traverse] *)
  let pp_raw_traverse out (set,map,map2) =
    let pp_map_entry out (s,l) =
      Format.fprintf out "(@[<2>%s: [@[%a@]]@])" s U.Fmt.(list string) l
    and pp_map2_entry out (s,l) =
      Format.fprintf out "(@[<2>%s: [@[%a@]]@])" s U.Fmt.(list pp_triple) l
    in
    Format.fprintf out
      "(@[<v>constants: [@[%a@]],@ deps: [@[%a@]]@,@ map2: [@[%a@]]@])"
      U.Fmt.(list string) (l_of_refset_env set)
      U.Fmt.(list pp_map_entry) (l_of_map1 map)
      U.Fmt.(list pp_map2_entry) (l_of_map2 map2)

  let string_of_ctx_object (x:Printer.context_object): string = match x with
    | Printer.Variable id -> Names.string_of_id id
    | Printer.Axiom (c,trip) ->
      U.Fmt.sprintf "(@[axiom %s@ : [@[<hv>%a@]]@])"
        (Names.string_of_con c) (U.Fmt.list pp_triple) trip
    | Printer.Opaque c -> U.Fmt.sprintf "(opaque %s)" (Names.string_of_con c)
    | Printer.Transparent c ->
      U.Fmt.sprintf "(transparent %s)" (Names.string_of_con c)

  let pp_ctxmap out map =
    let l = Printer.ContextObjectMap.fold (fun k ty acc ->(k,ty)::acc) map [] in
    let pp_pair out (key,ty) =
      fpf out "%s: %a" (string_of_ctx_object key) U.pp_term ty
    in
    fpf out "[@[%a@]]" (U.Fmt.list pp_pair) l

  (* recover the statement defining/declaring [l] *)
  let fetch_def_of_label env (l:Names.Label.t): Ast.statement =
    assert false (* TODO *)

  let problem_of_goal (g:[`NF] PV.Goal.t) : Ast.problem =
    let g_term = PV.Goal.concl g in
    let env = PV.Goal.env g in
    let hyps = PV.Goal.hyps g in
    (* call this handy function to get all dependencies *)
    let set, map, map2 =
      Assumptions.traverse (Names.Label.make "Top") g_term
    in
    Log.outputf "@[<2>get_problem:@ @[%a@]@]" pp_raw_traverse (set,map,map2);
    (* FIXME?
    let ctxmap =
      Assumptions.assumptions ~add_opaque:true ~add_transparent:true
        Names.full_transparent_state
        (Globnames.global_of_constr g_term) g_term
    in
    Log.outputf "@[<2>ctxmap: %a@]" pp_ctxmap ctxmap;
    *)
    assert false
end

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

  (* TODO *)
  let call pb =
    Unknown "should call nunchaku"

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
       (*PV.tclLIFT (N.print_debug (Pp.str ("extract from goal: " ^ Prettyp.default_object_pr.Prettyp. *)
       let pb = Extract.problem_of_goal g in
       Solve.tactic pb)


