
(** {1 The interface to Nunchaku} *)

(* inspiration from:
   https://github.com/mlasson/paramcoq/blob/master/src/parametricity.ml
   https://github.com/jpdeplaix/why3/blob/553cbabbffeb8116d9e7a3b4e95d2a2a5f9332f3/src/coq-tactic/why3tac.ml
   *)

module U = Nunchaku_coq_utils
module PV = Proofview

type coq_term = Term.constr

let fpf = Format.fprintf

(** {2 Intermediate AST} *)
module Ast = Nunchaku_coq_ast

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


