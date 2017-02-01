
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

(** {2 Debug Output} *)

type level = Feedback.level
type log_msg = level * Pp.std_ppcmds

module Log : sig
  val output : level -> string -> unit
  val outputf : level -> ('a, Format.formatter, unit, unit, unit, unit) format6 -> 'a
  val pop_logs : unit -> log_msg list
end = struct
  let st_ : log_msg list ref = ref []

  let output l s = st_ := (l,Pp.str s) :: !st_
  let outputf l msg = U.Fmt.ksprintf msg ~f:(output l)
  let pop_logs () =
    let l = List.rev !st_ in
    st_ := [];
    l
end

(** {2 Problem Extraction}

    This converts the given Coq goal into some problem that roughly looks
    like what Nunchaku will accept. *)

module Coq = struct
  let true_  = Coqlib.build_coq_True ()
  let false_ = Coqlib.build_coq_False ()
  let and_   = Coqlib.build_coq_and ()
  let iff_   = Coqlib.build_coq_iff ()
  let or_    = Coqlib.build_coq_or ()
  let eq_    = Coqlib.build_coq_eq ()
end

module Extract : sig
  val problem_of_goal : ([`NF],_) PV.Goal.t -> Ast.problem
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

  let id_of_const (cn:Names.constant): Ast.Nun_id.t =
    Names.(cn |> Constant.user |> KerName.to_string |> Ast.Nun_id.of_string)

  (* convert [t] into a Nunchaku term, and return the list of constants
     occurring in [t] *)
  let term_of_coq (t:coq_term) : Ast.term * Names.constant list =
    let module A = Ast in
    let constants = ref [] in
    (* adds a fresh (in subst) identifier based on [x] as the 0-th
       element of subst. *)
    (* TODO: subst should probably be a map. *)
    let push_fresh (x:Names.Name.t) (subst:Ast.id list) : Ast.id list =
      let x = Ast.Nun_id.of_coq_name x in
      let fresh = Ast.Nun_id.fresh x (Ast.Nun_id.Set.of_list subst) in
      fresh::subst
    in
    let rec simple_type_of_coq (subst:Ast.id list) (t:coq_term) : Ast.ty =
      match Constr.kind t with
      | Constr.Sort (Sorts.Prop _) -> A.ty_prop
      | Constr.Sort (Sorts.Type _) -> A.ty_type
      | Constr.Prod (_,a,b) when not (Termops.dependent (Constr.mkRel 1) b) ->
        A.ty_arrow (simple_type_of_coq subst a) (simple_type_of_coq subst b)
      | Constr.Const (cn,_) ->
        constants := cn :: !constants;
        A.var (id_of_const cn)
      | _ -> assert false
    in
    let rec term_of_coq (subst:Ast.id list) (t:coq_term) : Ast.term =
      match Constr.kind t with
      (* Propositional connectives. *)
      | _ when Constr.equal t Coq.true_ -> A.true_
      | _ when Constr.equal t Coq.false_ -> A.false_
      | Constr.App (h, [| p ; q |]) when Constr.equal h Coq.and_ ->
        A.and_ [term_of_coq subst p ; term_of_coq subst q]
      | Constr.App (h, [| p ; q |]) when Constr.equal h Coq.or_ ->
        A.or_ [term_of_coq subst p ; term_of_coq subst q]
      | Constr.App (h, [| p ; q |]) when Constr.equal h Coq.iff_ ->
        A.equiv (term_of_coq subst p) (term_of_coq subst q)
      | Constr.App (h, [| _ ; p ; q |]) when Globnames.is_global Coq.eq_ h ->
        A.eq (term_of_coq subst p) (term_of_coq subst q)
      (* arnaud: todo: je crois qu'il y a une fonction de bibliothèque pour
         tester si le de Bruijn 1 est dans un terme. Fix here and above. *)
      | Constr.Prod (_,p,q) when not (Termops.dependent (Constr.mkRel 1) q) ->
        A.imply (term_of_coq subst p) (term_of_coq subst q)
      | Constr.Prod (_,a,f) when Constr.equal f Coq.false_ ->
        (* [a -> false] becomes [not a] *)
        A.not_ (term_of_coq subst a)
      | Constr.Prod _ -> failwith "TODO: term_of_coq: Prod"
      (* /Propositional connectives *)
      (* simply-typed λ-calculus *)
      | Constr.Lambda (x,t,u) ->
        let subst = push_fresh x subst in
        let x = List.hd subst in
        A.fun_ (x, simple_type_of_coq subst t) (term_of_coq subst u)
      | Constr.App (x, args) ->
        A.app (term_of_coq subst x) Array.(map (term_of_coq subst) args |> to_list)
      | Constr.Rel n -> A.var @@ List.nth subst (n-1)
      (* Misc *)
      | Constr.LetIn _ -> failwith "TODO: term_of_coq: LetIn"
      | Constr.Cast _ -> failwith "TODO: term_of_coq: Cast"
      (* Hypotheses *)
      | Constr.Var _ -> failwith "TODO: term_of_coq: Var"
      (* Toplevel definitions *)
      | Constr.Const (cn,_) ->
        constants := cn :: !constants;
        A.var (id_of_const cn)
      | Constr.Ind _ -> failwith "TODO: term_of_coq: Ind"
      | Constr.Construct _ -> failwith "TODO: term_of_coq: Construct"
      (* Pattern Matching & fixed points *)
      | Constr.Case _ -> failwith "TODO: term_of_coq: Case"
      | Constr.Fix _ -> failwith "TODO: term_of_coq: Fix"
      | Constr.CoFix _ -> failwith "TODO: term_of_coq: CoFix"
      | Constr.Proj _ -> failwith "TODO: term_of_coq: Proj"
      (* Not supported *)
      | Constr.Meta _ -> failwith "Metas not supported"
      | Constr.Evar _ -> failwith "Evars not supported"
      (* Types *)
      | Constr.Sort (Sorts.Prop _) -> A.ty_prop
      | Constr.Sort (Sorts.Type _) ->
        failwith "TODO: term_of_coq: Sort" (* should not occur in terms for now *)
    in
    let new_t = term_of_coq [] t in
    new_t, !constants

  (* recover the statement defining/declaring [l] *)
  let fetch_def_of_label env (c:Names.constant): Ast.statement * Names.constant list =
    Log.outputf Feedback.Debug "fetch_def_of_label %s@."
      (Names.Constant.to_string c);
    let decl = Environ.lookup_constant c env in
    Log.outputf Feedback.Debug "stmt_of_decl @.";
    (* convert type *)
    let ty = match decl.Declarations.const_type with
      | Declarations.RegularArity ty -> ty
      | Declarations.TemplateArity _ -> failwith "TODO: stmt_of_decl: TemplateArity"
    in
    let ty, new_consts = term_of_coq ty in
    (* convert definition (if any) *)
    let def = decl.Declarations.const_body in
    let stmt, new_consts' = match def with
      | Declarations.Undef _ ->
        Ast.decl ~attrs:[] (id_of_const c) ty, []
      | Declarations.Def def ->
        let t, new_consts' =
          Mod_subst.force_constr def
          |> term_of_coq
        in
        Ast.def (id_of_const c) t, new_consts'
      | Declarations.OpaqueDef _ -> 
        Ast.axiom [Ast.true_], [] (* TODO *)
    in
    stmt, List.rev_append new_consts new_consts'

  (* main state for recursively gathering definitions + axioms *)
  type state = {
    env: Environ.env;
    (* global environment *)
    mutable processed: Names.Cset.t;
    (* set of already processed names *)
    mutable new_stmts: Ast.statement list;
    (* new statements, reversed *)
  }

  let create_state env =
    { env;
      processed=Names.Cset.empty;
      new_stmts=[];
    }

  (* recursively recover all dependencies from the given names *)
  let gather_deps env (root_constants: Names.constant list): Ast.statement list =
    let state = create_state env in
    (* recursive traversal, DFS, to enforce proper ordering of
       statements (i.e. definitions precede their use) *)
    let rec explore (c:Names.constant): unit =
      if not (Names.Cset.mem c state.processed) then (
        state.processed <- Names.Cset.add c state.processed;
        let stmt, deps = fetch_def_of_label state.env c in
        (* first, explore dependencies *)
        List.iter explore deps;
        (* then only we can push the new statement *)
        state.new_stmts <- stmt :: state.new_stmts;
      )
    in
    List.iter explore root_constants;
    List.rev state.new_stmts

  let problem_of_goal (g:([`NF],_) PV.Goal.t) : Ast.problem =
    let concl = PV.Goal.concl g in
    let env = PV.Goal.env g in
    let hyps =
      PV.Goal.hyps g
      |> List.map
        (function
          | Context.Named.Declaration.LocalAssum (_,ty)
          | Context.Named.Declaration.LocalDef (_,_,ty) -> ty)
    in
    (* call this handy function to get all dependencies *)
    (* let set, map, map2 = *)
    (*   Assumptions.traverse (Names.Label.make "Top") g_term *)
    (* in *)
    (* Log.outputf "@[<2>get_problem:@ @[%a@]@]" pp_raw_traverse (set,map,map2); *)
    (* FIXME?
    let ctxmap =
      Assumptions.assumptions ~add_opaque:true ~add_transparent:true
        Names.full_transparent_state
        (Globnames.global_of_constr g_term) g_term
    in
    Log.outputf "@[<2>ctxmap: %a@]" pp_ctxmap ctxmap;
    *)
    let concl, cs_list = term_of_coq concl in
    let cs_list, hyps =
      Util.List.fold_map
        (fun cs_list t ->
           let t', cs_list' = term_of_coq t in
           cs_list' @ cs_list, t')
        cs_list hyps
    in
    let goal =
      match hyps with
        | [] -> Ast.not_ concl
        | hyps -> Ast.(not_ @@ imply (and_ hyps) concl)
    in
    (* pull dependencies (axioms and definitions) recursively *)
    let decls = gather_deps env cs_list in
    decls @ [Ast.goal goal]
end

exception Nunchaku_counter_ex of string

module N = PV.NonLogical

(* mode of operation *)
type mode =
  | M_fail
  | M_warn

module Solve : sig
  type res =
    | Check_ok
    | Counter_ex of string
    | Unknown of string
    | Check_error of string

  val call : Ast.problem -> (res * log_msg list) N.t
  (** Call nunchaku on the given problem *)

  val return_res : mode -> (res * log_msg list)-> unit PV.tactic
  (** Return the result to Coq *)

  val timeout : int ref

  val tactic : mode:mode -> Ast.problem -> unit PV.tactic
  (** The whole tactic *)
end = struct
  type res =
    | Check_ok
    | Counter_ex of string
    | Unknown of string
    | Check_error of string

  let print_problem out (pb:Ast.problem): unit =
    Format.fprintf out "@[<v>%a@]@." Ast.pp_statement_list pb

  module Sexp = Nunchaku_coq_sexp

  let parse_res ~stdout (sexp:Sexp.t): res = match sexp with
    | `Atom "UNSAT" -> Check_ok
    | `Atom "TIMEOUT" -> Unknown ("timeout\n" ^ stdout)
    | `Atom "UNKNOWN" -> Unknown ("unknown\n" ^ stdout)
    | `List [`Atom "SAT"; _model] ->
      (* TODO: parse model *)
      Counter_ex stdout
    | _ ->
      failwith ("could not parse Nunchaku's output\noutput:\n" ^ stdout)

  let timeout = 10

  let call_ pb : res * log_msg list =
    let cmd = Printf.sprintf "nunchaku -o sexp -i nunchaku -nc -t %d 2>&1" timeout in
    let res =
      U.IO.popen cmd
        ~f:(fun (oc,ic) ->
          let input = Format.asprintf "%a@." print_problem pb in
          Log.outputf Feedback.Debug "@[<v>nunchaku input:@ `%s`@]@." input;
          output_string oc input;
          flush oc; close_out oc;
          (* now read Nunchaku's output *)
          try
            let out = U.IO.read_all ic in
            Log.outputf Feedback.Debug "@[<v>nunchaku output:@ `%s`@]@." out;
            if out="" then Check_error "empty output from Nunchaku"
            else begin match Nunchaku_coq_sexp.parse_string out with
              | Ok sexp -> parse_res ~stdout:out sexp
              | Error msg -> Check_error msg
            end
          with e ->
            Check_error (Printexc.to_string e)
        ) |> fst
    in
    let logs = Log.pop_logs () in
    res, logs

  let call pb = N.make (fun () -> call_ pb)

  let pp_msg (l,s) = match l with
    | Feedback.Info -> N.print_info s
    | Feedback.Error -> N.print_error s
    | Feedback.Warning -> N.print_warning s
    | Feedback.Debug -> N.print_debug s
    | Feedback.Notice -> N.print_notice s

  let pp_msgs l = N.List.iter pp_msg l

  let return_res mode (res,msgs) =
    let main =  match res with
      | Check_ok -> PV.tclUNIT ()
      | Unknown str ->
        PV.tclTHEN
          (PV.tclLIFT (N.print_debug (Pp.str "nunchaku returned `unknown`")))
          (PV.tclUNIT ())
      | Check_error s ->
        PV.V82.tactic
          (Tacticals.tclFAIL 0
             Pp.(str "error in nunchaku: " ++ str s))
      | Counter_ex s ->
        begin match mode with
          | M_fail -> 
            PV.V82.tactic
              (Tacticals.tclFAIL 0
                 Pp.(str "Nunchaku found a counter-example: " ++ str s))
          | M_warn ->
            (* just a warning *)
            PV.tclTHEN
              (PV.tclLIFT
                 (N.print_warning
                    Pp.(str "Nunchaku found a counter-example: " ++ str s)))
              (PV.tclUNIT ())
        end
    in
    PV.tclTHEN
      (PV.tclLIFT (N.List.iter pp_msg msgs))
      main

  let timeout : int ref = ref 10

  (*
    (fun (e,_) ->
       let err_msg =
         Pp.(str "error when running nunchaku: " ++ str (Printexc.to_string e))
       in
       N.print_error err_msg)
   *)

  let tactic ~mode pb =
    let t1 = N.timeout !timeout (call pb) in
    PV.tclBIND
      (PV.tclLIFT t1)
      (return_res mode)
end

let call ~(mode:mode) (): unit PV.tactic =
  PV.Goal.nf_enter
    {PV.Goal.enter=fun g ->
       (*PV.tclLIFT (N.print_debug (Pp.str ("extract from goal: " ^ Prettyp.default_object_pr.Prettyp. *)
       let pb = Extract.problem_of_goal g in
       Solve.tactic ~mode pb}
