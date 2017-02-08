
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

  let id_of_id (id:Names.Id.t) : Ast.Nun_id.t =
    id |> Names.Id.to_string |> Ast.Nun_id.of_string

  let id_of_minds (m:Names.MutInd.t): Ast.Nun_id.t =
    Names.MutInd.to_string m |> Ast.Nun_id.of_string

  type deps = {
    dep_consts: Names.constant list;
    dep_minds: Names.mutual_inductive list;
  }

  let dep_empty = {
    dep_consts=[];
    dep_minds=[];
  }

  let dep_add_cn c deps = {deps with dep_consts=c::deps.dep_consts}
  let dep_add_mind x deps = {deps with dep_minds=x::deps.dep_minds}

  let dep_merge a b = {
    dep_consts=a.dep_consts@b.dep_consts;
    dep_minds=a.dep_minds@b.dep_minds;
  }

  (* Convert [t] into a simple type in Nunchaku syntax, and return the
     list of constant occurring in [ty]. *)
  let simple_type_of_coq (subst:Ast.id list) (t:coq_term) : Ast.ty * deps=
    let module A = Ast in
    let deps : deps ref = ref dep_empty in
    let rec simple_type_of_coq subst t =
      match Constr.kind t with
      | Constr.Sort (Sorts.Prop _) -> A.ty_prop
      | Constr.Sort (Sorts.Type _) -> A.ty_type
      | Constr.Prod (_,a,b) when not (Termops.dependent (Constr.mkRel 1) b) ->
        (* A dummy value is inserted as a way to shift the
           substitution, as [b] is technically in the scope a new
           variable (even though it doesn't depend on it).*)
        let dummy = A.Nun_id.of_string "dummy" in
        A.ty_arrow (simple_type_of_coq subst a) (simple_type_of_coq (dummy::subst) b)
      | Constr.Prod _ -> failwith "simple_type_of_coq: dependent type"
      | Constr.Const (cn,_) ->
        deps := dep_add_cn cn !deps;
        A.var (id_of_const cn)
      | Constr.Rel n -> A.var @@ List.nth subst (n-1)
      | Constr.App (x,args) ->
        A.app (simple_type_of_coq subst x) Array.(map (simple_type_of_coq subst) args |> to_list)
      | _ -> assert false
    in
    let ty = simple_type_of_coq subst t in
    ty , !deps

  (* convert [t] into a Nunchaku term, and return the list of constants
     occurring in [t] *)
  let term_of_coq (env:Environ.env) (t:coq_term) : Ast.term * deps =
    let module A = Ast in
    let deps : deps ref = ref dep_empty in
    (* adds a fresh (in subst) identifier based on [x] as the 0-th
       element of subst. *)
    (* TODO: subst should probably be a map. *)
    let push_fresh (x:Names.Name.t) (subst:Ast.id list) : Ast.id list =
      let x = Ast.Nun_id.of_coq_name x in
      let fresh = Ast.Nun_id.fresh x (Ast.Nun_id.Set.of_list subst) in
      fresh::subst
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
        let (ty,deps') = simple_type_of_coq subst t in
        let () = deps := deps' in
        A.fun_ (x, ty) (term_of_coq subst u)
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
        deps := dep_add_cn cn !deps;
        A.var (id_of_const cn)
      | Constr.Ind ((m_inds,i_ind),_univ) ->
        (* i-th inductive of [m_inds] *)
        deps := dep_add_mind m_inds !deps;
        Log.outputf Feedback.Debug
          "term_of_coq: Ind (%s,%d)" (Names.MutInd.to_string m_inds) i_ind;
        A.var (id_of_minds m_inds)
      | Constr.Construct (((m_inds,i_ind),i_cstor), _univ) ->
        (* i-th cstor of ind *)
        deps := dep_add_mind m_inds !deps;
        Log.outputf Feedback.Debug
          "term_of_coq: Construct (%s,%d,%d)"
          (Names.MutInd.to_string m_inds) i_ind i_cstor;
        let mind = Environ.lookup_mind m_inds env in
        (* /!\ inductives are numbered from 0 while their constructors are
           numbered from 1. *)
        let ind = mind.Declarations.mind_packets.(i_ind) in
        A.var (id_of_id (ind.Declarations.mind_consnames.(i_cstor-1)))
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
    new_t, !deps

  (* recover the statement defining/declaring [l] *)
  let fetch_def_of_label env (c:Names.constant): Ast.statement * deps =
    Log.outputf Feedback.Debug "fetch_def_of_label %s@."
      (Names.Constant.to_string c);
    let decl = Environ.lookup_constant c env in
    Log.outputf Feedback.Debug "stmt_of_decl @.";
    (* convert type *)
    let ty = match decl.Declarations.const_type with
      | Declarations.RegularArity ty -> ty
      | Declarations.TemplateArity _ -> failwith "TODO: stmt_of_decl: TemplateArity"
    in
    let ty, new_deps = term_of_coq env ty in
    (* convert definition (if any) *)
    let def = decl.Declarations.const_body in
    let stmt, new_deps' = match def with
      | Declarations.Undef _ ->
        Ast.decl ~attrs:[] (id_of_const c) ty, dep_empty
      | Declarations.Def def ->
        let t, new_deps =
          Mod_subst.force_constr def
          |> term_of_coq env
        in
        (* TODO: if [t] is a type, use a copy instead, or just inline *)
        Ast.def (id_of_const c) t, new_deps
      | Declarations.OpaqueDef _ -> 
        Ast.axiom [Ast.true_], dep_empty (* TODO *)
    in
    stmt, dep_merge new_deps new_deps'

  (* recover the statement defining/declaring [l] *)
  let fetch_def_of_label env (c:Names.constant): Ast.statement * deps =
    Log.outputf Feedback.Debug "fetch_def_of_label %s@."
      (Names.Constant.to_string c);
    let decl = Environ.lookup_constant c env in
    (* convert type *)
    let ty = match decl.Declarations.const_type with
      | Declarations.RegularArity ty -> ty
      | Declarations.TemplateArity _ -> failwith "TODO: stmt_of_decl: TemplateArity"
    in
    let ty, new_deps = term_of_coq env ty in
    (* convert definition (if any) *)
    let def = decl.Declarations.const_body in
    let stmt, new_deps' = match def with
      | Declarations.Undef _ ->
        Ast.decl ~attrs:[] (id_of_const c) ty, dep_empty
      | Declarations.Def def ->
        let t, new_deps =
          Mod_subst.force_constr def
          |> term_of_coq env
        in
        Ast.def (id_of_const c) t, new_deps
      | Declarations.OpaqueDef _ -> 
        Ast.axiom [Ast.true_], dep_empty (* TODO *)
    in
    stmt, dep_merge new_deps new_deps'


  (* recover the statement defining the given mutual inductive type *)
  let fetch_def_of_mind env (mind:Names.mutual_inductive): Ast.statement * deps =
    Log.outputf Feedback.Debug "fetch_def_of_mind %s@."
      (Names.MutInd.to_string mind);
    let deps : deps ref = ref dep_empty in
    let rec decomp_arrow_args = function
      | { Ast.term=Ast.TyArrow (l,r)} -> l :: (decomp_arrow_args r)
      | _ -> []
    in
    (* The parameters of a constructor are represented as [Prod] in
       the constructor arity. However, we get the list of parameter
       externally, so can simply remove the leading [Prod]s given the
       list of parameter. *)
    let rec strip_params l a =
      match l , Constr.kind a with
      | _::l' , Constr.Prod (_,_,b) -> strip_params l' b
      | [] , _ -> a
      | _ , _ -> assert false
    in
    let body = Environ.lookup_mind mind env in
    let ind_names =
      Array.to_list body.Declarations.mind_packets
      |> List.map (fun ind -> id_of_id ind.Declarations.mind_typename)
    in
    let ind_l : Ast.mutual_types =
      Array.to_list body.Declarations.mind_packets
      |> List.map
        (fun ind ->
           let open Declarations in
           (* Small repetition here for simplicity *)
           let name = id_of_id ind.mind_typename in

           (* Generates a substitution corresponding to the
              parameters. The choice of name is base on what has been
              written by the used (defaults to 'a' if no name has been
              given: it would probably be better to let Coq infer the
              name in that case). The disambiguation is terribly
              conservative, it is probably desirable to have generate
              fresh name more lazily. TODO: take the opportunity to
              check that there are no unsupported features in the
              parameters as it would cause an incorrect type to be
              inferred: it's probably better to fail in that case. *)
           let param_subst =
             let string_of_name = function
               | Names.Name.Anonymous -> "a"
               | Names.Name.Name id -> Names.Id.to_string id
             in
             List.rev ind.mind_arity_ctxt
             |> List.mapi (fun i d -> Ast.Nun_id.of_string ((string_of_name (Context.Rel.Declaration.get_name d))^string_of_int i))
           in

           name ,
           param_subst ,
           let constructors =
             List.combine
               (Array.to_list ind.mind_consnames)
               (Array.to_list ind.mind_nf_lc)
           in
           constructors |> List.map (fun (id,ty) ->
               (* Remark: the name of the inductives in the
                  mutually-inductive block are represented as
                  [Rel]s. *)
               let (ty,deps') =
                 ty
                 |> strip_params param_subst
                 |> simple_type_of_coq (List.rev_append param_subst ind_names)
               in
               let () = deps := dep_merge !deps deps' in
               (id_of_id id , decomp_arrow_args ty)
           )
        )
    in
    let mk =
      match body.Declarations.mind_finite with
      | Decl_kinds.CoFinite -> Ast.codata
      | _ -> Ast.data
    in
    mk ind_l , !deps

  (* main state for recursively gathering definitions + axioms *)
  type state = {
    env: Environ.env;
    (* global environment *)
    mutable processed_consts: Names.Cset.t;
    (* set of already processed names *)
    mutable processed_minds: Names.Mindset.t;
    (* set of already processed inductive declarations *)
    mutable new_stmts: Ast.statement list;
    (* new statements, reversed *)
  }

  let create_state env =
    { env;
      processed_consts=Names.Cset.empty;
      processed_minds=Names.Mindset.empty;
      new_stmts=[];
    }

  (* recursively recover all dependencies from the given names *)
  let gather_deps env (deps:deps): Ast.statement list =
    let state = create_state env in
    (* recursive traversal, DFS, to enforce proper ordering of
       statements (i.e. definitions precede their use) *)
    let rec expand (deps:deps): unit =
      List.iter expand_const deps.dep_consts;
      List.iter expand_mind deps.dep_minds;
    and expand_const (c:Names.constant): unit =
      if not (Names.Cset.mem c state.processed_consts) then (
        state.processed_consts <- Names.Cset.add c state.processed_consts;
        let stmt, deps = fetch_def_of_label state.env c in
        (* expand sub-dependencies first *)
        expand deps;
        (* then only we can push the new statement *)
        state.new_stmts <- stmt :: state.new_stmts;
      )
    and expand_mind (mind:Names.mutual_inductive): unit =
      if not (Names.Mindset.mem mind state.processed_minds) then (
        state.processed_minds <- Names.Mindset.add mind state.processed_minds;
        let stmt, deps = fetch_def_of_mind state.env mind in
        (* expand sub-dependencies first *)
        expand deps;
        (* push new statment *)
        state.new_stmts <- stmt :: state.new_stmts;
      )
    in
    expand deps;
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
    let concl, cs_list = term_of_coq env concl in
    let cs_list, hyps =
      Util.List.fold_map
        (fun deps t ->
           let t', deps' = term_of_coq env t in
           dep_merge deps' deps, t')
        cs_list hyps
    in
    let goal = match hyps with
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
