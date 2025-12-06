(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(* File initially created by Christine Paulin, 1996 *)

(* This file builds various inductive schemes *)

open Pp
open CErrors
open Util
open Names
open Constr
open EConstr
open Declarations
open Context
open Inductive
open Environ
open LibBinding
open State
open Retyping
open Context.Rel.Declaration

type dep_flag = bool

(* Errors related to recursors building *)
type recursion_scheme_error =
  | NotAllowedCaseAnalysis of Evd.evar_map * (*isrec:*) bool * Sorts.t * pinductive
  | NotMutualInScheme of inductive * inductive
  | DuplicateInductiveBlock of inductive
  | NotAllowedDependentAnalysis of (*isrec:*) bool * inductive

exception RecursionSchemeError of env * recursion_scheme_error

let paramdecls_fresh_template sigma (mib,u) =
  match mib.mind_template with
  | None ->
    let params = Inductive.inductive_paramdecls (mib, EConstr.Unsafe.to_instance u) in
    sigma, EConstr.of_rel_context params
  | Some templ ->
    assert (EConstr.EInstance.is_empty u);
    let sigma, univs = List.fold_left_map (fun sigma -> function
        | None -> sigma, (fun ~default -> assert false)
        | Some s ->
          let sigma, u = match snd (Inductive.Template.bind_kind s) with
            | None -> sigma, Univ.Universe.type0
            | Some _ ->
              let sigma, u = Evd.new_univ_level_variable UState.univ_rigid sigma in
              sigma, Univ.Universe.make u
          in
          sigma, fun ~default -> Inductive.TemplateUniv u)
        sigma
        templ.template_param_arguments
    in
    let csts, params, _ = Inductive.instantiate_template_universes mib univs in
    let sigma = Evd.add_poly_constraints QGraph.Internal sigma csts in
    sigma, EConstr.of_rel_context params

(* ************************************************************************** *)
(*                              Generate Recursors                            *)
(* ************************************************************************** *)

let (let@) x f = x f
let (let*) x f = fun s -> let a = x s in f a s

type elim_info = int * one_inductive_body * bool * Evd.esorts

let dbg = CDebug.create ~name:"generate_recursors" ()

(* ************************************************************************** *)
(*                              View Argument                                 *)
(* ************************************************************************** *)

type arg =
  (* pos_ind, constant context, inst_nuparams inst_indices *)
  | ArgIsInd of int * rel_context * constr array * constr array
  (* constant context, hd, args (maybe empty) *)
  | ArgIsCst of rel_context * constr * constr array

(** Decompose the argument in [it_Prod_or_LetIn local, X] where [X] is Ind, nested or a constant *)
let view_arg kname mdecl t : arg State.t =
  let* env = get_env in
  let* sigma = get_sigma in
  let (cxt, hd) = Reductionops.whd_decompose_prod_decls env sigma t in
  let (hd, iargs) = decompose_app sigma hd in
  match kind sigma hd with
  (* If it is nested *)
  | Ind ((kname_indb, pos_indb), _) ->
    (* If it is the inductive *)
    if kname = kname_indb
    then let (_, local_nuparams_indices) = Array.chop mdecl.mind_nparams_rec iargs in
         let (local_nuparams, local_indices) = Array.chop (mdecl.mind_nparams - mdecl.mind_nparams_rec) local_nuparams_indices in
         return @@ ArgIsInd (pos_indb, cxt, local_nuparams, local_indices)
    (* 2.2 If it is nested *)
    else if Array.length iargs = 0 then return @@ ArgIsCst (cxt, hd, iargs)
    else begin
      (* NESTED NOT TREATED FOR THE MOMENT *)
      return @@ ArgIsCst (cxt, hd, iargs)
      end
  | _ -> return @@ ArgIsCst (cxt, hd, iargs)

(* seperate uparams and nuparams *)
let chop_letin n l =
  let rec goto i acc = function
    | h :: t ->
      begin match h with
      | LocalAssum _ -> if Int.equal i 0 then (List.rev acc, h::t) else goto (pred i) (h :: acc) t
      | LocalDef _ -> goto i (h :: acc) t
      end
    | [] -> if Int.equal i 0 then (List.rev acc, []) else failwith "goto"
  in
  goto n [] l

(** Generalize parameters for template and univ poly, and split uniform and non-uniform parameters *)
let get_params_sep sigma mdecl u =
  let (sigma, up_params) = paramdecls_fresh_template sigma (mdecl, u) in
  let (uparams, nuparams) = chop_letin mdecl.mind_nparams_rec @@ List.rev up_params in
  (sigma, List.rev uparams, List.rev nuparams)

(** Closure of uniform parameters forgetting letins *)
let closure_uparams binder naming_scheme uparams cc =
  closure_context_sep binder Old naming_scheme uparams (fun (x,_,_) -> cc x)

(** Closure of non-uniform parameters if [b], forgetting letins  *)
let closure_nuparams_opt b binder naming_scheme nuparams =
    if b
    then fun cc -> closure_context_sep binder Old naming_scheme nuparams (fun (x,_,_) -> cc (Some x))
    else fun cc -> cc None

(** Closure of non-uniform parameters if [key_uparams_opt = None], forgetting letins  *)
let closure_nuparams binder naming_scheme nuparams key_uparams_opt cc =
  let@ key_uparams_opt' = closure_nuparams_opt (Option.is_empty key_uparams_opt) binder naming_scheme nuparams in
  match key_uparams_opt, key_uparams_opt' with
  | Some z, None | None, Some z -> cc z
  | _, _ -> assert false

(** get the position in ind_bodies out of the position of mind_packets *)
let find_opt_pos p l =
  let rec aux i l = match l with
  | [] -> None
  | h::_ when p h -> Some (i, h)
  | _::t -> aux (1+i) t
  in aux 0 l

(** Compute relevance of an inductive block *)
let ind_relevance ind u = ERelevance.make @@ relevance_of_ind_body ind (EConstr.Unsafe.to_instance u)

(** Closure for indices. They are considered as [Fresh] as tey are not in the context of the arguments *)
let closure_indices binder naming_scheme indb u f =
  let* i = get_indices indb u in
  closure_context_sep binder Fresh naming_scheme i f

(* Convention for comments:
  - A1 ... An : uniform parameters = uparams
  - B0 ... Bm : non-uniform parameters = nuparams
  - i0 ... il : indices
*)

(** Builds the type of the predicate for the i-th block
    forall (B0 ... Bm : nuparams),
    forall (i1 ... tl : indices),
    (Ind A1 ... An B0 ... Bm i1 ... il) -> U)  *)
let make_type_pred kn u (pos_ind, ind, dep, sort) key_uparams nuparams key_nuparams_opt =
  let@ key_nuparams = closure_nuparams Prod naming_hd_fresh nuparams key_nuparams_opt in
  let@ (key_indices , _, _) = closure_indices  Prod (naming_hd_fresh_dep dep) ind u in
  (* NOT DEP: return the sort *)
  if not dep then return  @@ mkSort sort else
  (* DEP: bind the inductive, and return the sort *)
  let name_ind = make_annot Anonymous (ind_relevance ind u) in
  let* tind = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ _ = make_binder Prod naming_hd_fresh name_ind tind in
  return @@ mkSort sort

(** Closure Predicates *)
let closure_preds kn u ind_bodies binder key_uparams nuparams key_nuparams_opt cc =
  fold_right_state (fun a l -> a :: l) ind_bodies (fun _ ind cc ->
    let name_pred = make_annot (Name (Id.of_string "P")) ERelevance.relevant in
    let* ty_pred = make_type_pred kn u ind key_uparams nuparams key_nuparams_opt in
    make_binder binder naming_hd_fresh name_pred ty_pred cc
  ) cc

 (** Make the predicate P B0 ... Bm i0 ... il t *)
let make_pred rec_hyp key_preds focus dep inst_nuparams inst_indices t =
  let* z = geti_term key_preds focus in
  let pred =
    if rec_hyp
    then mkApp (z, Array.concat [inst_nuparams; inst_indices])
    else mkApp (z, inst_indices) in
  if not dep then return pred else
  return @@ mkApp (pred, [| t |])

(** Compute the type of the recursive call *)
let make_rec_call kn mdecl ind_bodies key_preds key_arg ty =
  let* v = view_arg kn mdecl ty in
  match v with
  | ArgIsInd (pos_ind_block, loc, inst_nuparams, inst_indices) -> begin
      (* generate recursion hypotheses only for the blocks that are used *)
      match find_opt_pos (fun (i,_,_,_) -> i = pos_ind_block) ind_bodies with
      | None -> return None
      | Some (pred_pos, (_, _, pred_dep, sort)) -> return @@
      Some (
        relevance_of_sort sort,
        (* Pi B0 ... Bm i0 ... il (x a0 ... an) *)
        let@ (key_locals, _, _) = closure_context_sep Prod Fresh naming_id loc in
        let* arg = get_term key_arg in
        let* loc = get_terms key_locals in
        let arg = mkApp (arg , Array.of_list loc) in
        make_pred true key_preds pred_pos pred_dep inst_nuparams inst_indices arg
      )
    end
  | _ -> return None

(** Create and bind the recursive call, if [rec_hyp] and if any *)
let make_rec_call_cc rec_hyp kn mdecl ind_bodies key_preds _ key_arg cc =
  let* arg = LibBinding.State.get_type key_arg in
  if rec_hyp then
    let* rec_call = make_rec_call kn mdecl ind_bodies key_preds key_arg arg in
    match rec_call with
    | Some (rec_hyp_rev, rec_hyp_ty) ->
        let name_rec_hyp = make_annot Anonymous rec_hyp_rev in
        let* rec_hyp_ty = rec_hyp_ty in
        let@ _ = make_binder Prod naming_id name_rec_hyp rec_hyp_ty in
        cc [key_arg]
    | _ -> cc [key_arg]
  else cc [key_arg]

(** Closure of the args, and of the rec call if [rec_hyp], and if any *)
let closure_args_and_rec_call rec_hyp kn u mdecl ind_bodies dep key_preds args =
  read_by_decl args
    (build_binder Prod Old (naming_hd_dep dep))
    (fun _ _ cc -> cc [])
    (make_rec_call_cc rec_hyp kn mdecl ind_bodies key_preds)

(** Generates the type associated to a constructor
    forall (B0 ... Bm : nuparams),
    forall x0 : arg0, [P x0], ..., xn : argn, [P n],
    P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
let make_type_ctor kn u mdecl ind_bodies pos_list (pos_ind, ind, dep, sort) pos_ctor (args, indices) key_uparams nuparams key_nuparams_opt key_preds =
  let rec_hyp = Option.is_empty key_nuparams_opt in
  let@ key_nuparams = closure_nuparams Prod naming_id nuparams key_nuparams_opt in
  let@ key_args = closure_args_and_rec_call rec_hyp kn u mdecl ind_bodies dep key_preds args in
  (* make cst *)
  let* k = get_terms key_args in
  let* cst = make_cst ((kn, pos_ind), u) pos_ctor key_uparams key_nuparams k in
  (* make pred cst *)
  let* inst_nuparams = get_terms key_nuparams in
  let* state = get_state in
  let weaken a = weaken a state in
  let inst_indices = Array.map weaken indices in
  make_pred rec_hyp key_preds pos_list dep (Array.of_list inst_nuparams) inst_indices cst

(** Closure assumptions functions over all the ctors *)
let closure_ctors rec_hyp kn mdecl u ind_bodies binder key_uparams nuparams key_nuparams_opt key_preds =
  fold_right_state (fun a l -> a :: l) ind_bodies (
    fun pos_list (pos_ind, ind, dep, sort) cc ->
    iterate_ctors mdecl ind u (
      fun pos_ctor ctor cc ->
      let name_assumption = make_annot (Name ind.mind_consnames.(pos_ctor)) (relevance_of_sort sort) in
      let* fct = make_type_ctor kn u mdecl ind_bodies pos_list (pos_ind, ind, dep, sort) pos_ctor ctor key_uparams nuparams key_nuparams_opt key_preds in
      make_binder binder naming_hd_fresh name_assumption fct cc
    ) cc
  )

(** Make the type of the conclusion
    P B0 ... Bm i0 ... il x *)
let make_ccl rec_hyp key_preds focus dep key_nuparams key_indices key_VarMatch =
  let* x = get_terms key_nuparams in
  let* y = get_terms key_indices in
  let* var = get_term key_VarMatch in
  make_pred rec_hyp key_preds focus dep (Array.of_list x) (Array.of_list y) var

(** Make the return type
    forall (B0 ... Bm : nuparams),
    forall (i1 ... il : indices),
    forall (x : Ind A0 ... An B0 ... Bm i0 ... il),
    P B0 ... Bm i0 ... il x *)
let make_return_type kn u ind_bodies focus key_uparams nuparams key_nuparams_opt key_preds =
  let (pos_ind, ind, dep, sort) = List.nth ind_bodies focus in
  let@ key_nuparams = closure_nuparams Prod naming_hd_fresh nuparams key_nuparams_opt in
  let@ (key_indices , _, _) = closure_indices Prod naming_hd_fresh ind u in
  let name_ind = make_annot Anonymous (ind_relevance ind u) in
  let* tind = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ (key_VarMatch) = make_binder Prod naming_hd_fresh name_ind tind in
  let rec_hyp = Option.is_empty key_nuparams_opt in
  make_ccl rec_hyp key_preds focus dep key_nuparams key_indices key_VarMatch

(** Generate the type of the recursor, useful for debugging *)
let gen_elim_type print_constr rec_hyp env sigma kn u mdecl uparams nuparams (ind_bodies : elim_info list) (focus : int) =

  dbg Pp.(fun () -> str "\n------------------------------------------------------------- \n"
    ++ str (MutInd.to_string kn) ++ str " ## pos_ind = " ++ int focus
    ++ str " ## rec_hyp = " ++ bool rec_hyp ++ str "\n") ;

  let t =
    let@ key_uparams = closure_uparams Prod naming_hd_fresh uparams in
    let@ key_nuparams_opt = closure_nuparams_opt (not rec_hyp) Prod naming_hd_fresh nuparams in
    let@ key_preds = closure_preds kn u ind_bodies Prod key_uparams nuparams key_nuparams_opt in
    let@ key_ctors = closure_ctors rec_hyp kn mdecl u ind_bodies Prod key_uparams nuparams key_nuparams_opt key_preds in
    make_return_type kn u ind_bodies focus key_uparams nuparams key_nuparams_opt key_preds
  in
  let x = t @@ State.make env sigma in
  dbg Pp.(fun () -> print_constr env sigma x ++ str "\n");
  x

(** Compute the recursive call *)
let make_rec_call kn mdecl ind_bodies key_fixs key_arg ty : ((constr State.t) option) State.t =
  let* v = view_arg kn mdecl ty in
  match v with
  | ArgIsInd (pos_ind_block, loc, inst_nuparams, inst_indices) -> begin
    (* generate recursion hypotheses only for the blocks that are used *)
      match find_opt_pos (fun (i,_,_,_) -> i = pos_ind_block) ind_bodies with
      | None -> return None
      | Some (pred_pos, _) ->
      return @@ Some (
        (* Fi B0 ... Bm i0 ... il (x a0 ... an) *)
        let@ (key_locals, _, _) = closure_context_sep Lambda Fresh naming_id loc in
        let* kpos = geti_term key_fixs pred_pos in
        let fix = mkApp (kpos, (Array.append inst_nuparams inst_indices)) in
        let* karg = get_term key_arg in
        let* kloc = get_terms key_locals in
        let arg = mkApp (karg, Array.of_list kloc) in
        return @@ mkApp (fix, [| arg |])
      )
    end
  | _ -> return None

(** Compute the arguments of the rec call *)
let compute_args_fix kn mdecl ind_bodies pos_list key_fixs key_args =
  CList.fold_right_i (fun pos_arg key_arg t ->
    let* karg = LibBinding.State.get_type key_arg in
    let* rec_call = make_rec_call kn mdecl ind_bodies key_fixs key_arg karg in
    let* karg' = get_term key_arg in
    let* t = t in
    match rec_call with
      | Some rc_tm -> let* rc_tm = rc_tm in
                return @@ karg' :: rc_tm :: t
      | None -> return @@ karg' :: t
  ) 0 key_args (return [])

let gen_elim_term print_constr (rec_hyp : bool) env sigma kn u mdecl uparams nuparams (ind_bodies : elim_info list) (focus : int) =

  let t =

  (* 1. Closure Uparams / preds / ctors *)
  let@ key_uparams = closure_uparams Lambda naming_hd_fresh uparams in
  let@ key_nuparams_opt = closure_nuparams_opt (not rec_hyp) Lambda naming_hd_fresh nuparams in
  let@ key_preds = closure_preds kn u ind_bodies Lambda key_uparams nuparams key_nuparams_opt in
  let@ key_ctors = closure_ctors rec_hyp kn mdecl u ind_bodies Lambda key_uparams nuparams key_nuparams_opt key_preds in
  (* 2. Fixpoint *)
  let fix_name pos_list (_,_,_,sort) = make_annot (Name (Id.of_string "F")) (relevance_of_sort sort) in
  let fix_type pos_list _ = make_return_type kn u ind_bodies pos_list key_uparams nuparams key_nuparams_opt key_preds in
  let fix_rarg pos_list (_,ind,_,_) = (mdecl.mind_nparams - mdecl.mind_nparams_rec) + ind.mind_nrealargs in
  let is_rec = let (_, ind, _, _) = List.hd ind_bodies in
    List.length ind_bodies > 1 ||
    (rec_hyp && Inductiveops.mis_is_recursive env ((kn, focus), mdecl, ind)) in
  let@ (key_fixs, pos_list, (pos_ind, ind, dep, sort)) =
    (* Doe not create a fix if it is not-recursive and only has one inductive body *)
    if is_rec
    then make_fix ind_bodies focus fix_rarg fix_name fix_type
    else fun cc -> cc ([], 0, List.hd ind_bodies) in
  (* 3. Closure Nuparams / Indices / Var *)
  let@ key_nuparams = closure_nuparams Lambda naming_hd_fresh nuparams key_nuparams_opt in
  let@ (key_indices , _, _) = closure_indices Lambda naming_hd_fresh ind u in
  let name_ind = make_annot Anonymous (ind_relevance ind u) in
  let* tind = make_ind ((kn, pos_ind), u) key_uparams key_nuparams key_indices in
  let@ key_VarMatch = make_binder Lambda naming_hd_fresh name_ind tind in
  let ccl =
  (* 4 Match to prove P ... x *)
    let* xup = get_terms key_uparams in
    let* xnup = get_terms key_nuparams in
    let params = Array.of_list (xup @ xnup) in
    let case_pred = make_ccl rec_hyp key_preds pos_list dep key_nuparams in
    let* xmatch = get_term key_VarMatch in
    let* xind = get_terms key_indices in
    let@ (key_args, _, _, pos_ctor) =
      make_case_or_projections naming_hd_fresh mdecl (kn, pos_ind) ind u key_uparams key_nuparams params
        xind case_pred (relevance_of_sort sort) (xmatch) in
    (* 5 Body of the branch *)
    let* hyp = getij_term key_ctors pos_list pos_ctor in
    let* xnup = get_terms key_nuparams in
    if rec_hyp
    (* REC: apply to nuparams + args + rec call *)
    then let* cfix = compute_args_fix kn mdecl ind_bodies pos_list key_fixs key_args in
          return @@ mkApp (hyp, Array.of_list (xnup @ cfix))
    (* NOT REC : apply to args *)
    else let* args = get_terms key_args in
          return @@ mkApp (hyp, Array.of_list args)

  in
  (* 6. If it is not-recursive, has primitive projections and is dependent => add a cast *)
  let* env = get_env in
  let projs = Environ.get_projections env (kn, pos_ind) in
  if is_rec || Option.is_empty projs || not dep then ccl else
  let* ty = make_ccl rec_hyp key_preds pos_list dep key_nuparams key_indices key_VarMatch in
  let* ccl = ccl in
  return @@ mkCast (ccl, DEFAULTcast, ty)

  in
  let t = t @@ State.make env sigma in
  dbg Pp.(fun () -> print_constr env sigma t ++ str "\n");
  t


(**********************************************************************)
(* build the eliminators mutual and individual *)

(** Check all dependent eliminations are allowed *)
let check_valid_elimination env sigma (kn, n) mib u lrecspec =
  (* Check the mutual can be eliminated. *)
  if mib.mind_private = Some true
  then user_err (str "case analysis on a private inductive type is not allowed");
  (* Check all the blocks can be eliminated *)
  List.iter (fun ((kni, ni),dep,s) ->
    (* Check that all the blocks can be eliminated to s *)
    if not @@ Inductiveops.is_allowed_elimination sigma ((mib,mib.mind_packets.(ni)),u) s
    then raise (RecursionSchemeError (env, NotAllowedCaseAnalysis (sigma, true, ESorts.kind sigma s, ((kn, ni), EInstance.kind sigma u))));
    (* Check if dep elim is allowed: rec (co)ind records with prim proj can not be eliminated dependently *)
    if dep && not (Inductiveops.has_dependent_elim (mib, mib.mind_packets.(ni)))
    then raise (RecursionSchemeError (env, NotAllowedDependentAnalysis (true, (kni, ni))));
  ) lrecspec

(** Check all the blocks are mutual, and not given twice *)
let check_valid_mutual env sigma (kn, n) mib u lrecspec =
  let _ : int list =
    List.fold_left (fun ln ((kni, ni),dep,s) ->
        (* Check all the blocks are mutual  *)
        if not (QMutInd.equal env kn kni)
        then raise (RecursionSchemeError (env, NotMutualInScheme ((kn, n),(kni, ni))));
        (* Check none is given twice *)
        if Int.List.mem ni ln
        then raise (RecursionSchemeError (env, DuplicateInductiveBlock (kn, ni)))
        else ni::ln)
      [n] lrecspec
  in
  ()

let build_mutual_induction_scheme_gen rec_hyp env sigma lrecspec u =
  match lrecspec with
  | (mind,dep,s)::tail ->
      let mib, mip = lookup_mind_specif env mind in
      (* Check the blocks are all mutual, different, and can be eliminated dependently *)
      let () = check_valid_mutual env sigma mind mib u tail in
      let () = check_valid_elimination env sigma mind mib u lrecspec in
      (* Compute values for gen_elim *)
      let listdepkind = (snd mind, mip, dep, s) :: List.map (fun ((_,ni), dep, s) -> (ni, mib.mind_packets.(ni), dep, s)) tail in
      (* Get parameters, and generalized them for UnivPoly + TemplatePoly *)
      let (sigma, uparams, nuparams) = get_params_sep sigma mib u in
      (* Compute eliminators' types and terms *)
      let recs_ty = List.init (List.length listdepkind)
        (gen_elim_type Termops.Internal.print_constr_env rec_hyp env sigma (fst mind) u mib uparams nuparams listdepkind) in
      let recs_tm = List.init (List.length listdepkind)
        (gen_elim_term Termops.Internal.print_constr_env rec_hyp env sigma (fst mind) u mib uparams nuparams listdepkind) in
      (sigma, recs_ty, recs_tm)
  | _ -> anomaly (Pp.str "build_mutual_induction_scheme expects a non empty list of inductive types.")

let build_mutual_induction_scheme env sigma ?(force_mutual=false) lrecspec u =
  let (sigma, _, recs_tm) = build_mutual_induction_scheme_gen true env sigma lrecspec u in
  sigma, recs_tm

let build_induction_scheme env sigma (ind, u) dep kind =
  let (sigma, _, recs_tm) = build_mutual_induction_scheme_gen true env sigma [(ind, dep, kind)] u in
  (sigma, List.hd recs_tm)

let build_case_analysis_scheme env sigma (ind, u) dep kind =
  let (sigma, recs_ty, recs_tm) = build_mutual_induction_scheme_gen false env sigma [(ind, dep, kind)] u in
  (sigma, List.hd recs_tm, List.hd recs_ty)
