(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Names
open Constr
open EConstr
open Environ
open Evd
open Context
open Util
open Namegen
open Declarations

module RelDecl = Rel.Declaration
open RelDecl








(* ************************************************************************** *)
(*                              View Argument                                 *)
(* ************************************************************************** *)



type arg =
  (* pos_ind, constant context, inst_nuparams inst_indices *)
  | ArgIsInd of int * rel_context * constr array * constr array
  (* ind, constant context, inst_uparams, inst_nuparams, inst_indices *)
  | ArgIsNested of inductive * rel_context * constr array * constr array * constr array
  (* constant context, hd, args (maybe empty) *)
  | ArgIsCst of rel_context * constr * constr array

(* Decompose the argument in [it_Prod_or_LetIn local, X]
  where [X] is Ind, nested or a constant *)
let view_arg kname mdecl sigma t : arg =
  let (cxt, hd) = decompose_prod_decls sigma t in
  let (hd, iargs) = decompose_app sigma hd in
  match kind sigma hd with
  (* If it is nested *)
  | Ind ((kname_indb, pos_indb), _) ->
    (* If it is the inductive *)
    if kname = kname_indb
    then let nb_uparams = mdecl.mind_nparams_rec in
         let (_, local_nuparams_indices) = Array.chop mdecl.mind_nparams_rec iargs in
         let (local_nuparams, local_indices) = Array.chop (mdecl.mind_nparams - mdecl.mind_nparams_rec) local_nuparams_indices in
         ArgIsInd (pos_indb, cxt, local_nuparams, local_indices)
    (* 2.2 If it is nested *)
    else if Array.length iargs = 0 then ArgIsCst (cxt, hd, iargs)
    else begin ArgIsCst (cxt, hd, iargs)
      (* match find (fun x => eq_constant kname_indb x.(ep_kname)) Ep with
      | Some xp ->
        (* 2.2.1 get uparams and nuparams + indices *)
        let inst_uparams = firstn xp.(ep_nb_uparams) iargs in
        let inst_nuparams_indices = skipn xp.(ep_nb_uparams) iargs in
        let inst_types = instante_types xp.(ep_type_uparams) inst_uparams in
        (* let inst_types := xp.(ep_type_uparams) in *)
        (* let inst_types := inst_uparams in *)
        VArgIsNested (xp, pos_indb, local, inst_uparams, inst_nuparams_indices, inst_types)
      | None -> VArgIsFree local hd iargs *)
      end
  | _ -> ArgIsCst (cxt, hd, iargs)


(* ************************************************************************** *)
(*                           State + fold function                            *)
(* ************************************************************************** *)


(* state *)
module State =
struct

  type state =
    { env : env;
      sigma : evar_map;
      names : Id.Set.t;
      subst : constr list;
    }

  (* make functions *)
  let make env sigma = {
    env = env;
    sigma = sigma;
    names = Id.Set.of_list @@ Termops.ids_of_rel_context @@ rel_context env;
    subst = []
  }

  let make_fresh_sigma env = {
    env = env;
    sigma = Evd.from_env env;
    names = Id.Set.of_list @@ Termops.ids_of_rel_context @@ rel_context env;
    subst = []
  }

  let state_context s = EConstr.of_rel_context @@ Environ.rel_context s.env

  (* weaken functions from the old context to the new one *)
  let weaken s c = Vars.substl s.subst c

  let weaken_rel s c = RelDecl.map_constr (weaken s) c

  let weaken_context s cxt =
    let nb_cxt = List.length cxt in
    List.mapi (fun i x ->
      let n = nb_cxt - i -1 in
      let weak x = Vars.substnl s.subst n x in
      match x with
      | LocalAssum (na, ty) -> LocalAssum (na, weak ty)
      | LocalDef (na, bd, ty) -> LocalDef (na, weak bd, weak ty)
      ) cxt

  (* Add variables to the context *)
  let add_names names decl =
    match get_name decl with
    | Anonymous -> names
    | Name id -> Id.Set.add id names

  let fresh_key s = List.length (state_context s)
  let fresh_keys s = List.init (List.length @@ state_context s) (fun i -> i)

  let push_old_rel s decl =
  let s' = { s with
      env = EConstr.push_rel (weaken_rel s decl) s.env ;
      names = add_names s.names decl;
      subst = mkRel 1 :: List.map (Vars.lift 1) s.subst
    } in
  (s', fresh_key s)

  let push_fresh_rel s decl =
    let s' = { s with
      env = EConstr.push_rel decl s.env ;
      names = add_names s.names decl;
      subst = List.map (Vars.lift 1) s.subst
    } in
  (s', fresh_key s)

  let push_subst s t = {s with
    subst = t :: List.map (Vars.lift 1) s.subst
  }

  let get_decl s key =
    let n' = List.length (state_context s) - key -1 in
    RelDecl.map_constr (Vars.lift n') (List.nth (state_context s) n')

  let getters f =
    let get_X s key = f (List.length ((state_context s)) - key -1) (get_decl s key) in

    let geti_X s keys pos_key = get_X s (List.nth keys pos_key) in

    let getij_X s keyss pos_k1 pos_k2 = get_X s (List.nth (List.nth keyss pos_k1) pos_k2) in

    let get_Xs s keys = List.map (get_X s) keys in

    (get_X, geti_X, getij_X, get_Xs)

  let get_sdecl_term =
    fun n d ->
    match RelDecl.get_value d with
    | Some tm -> Vars.lift 1 tm
    | None -> mkRel (1+n)

  let get_term, geti_term, getij_term, get_terms = getters get_sdecl_term

  let get_type, geti_type, getij_type, get_types = getters (fun _ d -> Vars.lift 1 (RelDecl.get_type d))

  let get_aname, geti_aname, getij_aname, get_anames = getters (fun _ cdecl -> RelDecl.get_annot cdecl)






  (* Print function *)
  let print_state s pretty =
    let env = s.env in
    let sigma = s.sigma in
    Format.printf "\n ************************************************************ \n";
    Format.printf "\n Print State \n";
    (* Print state *)
      Format.printf "BEGIN: State new context: \n";
      List.fold_right_i (fun i x _ ->
        Format.printf "------------------------------------------- \n";
        Format.printf "var | %n | " (List.length (Environ.rel_context s.env) - i);
        if pretty
        then Feedback.msg_info (Termops.Internal.print_constr_env s.env s.sigma (RelDecl.get_type x))
        else Feedback.msg_info (Termops.Internal.debug_print_constr s.sigma (RelDecl.get_type x))
      ) 0 (state_context s) ();
      Format.printf "END: State new context: \n";
    (* Print Substitution *)
      Format.printf "\n BEGIN: Substitution \n";
      List.fold_right (fun x _ ->
          if pretty
          then Feedback.msg_info (Termops.Internal.print_constr_env env sigma x)
          else Feedback.msg_info (Termops.Internal.debug_print_constr sigma x)
        ) s.subst ();
      Format.printf "\n END: Substitution \n"
    (* Format.printf "\n ************************************************************ \n" *)

end

open State

let ident_hd env sigma names na t =
  let na = named_hd env sigma na t in
  next_name_away na names

let set_name_rel s na ty =
  let id = ident_hd s.env s.sigma s.names ty na.binder_name in
  make_annot (Name id) na.binder_relevance

let set_names_context s l =
  let fold decl (names, l) =
    let id = ident_hd s.env s.sigma names (RelDecl.get_type decl) (RelDecl.get_name decl) in
    (Id.Set.add id names, set_name (Name id) decl :: l)
  in
  snd @@ List.fold_right fold l (s.names,[])



(* fold functions for state *)
let fold_right_state s l tp t =
  let rec aux ids1 i l s t =
    match l with
    | [] -> t (s, List.rev ids1)
    | a :: l -> tp s i a (fun (s, id1) -> aux (id1 :: ids1) (i+1) l s t)
  in
  aux [] 0 l s t

let fold_right_state2 s l tp t =
  let rec aux ids1 ids2 i l s t =
    match l with
    | [] -> t (s, List.rev ids1, List.rev ids2)
    | a :: l -> tp s i a (fun (s, id1, id2) -> aux (id1 :: ids1) (id2 :: ids2) (i+1) l s t)
  in
  aux [] [] 0 l s t

let fold_right_state3 s l tp t =
  let rec aux ids1 ids2 ids3 i l s t =
    match l with
    | [] -> t (s, List.rev ids1, List.rev ids2, List.rev ids3)
    | a :: l -> tp s i a (fun (s, id1, id2, id3) -> aux (id1 :: ids1) (id2 :: ids2) (id3 :: ids3) (i+1) l s t)
  in
  aux [] [] [] 0 l s t

let fold_left_state s l tp t =
  fold_right_state s (List.rev l) tp t

  let fold_left_state2 s l tp t =
  fold_right_state2 s (List.rev l) tp t

  let fold_left_state3 s l tp t =
  fold_right_state3 s (List.rev l) tp t

let fold_right_state_opt s l tp t =
  let rec aux ids1 i l s t =
    match l with
    | [] -> t (s, (List.rev ids1))
    | a :: l -> tp s i a (fun s id1 -> aux (List.append id1 ids1) (1+i) l s t)
  in
  aux [] 0 l s t

let fold_right_state_opt2 s l tp t =
  let rec aux ids1 ids2 i l s t =
    match l with
    | [] -> t (s , List.rev ids1, List.rev ids2)
    | a :: l -> tp s i a (fun s id1 id2 -> aux (List.append id1 ids1) (List.append id2 ids2) (i+1) l s t)
  in
  aux [] [] 0 l s t

  let fold_right_state_opt3 s l tp t =
  let rec aux ids1 ids2 ids3 i l s t =
    match l with
    | [] -> t (s , List.rev ids1, List.rev ids2, List.rev ids3)
    | a :: l -> tp s i a (fun s id1 id2 id3 -> aux (List.append id1 ids1) (List.append id2 ids2) (List.append id3 ids3) (i+1) l s t)
  in
  aux [] [] [] 0 l s t

let fold_left_state_opt s l tp cc =
  fold_right_state_opt s (List.rev l) tp cc

let fold_left_state_opt2 s l tp cc =
  fold_right_state_opt2 s (List.rev l) tp cc

let fold_left_state_opt3 s l tp cc =
  fold_right_state_opt3 s (List.rev l) tp cc



(* ************************************************************************** *)
(*                      Add variables to the state                            *)
(* ************************************************************************** *)


let add_old_var s na ty cc = cc (push_old_rel s (LocalAssum (na, ty)))
let add_old_letin s na bd ty cc = cc (push_old_rel s (LocalDef (na, bd, ty)))

let add_fresh_var s na ty cc = cc (push_fresh_rel s (LocalAssum (na, ty)))
let add_fresh_letin s na bd ty cc = cc (push_fresh_rel s (LocalDef (na, bd, ty)))



(* ************************************************************************** *)
(*                            Make Binders                                    *)
(* ************************************************************************** *)

let (let*) x f = x f

(* 1. Keep, and Make Binary Binders and letin *)
let kp_binder binder s na ty cc =
  let ty' = weaken s ty in
  let* (s', key_bind) = add_old_var s na ty in
  binder (na, ty', cc (s', key_bind))

let kp_tProd = kp_binder mkProd
let kp_tLambda = kp_binder mkLambda

let mk_binder binder s na ty cc =
  let* (s, key_mk) = add_fresh_var s na ty in
  binder (na, ty, cc (s, key_mk))

let mk_tProd = mk_binder mkProd
let mk_tLambda = mk_binder mkLambda

let kp_binder_name binder s na ty cc =
  let ty' = weaken s ty in
  let na = set_name_rel s na ty' in
  let* (s', key_bind) = add_old_var s na ty in
  binder (na, ty', cc (s', key_bind))

let kp_tProd_name = kp_binder_name mkProd
let kp_tLambda_name = kp_binder_name mkLambda

let mk_binder_name binder s na ty cc =
  let na = set_name_rel s na ty in
  let* (s, key_mk) = add_fresh_var s na ty in
  binder (na, ty, cc (s, key_mk))

let mk_tProd_name = mk_binder_name mkProd
let mk_tLambda_name = mk_binder_name mkLambda



let kp_tLetIn s na bd ty cc =
  let bd' = weaken s bd in
  let ty' = weaken s ty in
  let* (s', key_let) = add_old_letin s na bd ty in
  mkLetIn (na, bd', ty', cc (s', key_let))

let mk_tLetIn s na bd ty cc =
  let* (s, key_let) = add_fresh_letin s na bd ty in
  mkLetIn (na, bd, ty, cc (s, key_let))

(* 2. Iterate unary version *)

(* keep all vars *)
let read_context read_var read_letin s cxt =
  fold_left_state s cxt (fun s _ decl cc ->
      let na = RelDecl.get_annot decl in
      let ty = RelDecl.get_type decl in
      match RelDecl.get_value decl with
      | None    -> read_var s na ty cc
      | Some bd -> read_letin s na bd ty cc
  )

(* seperate var and letin *)
let read_context_sep read_var read_letin s cxt =
  fold_left_state_opt3 s cxt (fun s i decl cc ->
      let na = RelDecl.get_annot decl in
      let ty = RelDecl.get_type decl in
      match RelDecl.get_value decl with
      | None    -> read_var s na ty (fun (s, key_var) -> cc s [key_var] [] [key_var])
      | Some bd -> read_letin s na bd ty (fun (s, key_letin) -> cc s [] [key_letin] [key_letin])
  )

(* takes a continuation after binder var and letin to add fresh binders and decide what to do with the keys *)
let read_by_decl s cxt read_letin cc_letin read_var cc_var =
  fold_left_state_opt s cxt (fun s pos_decl decl cc ->
    match decl with
    | LocalDef (na, bd, ty) ->
        let* (s, key_letin) = read_letin s na bd ty in
        cc_letin s pos_decl key_letin cc
    | LocalAssum (na, ty) ->
        let* (s, key_var) = read_var s na ty in
        cc_var s pos_decl key_var cc
  )


let add_old_context s = read_context add_old_var add_old_letin s
let add_old_context_sep s = read_context_sep add_old_var add_old_letin s

let add_fresh_context s = read_context add_fresh_var add_fresh_letin s
let add_fresh_context_sep s = read_context_sep add_fresh_var add_fresh_letin s

let closure_old_context binder = read_context binder kp_tLetIn
let closure_old_context_sep binder = read_context_sep binder kp_tLetIn

let closure_new_context binder = read_context binder mk_tLetIn
let closure_new_context_sep binder = read_context_sep binder mk_tLetIn

(* ************************************************************************** *)
(*                       Mutual Inductive Type                                *)
(* ************************************************************************** *)

(* 3. Mutual Inductive Body Level *)

(* generalize properly parameters *)
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
    let sigma = Evd.add_constraints sigma csts in
    sigma, EConstr.of_rel_context params

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

let get_params_sep sigma mdecl u =
  let (sigma, up_params) = paramdecls_fresh_template sigma (mdecl, u) in
  let (uparams, nuparams) = chop_letin mdecl.mind_nparams_rec @@ List.rev up_params in
  (sigma, List.rev uparams, List.rev nuparams)

let closure_uparams binder s uparams = closure_old_context_sep binder s uparams
let closure_nuparams binder s nuparams = closure_old_context_sep binder s nuparams

let get_ind_bodies mdecl = mdecl.mind_packets

let iterate_inductives s mdecl tp cc =
  fold_right_state s (Array.to_list mdecl.mind_packets) tp cc

(* create fix *)
let mk_tFix s mdecl kname tFix_rarg focus tFix_name tFix_type tmc =
  let ind_bodies = get_ind_bodies mdecl in
  (* data fix *)
  let rargs = Array.mapi (fun pos_indb indb -> tFix_rarg pos_indb indb) (Array.copy ind_bodies) in
  let tFix_names = Array.mapi tFix_name (Array.copy ind_bodies) in
  let tFix_types = Array.mapi (tFix_type s) (Array.copy ind_bodies) in
  (* update context continuation *)
  (* MOST LIKELY BUGGED => IF A ∈ tFix_type -> new binders -> issues *)
  let cdecl pos_indb indb = LocalAssum (tFix_name pos_indb indb, tFix_type s pos_indb indb) in
  let tFix_context = List.rev (List.mapi cdecl (Array.to_list ind_bodies)) in
  let* (sFix, keys_Fix) = add_fresh_context s tFix_context in
  (* END BUG *)
  let tFix_bodies = Array.mapi (fun pos_indb indb -> tmc (sFix, keys_Fix, pos_indb, indb)) ind_bodies in
  (* result *)
  EConstr.mkFix ((rargs, focus), (tFix_names, tFix_types, tFix_bodies))

(* Doe not create a fix if it is not-recursive and only has one inductive body *)
  let mk_tFix_or_not is_rec s mdecl kn tFix_rarg pos_indb tFix_name tFix_type cc =
    if is_rec
    then mk_tFix s mdecl kn tFix_rarg pos_indb tFix_name tFix_type cc
    else cc (s, [], 0, mdecl.mind_packets.(0))


(* ************************************************************************** *)
(*                          One Inductive Type                                *)
(* ************************************************************************** *)

(* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
let make_ind s ind u key_uparams nuparams indices =
    let tInd = mkIndU (ind, u) in
    let args = [get_terms s key_uparams; nuparams; indices] in
    mkApp (tInd, (Array.of_list (List.concat args)))

(* Builds: Cst A1 ... An B0 ... Bm x1 ... xp *)
let make_cst s ind u pos_ctor key_uparams nuparams args =
  let tCst = mkConstructU ((ind, 1+pos_ctor), u) in
  let args = [get_terms s key_uparams; nuparams; args] in
  mkApp (tCst, (Array.of_list (List.concat args)))

let get_indices indb u =
    let indices, _ = List.chop indb.mind_nrealdecls indb.mind_arity_ctxt in
    Vars.subst_instance_context u @@ EConstr.of_rel_context indices

(* Closure for indices must be fresh as it is not in the context of the arguments *)
let add_indices s indb u = add_fresh_context_sep s (weaken_context s (get_indices indb u))
let closure_indices binder s indb u = closure_new_context_sep binder s (weaken_context s (get_indices indb u))

let default_rarg mdecl indb =
  (mdecl.mind_nparams - mdecl.mind_nparams_rec) + indb.mind_nrealargs

let get_args s mdecl u (cxt, ty) =
  let nb_params_letin = List.length mdecl.mind_params_ctxt in
  let (_, args) = List.chop nb_params_letin (List.rev cxt) in
  let args = Vars.subst_instance_context u @@ EConstr.of_rel_context @@ List.rev args in
  let (hd, xs) = decompose_app s.sigma (Vars.subst_instance_constr u @@  EConstr.of_constr ty) in
  let indices = Array.sub xs mdecl.mind_nparams (Array.length xs - mdecl.mind_nparams) in
  (args, indices)

let get_ctors s mdecl u pos_indb =
  let ctors = mdecl.mind_packets.(pos_indb).mind_nf_lc in
  Array.map (get_args s mdecl u) ctors

let iterate_ctors s mdecl u pos_indb tp cc =
  let ctors = get_ctors s mdecl u pos_indb in
  fold_right_state s (Array.to_list ctors) tp cc

let iterate_all_ctors s kname mdecl u tp cc =
  iterate_inductives s mdecl (
    fun s pos_indb indb cc -> iterate_ctors s mdecl u pos_indb (fun s -> tp s pos_indb indb) cc
  ) cc



(* mk match *)
let mk_tCase s mdecl ind indb u keys_uparams keys_nuparams params indices mk_case_pred case_relevance tm_match tc =
  let tCase_info = Inductiveops.make_case_info s.env ind RegularStyle in

  let case_invert =
    if Typeops.should_invert_case s.env (Unsafe.to_relevance case_relevance) tCase_info
    then Constr.CaseInvert {indices=Array.of_list indices}
    else Constr.NoInvert
  in

  let tCase_Pred =
    (* indices *)
    let indices = weaken_context s (get_indices indb u) in
    let name_indices = List.map get_annot @@ set_names_context s indices in
    let* (s, keys_fresh_indices, _, _) = add_fresh_context_sep s indices in
    (* new var *)
    let ty_var = make_ind s ind u keys_uparams (get_terms s keys_nuparams) (get_terms s keys_fresh_indices) in
    let name_var_match = set_name_rel s (make_annot Anonymous (Inductiveops.relevance_of_inductive s.env (ind, u))) ty_var in
    let* (s, key_var_match) = add_fresh_var s name_var_match ty_var in
    (* return type *)
    let return_type = mk_case_pred s keys_fresh_indices key_var_match in
    (* return *)
    ((Array.of_list (List.append name_indices [name_var_match]), return_type), case_relevance)
  in

  let branch pos_ctor ctor =
    let args = fst @@ get_args s mdecl u ctor in
    let names_args = Array.of_list (List.rev_map get_annot args) in
    let* s, key_args, key_letin, key_both = add_old_context_sep s args in
    let branches_body = tc (s, key_args, key_letin, key_both, pos_ctor) in
    (names_args, branches_body)
  in

  let branches = Array.mapi branch indb.mind_nf_lc in

  let case_info, pred, case_invert, c, branches = EConstr.expand_case s.env s.sigma (tCase_info, u, params, tCase_Pred, case_invert, tm_match, branches) in
  Inductiveops.simple_make_case_or_project s.env s.sigma case_info pred case_invert c branches

