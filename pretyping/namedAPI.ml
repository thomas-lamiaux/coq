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
open Context
open Util
open Namegen
open Declarations

module RelDecl = Rel.Declaration
open RelDecl


(* Barrowed code, for namming ??? *)
module RelEnv =
struct
  type t = { env : Environ.env; avoid : Id.Set.t }

  let make env =
    let avoid = Id.Set.of_list (Termops.ids_of_rel_context (rel_context env)) in
    { env; avoid }

  let avoid_decl avoid decl = match get_name decl with
  | Anonymous -> avoid
  | Name id -> Id.Set.add id avoid

  let push_rel decl env =
    { env = EConstr.push_rel decl env.env; avoid = avoid_decl env.avoid decl }

  let push_rel_context ctx env =
    let avoid = List.fold_left avoid_decl env.avoid ctx in
    { env = EConstr.push_rel_context ctx env.env; avoid }

end

let make_name env s r =
  let id = next_ident_away (Id.of_string s) env.RelEnv.avoid in
  make_annot (Name id) r



(* ************************************************************************** *)
(*                           State + fold function                            *)
(* ************************************************************************** *)


(* state *)
type state =
  { state_context : rel_context;
    state_subst : constr list;
  }

let print_state env sigma s =
  let env = Environ.push_rel_context (EConstr.Unsafe.to_rel_context s.state_context) env in
  Format.printf "\n ################################################# \n";
  Format.printf "\n ### Print State ### \n";
  (* Print state *)
    Format.printf "BEGIN: State new context: \n";
    List.fold_right_i (fun i x _ ->
      Format.printf "------------------------------------------- \n";
      Format.printf "var | %n | " (1+i);
      (* Feedback.msg_info (Termops.Internal.print_constr_env env sigma (get_type x)) *)
      Feedback.msg_info (Termops.Internal.debug_print_constr sigma (get_type x))
    ) 0 s.state_context ();
    Format.printf "END: State new context: \n";
  (* Print Substitution *)
    Format.printf "\n BEGIN: Substitution \n";
    List.fold_right (fun x _ ->
      Feedback.msg_info (Termops.Internal.print_constr_env env sigma x)) s.state_subst ();
    Format.printf "\n END: Substitution \n";
  Format.printf "\n ################################################# \n"


let init_state = { state_context = []; state_subst = [] }

let mk_state x y = { state_context = x; state_subst = y }

let weaken s c = Vars.substl s.state_subst c


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

(* Add Variables to State *)
let fresh_key s = List.length s.state_context

(* old declarations *)
let add_odecl s d =
  mk_state (RelDecl.map_constr (Vars.substl s.state_subst) d :: s.state_context)
    (mkRel 1 :: List.map (Vars.lift 1) s.state_subst)

let add_ovar s an ty : state =
  add_odecl s (LocalAssum (an, ty))

let add_old_var =
  fun s an ty cc ->
  let s' = add_ovar s an ty in
  cc (s', (fresh_key s))

let add_oletin s an db ty : state =
  add_odecl s (LocalDef (an, db, ty))

let add_old_letin =
  fun s an db ty cc ->
  let s' = add_oletin s  an db ty in
  cc (s', (fresh_key s))

let add_ocontext s cxt =
  List.fold_right (fun d s -> add_odecl s d)
    cxt s

(* add fresh declaration *)
let add_fdecl s d =
  mk_state (d :: s.state_context)
    (List.map (Vars.lift 1) s.state_subst)

let add_fvar s na t = add_fdecl s (LocalAssum (na,t))

let add_fresh_var =
  fun s an ty cc ->
  let s' = add_fvar s an ty in
  cc (s', (fresh_key s))

let add_fletin s an db ty =
  mk_state (LocalDef (an, db, ty) :: s.state_context)
    (List.map (Vars.lift 1) s.state_subst)

let add_fresh_letin =
  fun s an db ty cc ->
  let s' = add_fletin s an db ty in
  cc (s', (fresh_key s))

let add_fcontext s cxt =
  List.fold_right (fun d s -> add_fdecl s d)
    cxt s

(* substitute variables *)
let subst_obind s tm =
  mk_state s.state_context
    (tm :: List.map (Vars.lift 1) s.state_subst)

let subst_old_bind =
  fun s tm cc ->
  let s' = subst_obind s tm in
  cc s'

let subst_ocontext s ltm =
  mk_state s.state_context
  (List.rev_append ltm (List.map (Vars.lift (List.length ltm)) s.state_subst))

let subst_old_context =
  fun s ltm cc ->
  let s' = subst_ocontext s ltm in
  cc s'



(* ************************************************************************** *)
(*                            Get functions                                   *)
(* ************************************************************************** *)

let get_decl =
  fun s k ->
  let n' = List.length s.state_context - k -1 in
  RelDecl.map_constr (Vars.lift n') (List.nth s.state_context n')

let getters f =
  let get_X =
      fun s k -> f (List.length (s.state_context) - k -1) (get_decl s k)
  in

  let geti_X =
      fun s ks pos_k -> get_X s (List.nth ks pos_k)
  in

  let getij_X =
      fun s kss pos_k1 pos_k2 -> get_X s (List.nth (List.nth kss pos_k1) pos_k2)
  in

  let get_Xs =
      fun s ks -> List.map (fun k -> get_X s k) ks
  in
  (get_X, geti_X, getij_X, get_Xs)

let get_sdecl_term =
  fun n d ->
  match RelDecl.get_value d with
  | Some tm -> Vars.lift 1 tm
  | None -> mkRel (1+n)

let get_term, geti_term, getij_term, get_terms = getters get_sdecl_term

let get_type, geti_type, getij_type, get_types = getters (fun _ d -> Vars.lift 1 (RelDecl.get_type d))

let get_aname, geti_aname, getij_aname, get_anames = getters (fun _ cdecl -> RelDecl.get_annot cdecl)

let get_pos =
  fun s k -> List.length (s.state_context) - k - 1

let check_pos =
  fun s k read_pos -> Int.equal (List.length (s.state_context) -k -1) read_pos




(* ************************************************************************** *)
(*                            Make Binders                                    *)
(* ************************************************************************** *)

let (let*) x f = x f

(* 1. Keep, and Make Binary Binders and letin *)
let kp_binder binder =
  fun s an ty cc ->
  let ty' = weaken s ty in
  let* (s', key_bind) = add_old_var s an ty in
  binder (an, ty', cc (s', key_bind))

let kp_tProd = kp_binder mkProd
let kp_tLambda = kp_binder mkLambda

let mk_binder binder =
  fun s an ty cc ->
    let* (s, key_mk) = add_fresh_var s an ty in
    binder (an, ty, cc (s, key_mk))

let mk_tProd = mk_binder mkProd
let mk_tLambda = mk_binder mkLambda

let kp_tLetIn =
  fun s an db ty cc ->
  let db' = weaken s db in
  let ty' = weaken s ty in
  let* (s', key_let) = add_old_letin s an db ty in
  mkLetIn (an, db', ty', cc (s', key_let))

let mk_tLetIn =
  fun s an db ty cc ->
  let* (s, key_let) = add_fresh_letin s an db ty in
  mkLetIn (an, db, ty, cc (s, key_let))

(* 2. Iterate unary version *)

(* keep all vars *)
let read_context read_var read_letin s cxt =
  fold_left_state s cxt (fun s _ decl cc ->
      let an = RelDecl.get_annot decl in
      let ty = RelDecl.get_type decl in
      match RelDecl.get_value decl with
      | None    -> read_var s an ty cc
      | Some db -> read_letin s an db ty cc
  )

(* seperate var and letin *)
let read_context_sep read_var read_letin s cxt =
  fold_left_state_opt3 s cxt (fun s i decl cc ->
      let an = RelDecl.get_annot decl in
      let ty = RelDecl.get_type decl in
      match RelDecl.get_value decl with
      | None    -> read_var s an ty (fun (s, key_var) -> cc s [key_var] [] [key_var])
      | Some db -> read_letin s an db ty (fun (s, key_letin) -> cc s [] [key_letin] [key_letin])
  )

(* takes a continuation after binder var and letin to add fresh binders and decide what to do with the keys *)
let read_by_decl s cxt read_letin cc_letin read_var cc_var =
  fold_left_state_opt s cxt (fun s pos_decl decl cc ->
    match decl with
    | LocalDef (an, db, ty) ->
        let* (s, key_letin) = read_letin s an db ty in
        cc_letin s pos_decl key_letin cc
    | LocalAssum (an, ty) ->
        let* (s, key_var) = read_var s an ty in
        cc_var s pos_decl key_var cc
  )


let add_old_context s = read_context add_old_var add_old_letin s
let add_old_context_sep s = read_context_sep add_old_var add_old_letin s

let add_fresh_context s = read_context add_old_var add_old_letin s
let add_fresh_context_sep s = read_context_sep add_old_var add_old_letin s

let closure_old_context binder = read_context (kp_binder binder) kp_tLetIn
let closure_old_context_sep binder = read_context_sep (kp_binder binder) kp_tLetIn

let closure_new_context binder = read_context (mk_binder binder) kp_tLetIn
let closure_new_context_sep binder = read_context_sep (mk_binder binder) kp_tLetIn



(* ************************************************************************** *)
(*                       Mutual Inductive Type                                *)
(* ************************************************************************** *)

(* 3. Mutual Inductive Body Level *)
let get_params_sep mdecl =
  let nb_nuparams = mdecl.mind_nparams - mdecl.mind_nparams_rec in
  let (nuparams, uparams) = List.chop nb_nuparams mdecl.mind_params_ctxt in
  (EConstr.of_rel_context uparams, EConstr.of_rel_context nuparams)

let get_uparams mdecl =
  fst @@ get_params_sep mdecl

let get_nuparams mdecl =
  snd @@ get_params_sep mdecl

let get_params mdecl =
  EConstr.of_rel_context mdecl.mind_params_ctxt

let add_uparams mdecl s = add_old_context s (get_uparams mdecl)
let closure_uparams binder mdecl s = closure_old_context binder s (get_uparams mdecl)

let add_nuparams mdecl s = add_old_context s (get_nuparams mdecl)
let closure_nuparams binder mdecl s = closure_old_context binder s (get_nuparams mdecl)

let add_params mdecl s = add_old_context s (get_params mdecl)
let closure_params binder mdecl s = closure_old_context binder s (get_params mdecl)

let get_ind_bodies mdecl = mdecl.mind_packets

let iterate_inductives s mdecl tp cc =
  fold_right_state s (Array.to_list mdecl.mind_packets) tp cc

(* create fix *)
let mk_tFix env sigma mdecl kname s tFix_rarg focus tFix_name tFix_type tmc =
  let ind_bodies = get_ind_bodies mdecl in
  (* data fix *)
  let rargs = Array.mapi (fun pos_indb indb -> tFix_rarg pos_indb indb) ind_bodies in
  let tFix_names = Array.mapi tFix_name ind_bodies in
  let tFix_types = Array.mapi tFix_type ind_bodies in
  (* update context continuation *)
  let cdecl pos_indb indb = Context.Rel.Declaration.LocalAssum (tFix_name pos_indb indb, tFix_type pos_indb indb) in
  let tFix_context = List.rev (List.mapi cdecl (Array.to_list ind_bodies)) in
  let* (sFix, keys_Fix) = add_fresh_context s tFix_context in
  let tFix_bodies = Array.mapi (fun pos_indb indb -> tmc (sFix, keys_Fix, pos_indb, indb)) ind_bodies in
  (* result *)
  EConstr.mkFix ((rargs, focus), (tFix_names, tFix_types, tFix_bodies))


(* One Inductive Body Level *)

(* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
let make_ind =
  fun s ind u key_uparams nuparams indices ->
    let tInd = mkIndU (ind, u) in
    let args = [get_terms s key_uparams; nuparams; indices] in
    mkApp (tInd, (Array.of_list (List.concat args)))

(* Builds: Cst A1 ... An B0 ... Bm x1 ... xp *)
let make_cst =
  fun s ind u pos_ctor key_uparams nuparams args ->
  let tCst = mkConstructU ((ind, 1+pos_ctor), u) in
  let args = [get_terms s key_uparams; nuparams; args] in
  mkApp (tCst, (Array.of_list (List.concat args)))

let get_indices indb =
    let indices, _ = List.chop indb.mind_nrealdecls indb.mind_arity_ctxt in
    EConstr.of_rel_context indices

let add_indices s indb = add_old_context s (get_indices indb)
let closure_indices binder s indb = closure_old_context binder s (get_indices indb)

let default_rarg mdecl indb =
  (mdecl.mind_nparams - mdecl.mind_nparams_rec) + List.length (get_indices indb)

let get_args mdecl sigma (cxt, ty) =
  let args = EConstr.of_rel_context @@ List.rev @@ let (_, args) = List.chop mdecl.mind_nparams (List.rev cxt) in args in
  let (hd, xs) = decompose_app sigma (EConstr.of_constr ty) in
  let indices = Array.sub xs mdecl.mind_nparams (Array.length xs - mdecl.mind_nparams) in
  (args, indices)

let get_ctors mdecl sigma pos_indb =
  let ctors = mdecl.mind_packets.(pos_indb).mind_nf_lc in
  Array.map (get_args mdecl sigma) ctors

let iterate_ctors s mdecl sigma pos_indb tp cc =
  let ctors = get_ctors mdecl sigma pos_indb in
  fold_right_state s (Array.to_list ctors) tp cc

let iterate_all_ctors s kname mdecl sigma tp cc =
  iterate_inductives s mdecl (
    fun s pos_indb indb cc -> iterate_ctors s mdecl sigma pos_indb (fun s -> tp s pos_indb indb) cc
  ) cc



(* mk match *)
let mk_tCase env sigma s mdecl ind indb u keys_uparams keys_nuparams params mk_case_pred mk_case_relevance tm_match tc =
  let tCase_info = Inductiveops.make_case_info env ind RegularStyle in

  let tCase_Pred =
    (* indices *)
    let indices = get_indices indb in
    let name_indices = List.map get_annot indices in
    let* (s, keys_fresh_indices) = add_fresh_context s indices in
    (* new var *)
    let name_var_match = make_annot Anonymous ERelevance.relevant in
    let ty_var = make_ind s ind u keys_uparams (get_terms s keys_nuparams) (get_terms s keys_fresh_indices) in
    let* (s, key_var_match) = add_fresh_var s name_var_match ty_var in
    (* return type *)
    let return_type = mk_case_pred s keys_fresh_indices key_var_match in
    (* return *)
    ((Array.of_list (List.append name_indices [name_var_match]), return_type), mk_case_relevance)
  in

  let branch pos_ctor ctor =
    let (args, _) = get_args mdecl sigma ctor in
    let names_args = Array.of_list (List.map get_annot args) in
    let* s, key_args, key_letin, key_both = add_old_context_sep s args in
    let branches_body = tc (s, key_args, key_letin, key_both, pos_ctor) in
    (names_args, branches_body)
  in

  let branches = Array.mapi branch indb.mind_nf_lc in

  EConstr.mkCase (tCase_info, u, params, tCase_Pred, NoInvert, tm_match, branches)


(* View Argument *)
type arg =
  (* pos_ind, constant context, inst_nuparams inst_indices *)
  | ArgIsInd of int * rel_context * constr array * constr array
  (* ind, constant context, inst_uparams, inst_nuparams, inst_indices *)
  | ArgIsNested of inductive * rel_context * constr array * constr array * constr array
  (* constant context, hd, args (maybe empty) *)
  | ArgIsCst of rel_context * constr * constr array

(* Decompose the argument in [it_Prod_or_LetIn local, X]
  where [X] is Ind, nested or a constant *)
let view_arg kname mdecl s sigma t : arg =
  let (cxt, hd) = decompose_prod_decls sigma t in
  let (hd, iargs) = decompose_app sigma hd in
  match kind sigma hd with
  (* If it is the inductive *)
  (* | Rel pos ->
      match find_bool (fun k => check_pos s k pos) key_inds with
        | (pos_strpos_uparams, true) =>
            let local_nuparams_indices := skipn (get_nb_uparams s kname) iargs in
            let local_nuparams := firstn (get_nb_nuparams s kname) local_nuparams_indices in
            let local_indices  := skipn  (get_nb_nuparams s kname) local_nuparams_indices in
            VArgIsInd pos local local_nuparams local_indices
        | _ => VArgIsFree local hd iargs
        end *)
  (* If it is nested *)
  | Ind ((kname_indb, pos_indb), _) ->
    (* If it is the inductive *)
    if kname = kname_indb
    then let nb_uparams = List.length @@ get_uparams mdecl in
         let (_, local_nuparams_indices) = Array.chop nb_uparams iargs in
         let nb_nuparams = List.length @@ get_nuparams mdecl in
         let (local_nuparams, local_indices) = Array.chop nb_nuparams local_nuparams_indices in
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
