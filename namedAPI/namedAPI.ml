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
open EConstr
open Context
open Typing
open Util
open Namegen
open RelvEnv

module RelDecl = Rel.Declaration
open RelDecl

type aname = Name.t binder_annot

let lift_decl n =
  RelDecl.map_constr (Vars.lift n)


type state =
  { state_context : rel_context;
    state_subst : constr list;
  }

let init_state = { state_context = []; state_subst = [] }

let mk_state x y = { state_context = x; state_subst = y }

let weaken s c = Vars.substl s.state_subst c


(* fold functions for state *)
let fold_right_state (s : state) l tp t =
  let rec aux ids1 l s t =
    match l with
    | [] -> t (s, List.rev ids1)
    | a :: l -> tp s a (fun (s, id1) -> aux (id1 :: ids1) l s t)
  in
  aux [] l s t

let fold_right_state2 (s : state) l tp t =
  let rec aux ids1 ids2 l s t =
    match l with
    | [] -> t (s, List.rev ids1, List.rev ids2)
    | a :: l -> tp s a (fun (s, id1, id2) -> aux (id1 :: ids1) (id2 :: ids2) l s t)
  in
  aux [] [] l s t

let fold_right_state3 (s : state) l tp t =
  let rec aux ids1 ids2 ids3 l s t =
    match l with
    | [] -> t (s, List.rev ids1, List.rev ids2, List.rev ids3)
    | a :: l -> tp s a (fun (s, id1, id2, id3) -> aux (id1 :: ids1) (id2 :: ids2) (id3 :: ids3) l s t)
  in
  aux [] [] [] l s t

let fold_left_state s l tp t =
  fold_right_state s (List.rev l) tp t

  let fold_left_state2 s l tp t =
  fold_right_state2 s (List.rev l) tp t

  let fold_left_state3 s l tp t =
  fold_right_state3 s (List.rev l) tp t

let fold_right_state_opt (s : state) l tp t =
  let rec aux ids1 l s t =
    match l with
    | [] -> t s (List.rev ids1)
    | a :: l -> tp s a (fun s id1 -> aux (List.append id1 ids1) l s t)
  in
  aux [] l s t

let fold_right_state_opt2 (s : state) l tp t =
  let rec aux ids1 ids2 l s t =
    match l with
    | [] -> t (s , List.rev ids1, List.rev ids2)
    | a :: l -> tp s a (fun s id1 id2 -> aux (List.append id1 ids1) (List.append id2 ids2) l s t)
  in
  aux [] [] l s t

  let fold_right_state_opt3 (s : state) l tp t =
  let rec aux ids1 ids2 ids3 l s t =
    match l with
    | [] -> t (s , List.rev ids1, List.rev ids2, List.rev ids3)
    | a :: l -> tp s a (fun s id1 id2 id3 -> aux (List.append id1 ids1) (List.append id2 ids2) (List.append id3 ids3) l s t)
  in
  aux [] [] [] l s t

let fold_left_state_opt (s : state) l tp cc =
  fold_right_state_opt s (List.rev l) tp cc

let fold_left_state_opt2 (s : state) l tp cc =
  fold_right_state_opt2 s (List.rev l) tp cc

let fold_left_state_opt3 (s : state) l tp cc =
  fold_right_state_opt3 s (List.rev l) tp cc


(* Add Variables to State *)
type key = int
type keys = key list

let fresh_key s = List.length s.state_context

(* old declarations *)
let add_odecl s d =
  mk_state (RelDecl.map_constr (Vars.substl s.state_subst) d :: s.state_context)
    (mkRel 0 :: List.map (Vars.lift 1) s.state_subst)

let add_ovar (s : state) (an : aname) (ty : constr) : state =
  add_odecl s (LocalAssum (an, ty))

let add_old_var : state -> aname -> constr -> (state * key -> 'a) -> 'a =
  fun s an ty cc ->
  let s' = add_ovar s an ty in
  cc (s', (fresh_key s))

let add_oletin (s : state) (an : aname) (db : constr) (ty : constr) : state =
  add_odecl s (LocalDef (an, db, ty))

let add_old_letin : state -> aname -> constr -> constr -> (state * key -> 'a) -> 'a =
  fun s an db ty cc ->
  let s' = add_oletin s  an db ty in
  cc (s', (fresh_key s))

let add_ocontext (s : state) (cxt : rel_context) : state =
  List.fold_right (fun d s -> add_odecl s d)
    cxt s

(* add fresh declaration *)
let add_fdecl s d =
  mk_state (d :: s.state_context)
    (List.map (Vars.lift 1) s.state_subst)

let add_fvar s na t = add_fdecl s (LocalAssum (na,t))

let add_fresh_var : state -> aname -> constr -> (state * key -> 'a) -> 'a =
  fun s an ty cc ->
  let s' = add_fvar s an ty in
  cc (s', (fresh_key s))

let add_fletin (s : state) (an : aname) (db : constr) (ty : constr) : state =
  mk_state (LocalDef (an, db, ty) :: s.state_context)
    (List.map (Vars.lift 1) s.state_subst)

let add_fresh_letin : state -> aname -> constr -> constr -> (state * key -> _) -> _ =
  fun s an db ty cc ->
  let s' = add_fletin s an db ty in
  cc (s', (fresh_key s))

let add_fcontext (s : state) (cxt : rel_context) : state =
  List.fold_right (fun d s -> add_fdecl s d)
    cxt s

(* substitute variables *)
let subst_obind (s : state) (tm : constr) : state =
  mk_state s.state_context
    (tm :: List.map (Vars.lift 1) s.state_subst)

let subst_old_bind : state -> constr -> (state -> _) -> _ =
  fun s tm cc ->
  let s' = subst_obind s tm in
  cc s'

let subst_ocontext (s : state) (ltm : constr list) : state =
  mk_state s.state_context
  (List.rev_append ltm (List.map (Vars.lift (List.length ltm)) s.state_subst))

let subst_old_context : state -> constr list -> (state -> _) -> _ =
  fun s ltm cc ->
  let s' = subst_ocontext s ltm in
  cc s'


(* Get and check functions for the context *)
let get_decl : state -> key -> rel_declaration =
  fun s k ->
  let n' = List.length s.state_context - k -1 in
  RelDecl.map_constr (Vars.lift n') (List.nth s.state_context n')

let getters f =
  let get_X : state -> key -> _ =
      fun s k -> f (List.length (s.state_context) - k -1) (get_decl s k)
  in

  let geti_X : state -> keys -> int -> _ =
      fun s ks pos_k -> get_X s (List.nth ks pos_k)
  in

  let getij_X : state -> keys list -> int -> int -> _ =
      fun s kss pos_k1 pos_k2 -> get_X s (List.nth (List.nth kss pos_k1) pos_k2)
  in

  let get_Xs : state -> keys -> _ list =
      fun s ks -> List.map (fun k -> get_X s k) ks
  in
  (get_X, geti_X, getij_X, get_Xs)

let get_sdecl_term : int -> rel_declaration -> constr =
  fun n d ->
  match RelDecl.get_value d with
  | Some tm -> Vars.lift 1 tm
  | None -> mkRel n

let get_term, geti_term, getij_term, get_terms = getters get_sdecl_term

let get_type, geti_type, getij_type, get_types = getters (fun _ d -> Vars.lift 1 (RelDecl.get_type d))

let get_aname, geti_aname, getij_aname, get_anames = getters (fun _ cdecl -> RelDecl.get_annot cdecl)

let get_pos : state -> key -> int =
  fun s k -> List.length (s.state_context) - k - 1

let check_pos: state -> key -> int -> bool =
  fun s k read_pos -> Int.equal (List.length (s.state_context) -k -1) read_pos


(* creating terms  *)
let (let*) x f = x f

(* 1. Keep, and Make Binary Binders and letin *)
let kp_binder binder : state -> aname -> constr -> (state * key -> constr) -> constr =
  fun s an ty cc ->
  let ty' = weaken s ty in
  let* (s', key_bind) = add_old_var s an ty in
  binder (an, ty', cc (s', key_bind))

let kp_tProd = kp_binder mkProd
let kp_tLambda = kp_binder mkLambda

let mk_binder binder : state -> aname -> constr -> (state * key -> constr) -> constr =
  fun s an ty cc ->
    let* (s, key_mk) = add_fresh_var s an ty in
    binder (an, ty, cc (s, key_mk))

let mk_tProd = mk_binder mkProd
let mk_tLambda = mk_binder mkLambda

let kp_tLetIn : state -> aname -> constr -> constr -> (state * key -> constr) -> constr =
  fun s an db ty cc ->
  let db' = weaken s db in
  let ty' = weaken s ty in
  let* (s', key_let) = add_old_letin s an db ty in
  mkLetIn (an, db', ty', cc (s', key_let))

let mk_tLetIn : state -> aname -> constr -> constr -> (state * key -> constr) -> constr =
  fun s an db ty cc ->
  let* (s, key_let) = add_fresh_letin s an db ty in
  mkLetIn (an, db, ty, cc (s, key_let))

(* 2. Iterate unary version *)
(* keep all vars *)
let read_context read_var read_letin s cxt =
  fold_left_state s cxt (fun s decl cc ->
      let an = RelDecl.get_annot decl in
      let ty = RelDecl.get_type decl in
      match RelDecl.get_value decl with
      | None    -> read_var s an ty cc
      | Some db -> read_letin s an db ty cc
  )

(* seperate var and letin *)
let read_context_sep read_var read_letin s cxt =
  fold_left_state_opt3 s cxt (fun s decl cc ->
      let an = RelDecl.get_annot decl in
      let ty = RelDecl.get_type decl in
      match RelDecl.get_value decl with
      | None    -> read_var s an ty (fun (s, key_var) -> cc s [key_var] [] [key_var])
      | Some db -> read_letin s an db ty (fun (s, key_letin) -> cc s [] [key_letin] [key_letin])
  )

let add_old_context = read_context add_old_var add_old_letin
let add_old_context_sep = read_context_sep add_old_var add_old_letin

let add_fresh_context = read_context add_old_var add_old_letin
let add_fresh_context_sep = read_context_sep add_old_var add_old_letin

let closure_old_context binder = read_context (kp_binder binder) kp_tLetIn
let closure_old_context_sep binder = read_context_sep (kp_binder binder) kp_tLetIn

let closure_new_context binder = read_context (mk_binder binder) kp_tLetIn
let closure_new_context_sep binder = read_context_sep (mk_binder binder) kp_tLetIn


(* 3. Inductive *)

let unsafe_instance = UVars.Instance.empty

(* Builds: Ind A1 ... An B0 ... Bm i1 ... il *)
let make_ind =
  fun env sigma s kname pos_indb key_uparams key_nuparams key_indices ->
    let sigma, tind = Evd.fresh_global env sigma (GlobRef.IndRef (kname ,pos_indb)) in
    let args = [get_terms s key_uparams; get_terms s key_nuparams; get_terms s key_indices] in
    Typing.checked_appvect env sigma tind (Array.of_list (List.concat args))

let make_indt =
  fun env sigma s kname pos_indb key_uparams nuparams indices ->
  let sigma, tind = Evd.fresh_global env sigma (GlobRef.IndRef (kname ,pos_indb)) in
  let args = [get_terms s key_uparams; nuparams; indices] in
  Typing.checked_appvect env sigma tind (Array.of_list (List.concat args))


(* Builds: Cst A1 ... An B0 ... Bm *)
let make_cst =
  fun env sigma s kname pos_indb pos_ctor key_uparams key_nuparams ->
  let sigma, tcst = Evd.fresh_global env sigma (GlobRef.ConstructRef ((kname, pos_indb), pos_ctor)) in
  let args = [get_terms s key_uparams; get_terms s key_nuparams;] in
  Typing.checked_appvect env sigma tcst (Array.of_list (List.concat args))

let get_uparams env kname =
  let mdecl = Environ.lookup_mind kname env in
  let (uparams, _) = List.chop mdecl.mind_nparams_rec mdecl.mind_params_ctxt in
  EConstr.of_rel_context uparams

let get_nuparams env kname =
  let mdecl = Environ.lookup_mind kname env in
  let (_, nuparams) = List.chop mdecl.mind_nparams_rec mdecl.mind_params_ctxt in
  EConstr.of_rel_context nuparams

let get_params env kname =
  EConstr.of_rel_context (Environ.lookup_mind kname env).mind_params_ctxt

let get_indices env kname pos_indb =
    let mdecl = Environ.lookup_mind kname env in
    let indb = Array.get mdecl.mind_packets pos_indb in
    let indices, _ = List.chop indb.mind_nrealdecls indb.mind_arity_ctxt in
    EConstr.of_rel_context indices



let add_uparams env s kname = add_old_context s (get_uparams env kname)

let closure_uparams binder env s kname = closure_old_context binder s (get_uparams env kname)

let add_nuparams env s kname = add_old_context s (get_nuparams env kname)

let closure_nuparams binder env s kname  = closure_old_context binder s (get_nuparams env kname)

let add_params env s kname  = add_old_context s (get_params env kname)

let closure_params binder env s kname  = closure_old_context binder s (get_params env kname)

let add_indices env s kname pos_indb = add_old_context s (get_indices env kname pos_indb)

let closure_params binder env s kname pos_indb = closure_old_context binder s (get_indices env kname pos_indb)

let make_name env s r =
  let id = next_ident_away (Id.of_string s) env.RelEnv.avoid in
  make_annot (Name id) r

let nameP = make_name env "P" ERelevance.relevant


let mk_tFix env sigma kname pos_indb