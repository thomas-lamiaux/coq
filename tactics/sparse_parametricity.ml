(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Util
open Names
open Constr
open EConstr
open Declarations
open Inductive
open LibBinding
open State

let (let@) x f = x f
let (let*) x f = State.bind x f

  (** {6 Lookup Sparse Parametricity } *)

let warn_no_sparse_parametricity =
  CWarnings.create ~name:"no-sparse-parametricity" ~category:Deprecation.Version.v9_2
  Pp.(fun (ind, ind_nested) ->
    Nametab.XRefs.pr (TrueGlobal (IndRef ind)) ++ str " is nested using " ++  Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++
    str " but sparse parametricity for " ++ Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++ str " is not registered.\n"
    )

let warn_no_local_fundamental_theorem =
  CWarnings.create ~name:"no-local_fundamental_theorem" ~category:Deprecation.Version.v9_2
  Pp.(fun (ind,ind_nested) ->
    Nametab.XRefs.pr (TrueGlobal (IndRef ind)) ++ str " is nested using " ++  Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++
    str " but the local fundamental theorem for " ++ Nametab.XRefs.pr (TrueGlobal (IndRef ind_nested)) ++ str " is not registered.\n"
    )

let lookup_sparse_parametricity ind ind_nested =
    match Ind_tables.lookup_scheme "sparse_parametricity" ind_nested with
    | None -> warn_no_sparse_parametricity (ind, ind_nested); None
    | Some ref_sparam ->
    match Ind_tables.lookup_scheme "local_fundamental_theorem" ind_nested with
    | None -> warn_no_local_fundamental_theorem (ind, ind_nested); None
    | Some ref_lfth -> Some (ref_sparam, ref_lfth)


  (** {6 Instantiate Sparse Parametricity } *)

let mkFunTrue x =
  let@ _ = rebind fid Lambda Fresh naming_id x in
  return @@ mkRef ((Rocqlib.lib_ref "core.True.type"), EInstance.empty)

let instantiate_sparse_parametricity inst_uparams strpos preds =
  let preds = Array.to_list preds in
  let inst_uparams = Array.to_list inst_uparams in
  let* s = get_state in
  let inst_sparam =
    List.fold_right (fun (inst_uparam, b, pred) acc ->
      if not b then inst_uparam :: acc else
      match pred with
      | None -> inst_uparam :: (snd @@ mkFunTrue inst_uparam s) :: acc
      | Some pred -> inst_uparam :: pred :: acc
      )
    (List.combine3 inst_uparams strpos preds) []
  in
  return @@ Array.of_list inst_sparam

let mkFunI x =
  let@ _ = rebind fid Lambda Fresh naming_id x in
  return @@ mkRef ((Rocqlib.lib_ref "core.True.I"), EInstance.empty)

let instantiate_fundamental_theorem inst_uparams strpos preds preds_hold =
  let inst_uparams = Array.to_list inst_uparams in
  let preds = Array.to_list preds in
  let preds_hold = Array.to_list preds_hold in
  let* s = get_state in
  let inst_lfth =
    List.fold_right (fun (inst_uparam, b, (pred, pred_hold)) acc ->
      if not b then inst_uparam :: acc else
      match pred, pred_hold with
      | None, None -> inst_uparam :: (snd @@ mkFunTrue inst_uparam s) :: (snd @@ mkFunI inst_uparam s) :: acc
      | Some pred, Some pred_hold -> inst_uparam :: pred :: pred_hold :: acc
      | _, _ -> assert false
    )
    (List.combine3 inst_uparams strpos @@ List.combine preds preds_hold) []
  in
  return @@ Array.of_list inst_lfth


  (** {6 View for Arguments } *)

type head_arg =
  (* pos_ind, constant context, inst_nuparams inst_indices *)
  | ArgIsInd of int * constr array * constr array
  (** get the position in ind_bodies out of the position of mind_packets *)
  (* kn_nested, pos_nested, inst_uparams, inst_nuparams_indices *)
  | ArgIsNested of MutInd.t * int
                   * mutual_inductive_body * bool list * one_inductive_body
                  * constr array * constr array
  (* constant context, hd, args (maybe empty) *)
  | ArgIsCst

(** View to decompose arguments as [forall locs, X] where [X] is further decomposed
    as a uniform parameter, the inductive, a nested argument or a constant. *)
type arg = rel_context * head_arg

(* Decompose the argument in [it_Prod_or_LetIn local, X] where [X] is Ind, nested or a constant *)
let view_arg kn mdecl t : arg State.t =
  let* (cxt, hd) = whd_decompose_prod_decls t in
  let* (hd, iargs) = decompose_app hd in
  let* sigma = get_sigma in
  match kind sigma hd with
  | Ind ((kn_ind, pos_ind), _) ->
    (* If it is the inductive *)
    if kn = kn_ind
    then let (_, local_nuparams_indices) = Array.chop mdecl.mind_nparams_rec iargs in
         let nb_nuparams = mdecl.mind_nparams - mdecl.mind_nparams_rec in
         let (local_nuparams, local_indices) = Array.chop nb_nuparams local_nuparams_indices in
         return @@ (cxt, ArgIsInd (pos_ind, local_nuparams, local_indices))
    (* if there is no argument, it cannot be nested *)
    else if Array.length iargs = 0 then return @@ (cxt, ArgIsCst)
    else begin
      (* If it may be nested *)
      let* env = get_env in
      let (mib_nested, ind_nested) = lookup_mind_specif env (kn_ind, pos_ind) in
      let mib_nested_strpos = Positive_parameters.compute_params_rec_strpos env kn_ind mib_nested in
      (* Check if at least one parameter can be nested upon *)
      if List.exists (fun a -> a) mib_nested_strpos then
        let (inst_uparams, inst_nuparams_indices) = Array.chop mib_nested.mind_nparams_rec iargs in
        return @@ (cxt, ArgIsNested (kn_ind, pos_ind, mib_nested, mib_nested_strpos,
                          ind_nested, inst_uparams, inst_nuparams_indices))
      else return @@ (cxt, ArgIsCst)
    end
  | _ -> return @@ (cxt, ArgIsCst)
