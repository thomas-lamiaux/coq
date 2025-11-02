open Names
open Declarations
open Context
open EConstr
module RelDecl = Rel.Declaration
open RelDecl
open NamedAPI
open State


let gen_rec kn u (mdecl : mutual_inductive_body) sort_pred dep =

  let pred_relevance = Retyping.relevance_of_sort sort_pred in

  let ind_relevance s pos_indb = Inductiveops.relevance_of_inductive s.env ((kn, pos_indb), u) in

  let make_ind_keys s pos_indb keys_uparams keys_nuparams keys_indices =
    make_ind s (kn, pos_indb) u keys_uparams (get_terms s keys_nuparams) (get_terms s keys_indices)
  in


  (* ################################# *)
  (*     1. Predicates                 *)
  (* ################################# *)

  (* 1.1. Builds the type of the predicate for the i-th block
    forall (B0 ... Bm : nuparams),
    forall (i1 ... tl : indices),
    (Ind A1 ... An B0 ... Bm i1 ... il) -> U)  *)
  let make_type_pred s pos_indb indb keys_uparams nuparams: constr =
    let* (s, keys_nuparams, _, _) = closure_nuparams kp_tProd_name s nuparams in
    let* (s, keys_indices , _, _) = closure_indices (if dep then mk_tProd_name else mk_tProd) s indb u in
    if not dep then mkSort sort_pred else
    let name_ind = make_annot Anonymous (ind_relevance s pos_indb) in
    let ind = make_ind_keys s pos_indb keys_uparams keys_nuparams keys_indices in
    let* _ = mk_tProd_name s name_ind ind in
    mkSort sort_pred
  in

  (* closure version *)
  let closure_preds binder s keys_uparams nuparams =
    iterate_inductives s mdecl
      (fun s pos_indb indb cc ->
        let name_pred = make_annot (Name (Id.of_string "P")) ERelevance.relevant in
        binder s name_pred (make_type_pred s pos_indb indb keys_uparams nuparams) cc
    )
  in



  (* ################################# *)
  (*     2. Assumption Functions       *)
  (* ################################# *)

  (* This function computes the type of the recursive call *)
  let make_rec_call s key_preds key_arg ty : constr option =
    (* Format.printf "\n BEGIN: view"; *)
    let x = view_arg kn mdecl s.sigma ty in
    (* Format.printf "\n END: view \n"; *)
    match x with
    | ArgIsInd (pos_ind, loc, inst_nuparams, inst_indices) ->
        Some (
          (* Pi B0 ... Bm i0 ... il (x a0 ... an) *)
          let* (s, key_locals, _, _) = closure_new_context_sep mk_tProd s loc in
          let pred = mkApp ((geti_term s key_preds pos_ind), (Array.append inst_nuparams inst_indices)) in
          if not dep then pred else
          let arg = mkApp (get_term s key_arg, Array.of_list (get_terms s key_locals)) in
          mkApp (pred, Array.make 1 arg)
        )
    | _ -> None
  in

  (* Create and bind the recursive call *)
  let make_rec_call_cc key_preds s _ key_arg cc =
    let red_ty = Reductionops.whd_all s.env s.sigma (get_type s key_arg) in
    match make_rec_call s key_preds key_arg red_ty with
    | Some ty -> let name_rec_hyp = make_annot Anonymous pred_relevance in
                  mk_tProd s name_rec_hyp ty (fun (s, key_rec) -> cc s [key_arg])
    | _ -> cc s [key_arg]
  in

  (* 1.2.2 Generates the type associated to a constructor *)
  (* forall (B0 ... Bm : nuparams),
     forall x0 : arg0, [P x0], ..., xn : argn, [P n],
     P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
  let make_type_ctor s pos_indb indb pos_ctor ctor keys_uparams nuparams key_preds =
    let* (s, keys_nuparams, _, _) = closure_nuparams kp_tProd_name s nuparams in
    let (args, indices) = ctor in
    let* (s, key_args) = read_by_decl s args kp_tLetIn (fun s _ _ cc -> cc s []) (if dep then kp_tProd_name else kp_tProd) (make_rec_call_cc key_preds) in
    let indices = Array.map (weaken s) indices in
    let pred = mkApp ((geti_term s key_preds pos_indb), Array.append (Array.of_list (get_terms s keys_nuparams)) indices) in
    if not dep then pred else
    let cst = make_cst s (kn, pos_indb) u pos_ctor keys_uparams (get_terms s keys_nuparams) (get_terms s key_args) in
    mkApp (pred, Array.make 1 cst)
  in

  (* closure assumptions functions over all the ctors *)
  let closure_ctors binder s sigma keys_uparams nuparams key_preds cc =
    iterate_all_ctors s kn mdecl u (
      fun s pos_indb indb pos_ctor ctor cc ->
      let name_assumption = make_annot (Name indb.mind_consnames.(pos_ctor)) pred_relevance in
      let fct = make_type_ctor s pos_indb indb pos_ctor ctor keys_uparams nuparams key_preds in
      binder s name_assumption fct cc
    ) cc
  in



  (* ################################# *)
  (*          3. Return Types          *)
  (* ################################# *)

  (* 1.3. Make the type of the conclusion *)
  (* P B0 ... Bm i0 ... il x *)
  let make_ccl s key_preds pos_indb keys_nuparams keys_indices key_VarMatch =
    let args = Array.of_list (get_terms s keys_nuparams @ get_terms s keys_indices) in
    let pred = mkApp (geti_term s key_preds pos_indb, args) in
    if not dep then pred else
    mkApp (pred, Array.make 1 (get_term s key_VarMatch))
  in

  (* 1.4. Make the return type *)
  (* forall (B0 ... Bm : nuparams),
     forall (i1 ... il : indices),
     forall (x : Ind A0 ... An B0 ... Bm i0 ... il),
     P B0 ... Bm i0 ... il x *)
  let make_return_type s pos_indb indb keys_uparams nuparams key_preds =
      let* (s, keys_nuparams, _, _) = closure_nuparams kp_tProd_name s nuparams in
      let* (s, keys_indices , _, _) = closure_indices mk_tProd_name s indb u in
      let name_ind = make_annot Anonymous (ind_relevance s pos_indb) in
      let ind = make_ind_keys s pos_indb keys_uparams keys_nuparams keys_indices in
      let* (s, key_VarMatch) = mk_tProd_name s name_ind ind in
      make_ccl s key_preds pos_indb keys_nuparams keys_indices key_VarMatch
  in



  (* ####################################### *)
  (*    4. Make the type of the recursors    *)
  (* ####################################### *)

  let gen_rec_type env sigma pos_indb =
    let (sigma, uparams, nuparams) = get_params_sep sigma mdecl u in
    let s = State.make env sigma in
    let indb = mdecl.mind_packets.(pos_indb) in
    let* (s, key_uparams, _, _) = closure_uparams kp_tProd_name s uparams in
    let* (s, key_preds)   = closure_preds mk_tProd_name s key_uparams nuparams in
    let* (s, key_ctors)   = closure_ctors mk_tProd_name s sigma key_uparams nuparams key_preds in
    make_return_type s pos_indb indb key_uparams nuparams key_preds
  in



(* ####################################### *)
(*    5. Make the term of the recursors    *)
(* ####################################### *)

  (* ty is well-formed in s *)
  let make_rec_call key_fixs s key_arg ty : constr option =
    match view_arg kn mdecl s.sigma ty with
    | ArgIsInd (pos_ind, loc, inst_nuparams, inst_indices) ->
        Some (
          (* Fi B0 ... Bm i0 ... il (x a0 ... an) *)
          let* (s, key_locals, _, _) = closure_new_context_sep mk_tLambda s loc in
          let fix = mkApp ((geti_term s key_fixs pos_ind), (Array.append inst_nuparams inst_indices)) in
          let arg = mkApp (get_term s key_arg, Array.of_list (get_terms s key_locals)) in
          mkApp (fix, Array.make 1 arg)
        )
    | _ -> None
  in

  (* Compute the arguments of the rec call *)
  let compute_args_fix pos_ctor s key_fixs key_args =
    CList.fold_right_i (fun pos_arg key_arg t ->
      let red_ty = Reductionops.whd_all s.env s.sigma (get_type s key_arg) in
      match make_rec_call key_fixs s key_arg red_ty with
        | Some rc_tm -> (get_term s key_arg) :: rc_tm :: t
        | None -> (get_term s key_arg) :: t
    ) 0 key_args []
    in

let gen_rec_term env sigma pos_indb indb =

  (* 0. Initialise template polymorphism + state *)
  let (sigma, uparams, nuparams) = get_params_sep sigma mdecl u in
  let s = State.make env sigma in

  let t =

    (* 1. Closure Uparams / preds / ctors *)
    let* (s, key_uparams, _, _) = closure_uparams kp_tLambda_name s uparams in
    let* (s, key_preds)   = closure_preds   mk_tLambda_name s key_uparams nuparams in
    let* (s, key_ctors)   = closure_ctors   mk_tLambda_name s sigma key_uparams nuparams key_preds in
    (* 2. Fixpoint *)
    let tFix_name pos_indb indb = make_annot (Name.Name (Id.of_string "F")) pred_relevance in
    let tFix_type s pos_indb indb = make_return_type s pos_indb indb key_uparams nuparams key_preds in
    let tFix_rarg pos_indb indb = default_rarg mdecl indb in
    let is_rec = Array.length mdecl.mind_packets > 1 || Inductiveops.mis_is_recursive env ((kn, pos_indb), mdecl, indb) in
    let* (s, key_fixs, pos_indb, indb) = mk_tFix_or_not is_rec s mdecl kn tFix_rarg pos_indb tFix_name tFix_type in
    (* 3. Closure Nuparams / Indices / Var *)
    let* (s, key_nuparams, _, _) = closure_nuparams kp_tLambda_name s nuparams in
    let* (s, key_indices , _, _) = closure_indices mk_tLambda_name s indb u in
    let name_ind = make_annot Anonymous (ind_relevance s pos_indb) in
    let ind = make_ind_keys s pos_indb key_uparams key_nuparams key_indices in
    let* (s, key_VarMatch) = mk_tLambda_name s name_ind ind in
    (* 4. Proof of P ... x by match *)
    let params = Array.of_list (get_terms s key_uparams @ get_terms s key_nuparams) in
    let tCase_pred s keys_fresh_indices key_var_match = make_ccl s key_preds pos_indb key_nuparams keys_fresh_indices key_var_match in
    let* (s, key_args, key_letin, key_both, pos_ctor) =
      mk_tCase s mdecl (kn, pos_indb) indb u key_uparams key_nuparams params (get_terms s key_indices)
            tCase_pred pred_relevance (get_term s key_VarMatch) in
    (* 5. Make the branch *)
    let args = get_terms s key_nuparams @ compute_args_fix pos_ctor s key_fixs key_args  in
    mkApp ((getij_term s key_ctors pos_indb pos_ctor), Array.of_list args)

  in (sigma, t)

in gen_rec_term

let gen_rec env sigma kn u mdecl sort_pred dep pos_ind indb =
  gen_rec kn u mdecl sort_pred dep env sigma pos_ind indb

