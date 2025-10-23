open Names
open Declarations
open Context
open EConstr
open NamedAPI

let gen_rec env sigma kn sort_pred =
  (* sort pred specify the output sorts of the induction predicates *)

  let mdecl = Environ.lookup_mind kn env  in

  (*  universes *)
  let u = EInstance.make @@ UVars.make_abstract_instance @@ Declareops.universes_context mdecl.mind_universes in

  (* simplified make_ind for keys *)
  let make_ind_keys s pos_indb keys_uparams keys_nuparams keys_indices =
    make_ind s (kn, pos_indb) u keys_uparams (get_terms s keys_nuparams) (get_terms s keys_indices)
  in

  (* ################################# *)
  (*    1. Make the different types    *)
  (* ################################# *)


  (* 1.1. Builds the type of the predicate for the i-th block
    forall (B0 : R0) ... (Bm : Rm),
    forall (i1 : t1) ... (il : tl),
    (Ind A1 ... An B0 ... Bm i1 ... il) -> U)  *)
  let make_type_pred s pos_indb indb keys_uparams : constr =
    let* (s, keys_nuparams) = closure_nuparams mkProd mdecl s in
    let* (s, keys_indices) = closure_indices mkProd s indb in
    let ind = make_ind_keys s pos_indb keys_uparams keys_nuparams keys_indices in
    mkProd ((make_annot Anonymous ERelevance.relevant), ind, mkSort (sort_pred pos_indb))
  in

  (* closure version *)
  let closure_preds binder s keys_uparams =
    iterate_inductives s mdecl
      (fun s pos_indb indb cc ->
        let name_pred = make_annot Anonymous ERelevance.relevant in
        mk_binder binder s name_pred (make_type_pred s pos_indb indb keys_uparams) cc
    )
  in

  (* 1.2. Make Assumption Functions *)

  let make_type_ctor_cc pos_indb indb pos_ctor ctor keys_uparams key_preds key_fixs =

    (* This function computes the type of the recursive call, and its inhabitant *)
    let rec make_rec_call s key_arg ty : (constr * constr) option =
      match view_arg kn mdecl s sigma ty with
      | ArgIsCst _ -> None
      | ArgIsInd (pos_ind, loc, inst_nuparams, inst_indices) ->
          Some (
            (* Pi B0 ... Bm i0 ... il (x a0 ... an) *)
            ( let* (s, key_locals, _, _) = closure_old_context_sep mkProd s loc in
              let pred = mkApp ((geti_term s key_preds pos_ind), (Array.append inst_nuparams inst_indices)) in
              let arg = mkApp (get_term s key_arg, Array.of_list (get_terms s key_locals)) in
              mkApp (pred, Array.make 1 arg)),
            (* Fi  B0 ... Bm i0 ... il (x a0 ... an) *)
            ( let* (s, key_locals, _, _) = closure_old_context_sep mkLambda s loc in
              let fix = mkApp ((geti_term s key_fixs pos_ind), (Array.append inst_nuparams inst_indices)) in
              let arg = mkApp (get_term s key_arg, Array.of_list (get_terms s key_locals)) in
              mkApp (fix, Array.make 1 arg))
          )
      | ArgIsNested (ind, loc, inst_uparams, inst_nuparams, inst_indices) -> None
    in

    (* get the rec call *)
    let make_rec_call_cc s _ key_arg cc =
      let red_ty = Reductionops.whd_all env sigma (get_type s key_arg) in
      match make_rec_call s key_arg red_ty with
      | Some (ty, _) ->
          let name_rec_hyp = make_annot Anonymous ERelevance.relevant in
          mk_tProd s name_rec_hyp ty (fun (s, key_rec) -> cc s [key_arg])
      | _ -> cc s [key_arg]
    in

    (* 1.2.2 Generates the type associated to a constructor *)
    (* forall (B0 : R0) ... (Bm : Rm),
      forall x0 : t0, [P x0], ..., xn : tn, [P n],
      P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
    let make_type_ctor s =
        let* (s, keys_nuparams) = closure_nuparams mkProd mdecl s in
        let (cxt, hd) = ctor in
        let indices = [] in
        let* (s, key_args) = read_by_decl s cxt kp_tLetIn (fun s _ _ cc -> cc s []) kp_tProd make_rec_call_cc in
        let pred = mkApp ((geti_term s key_preds pos_indb), Array.of_list (get_terms s keys_nuparams @ indices)) in
        let cst = make_cst s (kn, pos_indb) u pos_ctor keys_uparams (get_terms s keys_nuparams) (get_terms s key_args) in
        mkApp (pred, Array.make 1 cst)
    in

    (* the associated continuation *)
    let make_type_ctor_cc binder s cc =
      let name_assumption = make_annot (Name indb.mind_consnames.(pos_ctor)) ERelevance.relevant in
      mk_binder binder s name_assumption (make_type_ctor s) cc
    in

    (make_rec_call, make_type_ctor_cc)

  in

  let make_rec_call pos_indb indb pos_ctor ctor keys_uparams key_preds key_fixs =
    let (x, y) = make_type_ctor_cc pos_indb indb pos_ctor ctor keys_uparams key_preds key_fixs in
    x
  in

  let make_type_ctor_cc pos_indb indb pos_ctor ctor keys_uparams key_preds key_fixs =
    let (x, y) = make_type_ctor_cc pos_indb indb pos_ctor ctor keys_uparams key_preds key_fixs in
    y
  in

  (* closure of over all the ctors *)
  let closure_ctors binder s keys_uparams key_preds cc =
    iterate_all_ctors s kn mdecl (
      fun s pos_indb indb pos_ctor ctor cc ->
      make_type_ctor_cc pos_indb indb pos_ctor ctor keys_uparams key_preds [] binder s cc) cc
  in


  (* 1.3. Make the type of the conclusion *)
  (* P B0 ... Bm i0 ... il x *)
  let make_ccl s key_preds pos_indb keys_nuparams keys_indices key_VarMatch =
      let pred = geti_term s key_preds pos_indb in
      let args = Array.of_list (get_terms s keys_nuparams @ get_terms s keys_indices @ get_terms s [key_VarMatch]) in
      mkApp (pred, args)
  in

  (* 1.4. Make the return type *)
  (* forall (B0 : R0) ... (Bm : Rm),
     forall (i1 : t1) ... (il : tl),
     forall (x : Ind A0 ... An B0 ... Bm i0 ... il),
      P B0 ... Bm i0 ... il x *)
  let make_return_type s pos_indb indb keys_uparams key_preds =
      let* (s, keys_nuparams) = closure_nuparams mkProd mdecl s in
      let* (s, keys_indices) = closure_indices mkProd s indb in
      let ind = make_ind_keys s pos_indb keys_uparams keys_nuparams keys_indices in
      let* (s, key_VarMatch) = mk_tProd s (make_annot Anonymous ERelevance.relevant) ind in
      make_ccl s key_preds pos_indb keys_nuparams keys_indices key_VarMatch
  in


  (* ####################################### *)
  (*    2. Make the type of the recursors    *)
  (* ####################################### *)

  let gen_rec_type pos_indb indb =
    let s = init_state in
    let* (s, key_uparams) = closure_uparams mkProd mdecl s in
    let* (s, key_preds)   = closure_preds mkProd s key_uparams in
    let* (s, key_ctors)   = closure_ctors mkProd s key_uparams key_preds in
    make_return_type s pos_indb indb key_uparams key_preds
  in






(* ####################################### *)
(*    3. Make the type of the recursors    *)
(* ####################################### *)

(* 3.1 Compute the arguments of the rec call *)
let compute_args_fix s pos_indb indb pos_ctor ctor keys_uparams key_preds key_fixs key_args =
  List.fold_right (fun key_arg t ->
    let red_ty = Reductionops.whd_all env sigma (get_type s key_arg) in
    match make_rec_call pos_indb indb pos_ctor ctor keys_uparams key_preds key_fixs s key_arg red_ty with
    | Some (rc_ty, rc_tm) -> (get_term s key_arg) :: rc_tm :: t
    | None -> (get_term s key_arg) :: t
  ) key_args []
  in

(* 3.2 Generates the recursor *)
let gen_rec_term pos_indb =
  (* 0. Initialise state with inductives *)
  (* let s := add_mdecl kname nb_uparams mdecl init_state in *)
  (* let* s := subst_ind s kname in *)
  let s = init_state in
  (* 1. Closure Uparams / preds / ctors *)
  let* (s, key_uparams) = closure_uparams mkProd mdecl s in
  let* (s, key_preds)   = closure_preds   mkLambda s key_uparams in
  let* (s, key_ctors)   = closure_ctors   mkLambda s key_uparams key_preds in
  (* 2. Fixpoint *)
  let tFix_type pos_indb indb = make_return_type s pos_indb indb key_uparams key_preds in
  let tFix_rarg pos_indb indb = default_rarg mdecl indb in
  let* (s, key_fixs, pos_indb, indb) = mk_tFix env sigma mdecl kn s tFix_rarg pos_indb tFix_type in
  (* 3. Closure Nuparams / Indices / Var *)
  let* (s, key_nuparams) = closure_nuparams mkLambda mdecl s in
  let* (s, key_indices ) = closure_indices  mkLambda s indb in
  let* (s, key_VarMatch) = mk_tLambda s (make_annot Anonymous ERelevance.relevant)
                          (make_ind_keys s pos_indb key_uparams key_nuparams key_indices) in

  (* 4. Proof of P ... x by match *)
  let tCase_pred s keys_fresh_indices key_var_match = make_ccl s key_preds pos_indb key_nuparams key_indices key_VarMatch in
  let* (s, key_args, key_letin, key_both, pos_ctor, ctor) = mk_tCase env s mdecl (kn, pos_indb) indb u
          tCase_pred key_uparams key_nuparams (get_term s key_VarMatch) in
  (* 5. Make the branch *)
  let args = get_terms s key_nuparams @ compute_args_fix s pos_indb indb pos_ctor ctor key_uparams key_preds key_fixs key_args in
  mkApp ((getij_term s key_ctors pos_indb pos_ctor), Array.of_list args)

in

gen_rec_term



