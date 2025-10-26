open Names
open Declarations
open Context
open EConstr
module RelDecl = Rel.Declaration
open RelDecl
open NamedAPI

(* Differences with ind_rect:

-> no-dep is not supported
-> let in params are not unfolded

*)



let gen_rec env sigma kn u mdecl sort_pred =
  (* sort pred specify the output sorts of the induction predicates *)

  let pred_relevance = Retyping.relevance_of_sort sort_pred in
  (*  universes *)
  (* let u = EInstance.make @@ UVars.make_abstract_instance @@ Declareops.universes_context mdecl.mind_universes in *)

  (* simplified make_ind for keys *)
  let make_ind_keys s pos_indb keys_uparams keys_nuparams keys_indices =
    make_ind s (kn, pos_indb) u keys_uparams (get_terms s keys_nuparams) (get_terms s keys_indices)
  in

  (* ################################# *)
  (*     1. Predicates                 *)
  (* ################################# *)


  (* 1.1. Builds the type of the predicate for the i-th block
    forall (B0 : R0) ... (Bm : Rm),
    forall (i1 : t1) ... (il : tl),
    (Ind A1 ... An B0 ... Bm i1 ... il) -> U)  *)
  let make_type_pred s pos_indb indb keys_uparams : constr =
    let* (s, keys_nuparams, _, _) = closure_nuparams mkProd mdecl s in
    let* (s, keys_indices , _, _) = closure_indices mkProd s indb in
    let ind = make_ind_keys s pos_indb keys_uparams keys_nuparams keys_indices in
    mkProd ((make_annot Anonymous (ERelevance.make indb.mind_relevance)), ind, mkSort sort_pred)
  in

  (* closure version *)
  let closure_preds binder s keys_uparams =
    iterate_inductives s mdecl
      (fun s pos_indb indb cc ->
        let name_pred = make_annot (Name.Name (Id.of_string "P")) ERelevance.relevant in
        mk_binder binder s name_pred (make_type_pred s pos_indb indb keys_uparams) cc
    )
  in


  (* ################################# *)
  (*     2. Assumption Functions       *)
  (* ################################# *)

  (* This function computes the type of the recursive call *)
  let make_rec_call s key_preds key_arg ty : constr option =
    (* Format.printf "\n BEGIN: view"; *)
    let x = view_arg kn mdecl s sigma ty in
    (* Format.printf "\n END: view \n"; *)
    match x with
    | ArgIsInd (pos_ind, loc, inst_nuparams, inst_indices) ->
        Some (
          (* Pi B0 ... Bm i0 ... il (x a0 ... an) *)
          let* (s, key_locals, _, _) = closure_old_context_sep mkProd s loc in
          let pred = mkApp ((geti_term s key_preds pos_ind), (Array.append inst_nuparams inst_indices)) in
          let arg = mkApp (get_term s key_arg, Array.of_list (get_terms s key_locals)) in
          mkApp (pred, Array.make 1 arg)
        )
    | _ -> None
  in

  (* Create and bind the recursive call *)
  let make_rec_call_cc key_preds s _ key_arg cc =
    let env = Environ.push_rel_context (EConstr.Unsafe.to_rel_context s.state_context) env in
    let red_ty = Reductionops.whd_all env sigma (get_type s key_arg) in
    match make_rec_call s key_preds key_arg red_ty with
    | Some ty -> let name_rec_hyp = make_annot Anonymous pred_relevance in
                  mk_tProd s name_rec_hyp ty (fun (s, key_rec) -> cc s [key_arg])
    | _ -> cc s [key_arg]
  in

  (* 1.2.2 Generates the type associated to a constructor *)
  (* forall (B0 : R0) ... (Bm : Rm),
    forall x0 : t0, [P x0], ..., xn : tn, [P n],
    P B0 ... Bm f0 ... fl (cst A0 ... An B0 ... Bm x0 ... xl) *)
  let make_type_ctor s pos_indb indb pos_ctor ctor keys_uparams key_preds =
    (* Format.printf "\n BEGIN: closure nup"; *)
    let* (s, keys_nuparams, _, _) = closure_nuparams mkProd mdecl s in
    (* Format.printf "\n END: closure nup \n"; *)
    let (cxt, indices) = ctor in
    (* Format.printf "\n BEGIN: closure args"; *)
    let* (s, key_args) = read_by_decl s cxt kp_tLetIn (fun s _ _ cc -> cc s []) kp_tProd (make_rec_call_cc key_preds) in
    (* Format.printf "\n END: closure args \n"; *)
    let indices = Array.map (weaken s) indices in
    let pred = mkApp ((geti_term s key_preds pos_indb), Array.append (Array.of_list (get_terms s keys_nuparams)) indices) in
    let cst = make_cst s (kn, pos_indb) u pos_ctor keys_uparams (get_terms s keys_nuparams) (get_terms s key_args) in
    mkApp (pred, Array.make 1 cst)
  in

  (* closure assumptions functions over all the ctors *)
  let closure_ctors binder s sigma keys_uparams key_preds cc =
    iterate_all_ctors s kn mdecl sigma (
      fun s pos_indb indb pos_ctor ctor cc ->
      let name_assumption = make_annot (Name indb.mind_consnames.(pos_ctor)) pred_relevance in
      let fct = make_type_ctor s pos_indb indb pos_ctor ctor keys_uparams key_preds in
      mk_binder binder s name_assumption fct cc
    ) cc
  in


  (* ################################# *)
  (*          3. Return Types          *)
  (* ################################# *)

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
      let* (s, keys_nuparams, _, _) = closure_nuparams mkProd mdecl s in
      let* (s, keys_indices , _, _) = closure_indices mkProd s indb in
      let ind = make_ind_keys s pos_indb keys_uparams keys_nuparams keys_indices in
      let* (s, key_VarMatch) = mk_tProd s (make_annot Anonymous (ERelevance.make indb.mind_relevance)) ind in
      make_ccl s key_preds pos_indb keys_nuparams keys_indices key_VarMatch
  in


  (* ####################################### *)
  (*    4. Make the type of the recursors    *)
  (* ####################################### *)

  let gen_rec_type pos_indb =
    Format.printf "################################################## \n";
    Format.printf "\n ### PP rec # Type: %s # block %n ### \n" (MutInd.to_string kn) pos_indb ;
    Feedback.msg_info (Termops.Internal.print_constr_env env sigma (mkSort sort_pred));
    let t =
      let s = init_state in
      let indb = mdecl.mind_packets.(pos_indb) in
      let* (s, key_uparams, _, _) = closure_uparams mkProd mdecl s in
      (* Format.printf "\n     SUCESS: closure up     \n "; *)
      let* (s, key_preds)   = closure_preds mkProd s key_uparams in
      (* Format.printf "\n     SUCESS: closure preds     \n "; *)
      let* (s, key_ctors)   = closure_ctors mkProd s sigma key_uparams key_preds in
      (* Format.printf "\n     SUCESS: closure ctors     \n "; *)
      make_return_type s pos_indb indb key_uparams key_preds
    in
    (* Format.printf "\n ------------------------------------------------------------- \n";
    Feedback.msg_info (Termops.Internal.debug_print_constr sigma t);
    Format.printf "\n" ; *)
    Format.printf "\n ------------------------------------------------------------- \n";
    Feedback.msg_info (Termops.Internal.print_constr_env env sigma t);
    Format.printf "\n \n" ;
    t
  in






(* ####################################### *)
(*    5. Make the term of the recursors    *)
(* ####################################### *)

  let make_rec_call key_fixs s key_arg ty : constr option =
    match view_arg kn mdecl s sigma ty with
    | ArgIsInd (pos_ind, loc, inst_nuparams, inst_indices) ->
        Some (
          (* Fi B0 ... Bm i0 ... il (x a0 ... an) *)
          let* (s, key_locals, _, _) = closure_old_context_sep mkLambda s loc in
          let fix = mkApp ((geti_term s key_fixs pos_ind), (Array.append inst_nuparams inst_indices)) in
          let arg = mkApp (get_term s key_arg, Array.of_list (get_terms s key_locals)) in
          mkApp (fix, Array.make 1 arg)
        )
    | _ -> None
  in

  (* 3.1 Compute the arguments of the rec call *)
  let compute_args_fix pos_ctor s key_fixs key_args =
    CList.fold_right_i (fun pos_arg key_arg t ->
      let ty_arg = get_type s key_arg in
      (* Format.printf "\n ------------------------------------------------------------- \n";
      Format.printf "pos arg : %n | key_arg : %n \n" pos_arg key_arg;
      Feedback.msg_info (Termops.Internal.debug_print_constr sigma ty_arg);
      Format.printf "\n" ; *)
      let env = Environ.push_rel_context (EConstr.Unsafe.to_rel_context s.state_context) env in
      let red_ty = Reductionops.whd_all env sigma ty_arg in
      match make_rec_call key_fixs s key_arg red_ty with
        | Some rc_tm -> (get_term s key_arg) :: rc_tm :: t
        | None -> (get_term s key_arg) :: t
    ) 0 key_args []
    in

let debug_cxt s n cxt  =
  Format.printf "\n BEGIN DEBUG %s: %n \n" s n;
  List.fold_left (fun _ x ->
    match x with
    | LocalAssum (_, ty) ->
      Feedback.msg_info (Termops.Internal.debug_print_constr sigma ty)
    | _ -> ()
    ) () cxt ;
  Format.printf "\n END DEBUG %s \n" s;
    in

(* 3.2 Generates the recursor *)
let gen_rec_term pos_indb =

  Format.printf "################################################## \n";
  Format.printf "\n ### PP rec # Type: %s # block %n ### \n" (MutInd.to_string kn) pos_indb ;
  Feedback.msg_info (Termops.Internal.print_constr_env env sigma (mkSort sort_pred));
  (* Format.printf "IS ALLOWED ELIMINATION: %b" (Inductiveops.is_allowed_elimination sigma ((mdecl, mdecl.mind_packets.(0)), u) sort_pred); *)
  (* let b = Array.fold_right (fun mipi b -> b && Inductiveops.is_allowed_elimination sigma ((mdecl,mipi),u) sort_pred) mdecl.mind_packets true in
  Format.printf "IS ALLOWED ELIMINATION: %b" b; *)

  let t =
  (* 0. Initialise state with inductives *)
  let s = init_state in
  (* 1. Closure Uparams / preds / ctors *)
  let* (s, key_uparams, _, _) = closure_uparams mkLambda mdecl s in
  let* (s, key_preds)   = closure_preds   mkLambda s key_uparams in
  let* (s, key_ctors)   = closure_ctors   mkLambda s sigma key_uparams key_preds in
  (* 2. Fixpoint *)
  let tFix_name pos_indb indb = make_annot (Name.Name (Id.of_string "F")) pred_relevance in
  let tFix_type s pos_indb indb = make_return_type s pos_indb indb key_uparams key_preds in
  let tFix_rarg pos_indb indb = default_rarg mdecl indb in
  let* (s, key_fixs, pos_indb, indb) = mk_tFix env sigma mdecl kn s tFix_rarg pos_indb tFix_name tFix_type in
  (* 3. Closure Nuparams / Indices / Var *)
  let* (s, key_nuparams, _, _) = closure_nuparams mkLambda mdecl s in
  let* (s, key_indices , _, _) = closure_indices  mkLambda s indb in
  let* (s, key_VarMatch) = mk_tLambda s (make_annot Anonymous (ERelevance.make indb.mind_relevance))
                          (make_ind_keys s pos_indb key_uparams key_nuparams key_indices) in
  (* 4. Proof of P ... x by match *)
  let params = Array.of_list (get_terms s key_uparams @ get_terms s key_nuparams) in
  let tCase_pred s keys_fresh_indices key_var_match = make_ccl s key_preds pos_indb key_nuparams keys_fresh_indices key_var_match in
  let* (s, key_args, key_letin, key_both, pos_ctor) =
    mk_tCase env sigma s mdecl (kn, pos_indb) indb u key_uparams key_nuparams params
          tCase_pred pred_relevance (get_term s key_VarMatch) in
  (* 5. Make the branch *)
  let args = get_terms s key_nuparams @ compute_args_fix pos_ctor s key_fixs key_args  in
  mkApp ((getij_term s key_ctors pos_indb pos_ctor), Array.of_list args)

in
Format.printf "\n ------------------------------------------------------------- \n";
Feedback.msg_info (Termops.Internal.debug_print_constr sigma t);
Format.printf "\n" ;
(* Format.printf "\n ------------------------------------------------------------- \n";
Feedback.msg_info (Termops.Internal.print_constr_env env sigma t);
Format.printf "\n \n" ; *)
  t
in

(* gen_rec_term *)
gen_rec_type


