(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Proof

(**********************************************************************)
(* Shortcut to build a term using tactics *)

let refine_by_tactic ~name ~poly env sigma ty tac =
  (* Save the initial side-effects to restore them afterwards. *)
  let eff = Evd.eval_side_effects sigma in
  let old_len = Safe_typing.length_private @@ Evd.seff_private eff in
  (* Save the existing goals *)
  let sigma = Evd.push_future_goals sigma in
  (* Start a proof *)
  let prf = start ~name ~poly sigma [env, ty] in
  let (prf, _, ()) =
    try run_tactic env tac prf
    with Logic_monad.TacticFailure e as src ->
      (* Catch the inner error of the monad tactic *)
      let (_, info) = Exninfo.capture src in
      Exninfo.iraise (e, info)
  in
  (* Plug back the retrieved sigma *)
  let { goals; stack; sigma; entry } = data prf in
  assert (stack = []);
  let ans = match Proofview.initial_goals entry with
  | [_, c, _] -> c
  | _ -> assert false
  in
  let ans = EConstr.to_constr ~abort_on_undefined_evars:false sigma ans in
  (* [neff] contains the freshly generated side-effects *)
  let neff = Evd.seff_private @@ Evd.eval_side_effects sigma in
  let new_len = Safe_typing.length_private neff in
  let neff, _ = Safe_typing.pop_private neff (new_len - old_len) in
  (* Reset the old side-effects *)
  let sigma = Evd.set_side_effects eff sigma in
  (* Restore former goals *)
  let _goals, sigma = Evd.pop_future_goals sigma in
  (* Push remaining goals as future_goals which is the only way we
     have to inform the caller that there are goals to collect while
     not being encapsulated in the monad *)
  let sigma = List.fold_right Evd.declare_future_goal goals sigma in
  (* Get rid of the fresh side-effects by internalizing them in the term
     itself. Note that this is unsound, because the tactic may have solved
     other goals that were already present during its invocation, so that
     those goals rely on effects that are not present anymore. Hopefully,
     this hack will work in most cases. *)
  let (ans, uctx) = Safe_typing.inline_private_constants env ((ans, Univ.ContextSet.empty), neff) in
  let sigma = Evd.merge_universe_context_set ~sideff:true UState.UnivRigid sigma uctx in
  EConstr.of_constr ans, sigma
