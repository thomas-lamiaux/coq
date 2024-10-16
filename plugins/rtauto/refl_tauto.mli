(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)
(* raises Not_found if no proof is found *)


type atom_env=
    {mutable next:int;
     mutable env:(Constr.t*int) list}

val make_form
  :  Environ.env -> Evd.evar_map -> atom_env
  -> EConstr.types -> Proof_search.form

val make_hyps
  :  Environ.env -> Evd.evar_map
  -> atom_env
  -> EConstr.types list
  -> EConstr.named_context
  -> (Names.Id.t EConstr.binder_annot * Proof_search.form) list

val rtauto_tac : unit Proofview.tactic
