(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val refine_by_tactic
  :  name:Names.Id.t
  -> poly:PolyFlags.t
  -> Environ.env
  -> Evd.evar_map
  -> EConstr.types
  -> unit Proofview.tactic
  -> EConstr.constr * Evd.evar_map
(** A variant of {!Proof.solve} that handles open terms as well.
    Caveat: all effects are purged in the returned term at the end, but other
    evars solved by side-effects are NOT purged, so that unexpected failures may
    occur. Ideally all code using this function should be rewritten in the
    monad. *)
