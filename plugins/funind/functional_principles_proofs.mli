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

val prove_princ_for_struct :
     Evd.evar_map ref
  -> bool
  -> int
  -> Constant.t array
  -> EConstr.constr array
  -> int
  -> unit Proofview.tactic

val prove_principle_for_gen :
     Constant.t * Constant.t * Constant.t
  -> (* name of the function, the functional and the fixpoint equation *)
     Indfun_common.tcc_lemma_value ref
  -> (* a pointer to the obligation proofs lemma *)
     bool
  -> (* is that function uses measure *)
     int
  -> (* the number of recursive argument *)
     EConstr.types
  -> (* the type of the recursive argument *)
     EConstr.constr
  -> (* the wf relation used to prove the function *)
     unit Proofview.tactic

(* val is_pte  : rel_declaration -> bool  *)
