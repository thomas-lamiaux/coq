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
open Environ
open Evd

(** Eliminations *)
type dep_flag = bool

(** Errors related to recursors building *)
type recursion_scheme_error =
  | NotAllowedCaseAnalysis of evar_map * (*isrec:*) bool * Sorts.t * Constr.pinductive
  | NotMutualInScheme of inductive * inductive
  | DuplicateInductiveBlock of inductive
  | NotAllowedDependentAnalysis of (*isrec:*) bool * inductive

exception RecursionSchemeError of env * recursion_scheme_error

val build_case_analysis_scheme : env -> Evd.evar_map -> inductive puniverses ->
  dep_flag -> ESorts.t -> evar_map * constr * constr

(** Builds a recursive induction scheme (Peano-induction style) in the given sort.  *)
val build_induction_scheme : env -> evar_map -> inductive puniverses ->
  dep_flag -> ESorts.t -> evar_map * constr

(** Builds mutual (recursive) induction schemes *)
val build_mutual_induction_scheme :
  env -> evar_map -> ?force_mutual:bool ->
  (inductive * dep_flag * EConstr.ESorts.t) list -> einstance -> evar_map * constr list
