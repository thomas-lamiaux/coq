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
open Environ
open EConstr

(** Operations for handling terms under a local typing context. *)

open Evd

(** Variants of [Tacmach] functions built with the new proof engine *)

val pf_apply : (env -> evar_map -> 'a) -> Proofview.Goal.t -> 'a

val project : Proofview.Goal.t -> Evd.evar_map
[@@ocaml.deprecated "(9.2) Use Proofview.Goal.sigma"]

val pf_env : Proofview.Goal.t -> Environ.env
[@@ocaml.deprecated "(9.2) Use Proofview.Goal.env"]

val pf_concl : Proofview.Goal.t -> types
[@@ocaml.deprecated "(9.2) Use Proofview.Goal.concl"]

(** This function does no type inference and expects an already well-typed term.
    It recomputes its type in the fastest way possible (no conversion is ever involved) *)
val pf_get_type_of : Proofview.Goal.t -> constr -> types
[@@ocaml.deprecated "(9.2) Use Retyping.get_type_of"]

(** This function entirely type-checks the term and computes its type
    and the implied universe constraints. *)
val pf_type_of : Proofview.Goal.t -> constr -> evar_map * types
[@@ocaml.deprecated "(9.2) Use Typing.type_of"]

val pf_conv_x : Proofview.Goal.t -> t -> t -> bool
[@@ocaml.deprecated "(9.2) Use Reductionops.is_conv"]

val pf_get_new_id  : Id.t -> Proofview.Goal.t -> Id.t
val pf_ids_of_hyps : Proofview.Goal.t -> Id.t list
val pf_ids_set_of_hyps : Proofview.Goal.t -> Id.Set.t

val pf_hyps_types : Proofview.Goal.t -> (Id.t * types) list
[@@ocaml.deprecated "(9.2) Use EConstr.named_context"]

val pf_get_hyp : Id.t -> Proofview.Goal.t -> named_declaration
val pf_get_hyp_typ        : Id.t -> Proofview.Goal.t -> types
val pf_last_hyp           : Proofview.Goal.t -> named_declaration
[@@ocaml.deprecated "(9.2) Use EConstr.named_context"]

val pf_nf_concl : Proofview.Goal.t -> types
[@@ocaml.deprecated "(9.2) Use Reductionops.nf_evar"]

val pf_hnf_constr : Proofview.Goal.t -> constr -> types
[@@ocaml.deprecated "(9.2) Use Tacred.hnf_constr"]

val pf_hnf_type_of : Proofview.Goal.t -> constr -> types
[@@ocaml.deprecated "(9.2) Use Reductionops.whd_all and Retyping.get_type_of"]

val pf_compute : Proofview.Goal.t -> constr -> constr
[@@ocaml.deprecated "(9.2) Use Tacred.pf_compute"]

val pf_whd_compute : Proofview.Goal.t -> constr -> constr
[@@ocaml.deprecated "(9.2) Use Tacred.whd_compute"]

val pf_nf_evar : Proofview.Goal.t -> constr -> constr
[@@ocaml.deprecated "(9.2) Use Reductionops.nf_evar"]

val pr_gls : Proofview.Goal.t -> Pp.t
[@@ocaml.deprecated "(9.2) Use Printer.pr_evar"]
