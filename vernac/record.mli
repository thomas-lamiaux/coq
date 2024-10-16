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
open Vernacexpr
open Constrexpr
open Structures

module Ast : sig
  type t =
    { name : Names.lident
    ; is_coercion : coercion_flag
    ; binders: local_binder_expr list
    ; cfs : (local_decl_expr * record_field_attr) list
    ; idbuild : Id.t
    ; sort : constr_expr option
    ; default_inhabitant_id : Id.t option
    }
end

val definition_structure
  : flags:ComInductive.flags
  -> cumul_univ_decl_expr option
  -> inductive_kind
  -> primitive_proj:bool
  -> Ast.t list
  -> GlobRef.t list

  module Data : sig
    type projection_flags = {
      pf_coercion: bool;
      pf_reversible: bool;
      pf_instance: bool;
      pf_priority: int option;
      pf_locality: Goptions.option_locality;
      pf_canonical: bool;
    }
    type raw_data
    type t =
      { id : Id.t
      ; idbuild : Id.t
      ; is_coercion : bool
      ; proj_flags : projection_flags list
      ; rdata : raw_data
      ; inhabitant_id : Id.t
      }
  end

  (** A record is an inductive [mie] with extra metadata in [records] *)
  module Record_decl : sig
    type t = {
      mie : Entries.mutual_inductive_entry;
      default_dep_elim : DeclareInd.default_dep_elim list;
      records : Data.t list;
      (* TODO: this part could be factored in mie *)
      primitive_proj : bool;
      impls : DeclareInd.one_inductive_impls list;
      globnames : UState.named_universes_entry;
      global_univ_decls : Univ.ContextSet.t option;
      projunivs : Entries.universes_entry;
      ubinders : UnivNames.universe_binders;
      projections_kind : Decls.definition_object_kind;
      poly : bool;
      indlocs : Loc.t option list;
    }
end

(** Ast.t list at the constr level *)
val interp_structure
  : flags:ComInductive.flags
  -> cumul_univ_decl_expr option
  -> inductive_kind
  -> primitive_proj:bool
  -> Ast.t list
  -> Record_decl.t


val declare_existing_class : GlobRef.t -> unit

val canonical_inhabitant_id : isclass:bool -> Id.t -> Id.t

(* Implementation internals, consult Coq developers before using;
   current user Elpi, see https://github.com/LPCIC/coq-elpi/pull/151 *)
module Internal : sig
  type projection_flags = {
    pf_coercion: bool;
    pf_reversible: bool;
    pf_instance: bool;
    pf_priority: int option;
    pf_locality: Goptions.option_locality;
    pf_canonical: bool;
  }

  val declare_projections
    : Names.inductive
    -> Entries.universes_entry * UnivNames.universe_binders
    -> ?kind:Decls.definition_object_kind
    -> Names.Id.t
    -> projection_flags list
    -> Impargs.manual_implicits list
    -> Constr.rel_context
    -> Structure.projection list

  val declare_structure_entry : Structure.t -> unit

end
