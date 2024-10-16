(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

type xml = Xml_datatype.xml

type t
type target = TChannel of out_channel | TBuffer of Buffer.t

val make : target -> t

(** Print the xml data structure to a source into a compact xml string (without
 any user-readable formatting ). *)
val print : t -> xml -> unit

(** Print the xml data structure into a compact xml string (without
 any user-readable formatting ). *)
val to_string : xml -> string

(** Print the xml data structure into an user-readable string with
 tabs and lines break between different nodes. *)
val to_string_fmt : xml -> string

(** Print PCDATA as a string by escaping XML entities. *)
val pcdata_to_string : string -> string
