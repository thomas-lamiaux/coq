(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Constr
open Conversion

(**********************************************************************
  s conversion functions *)
val vm_conv : conv_pb -> types kernel_conversion_function

(** A conversion function parametrized by a universe comparator and
   evar normalizer. Used outside of the kernel. *)
val vm_conv_gen : conv_pb -> Genlambda.evars -> Environ.env -> ('a, 'err) generic_conversion_function
