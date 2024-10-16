(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let kind_filter str =
  let kinds = [ "--kind=proof"; "--kind=tactic"; "--kind=query" ] in
  not (List.exists (String.equal str) kinds)

let worker_parse_extra extra_args =
  let stm_opts, extra_args = Stmargs.parse_args ~init:Stm.AsyncOpts.default_opts extra_args in
  let extra_args = List.filter kind_filter extra_args in
  ((),stm_opts), extra_args

let worker_init init ((),stm_opts)  injections ~opts : Vernac.State.t =
  Flags.quiet := true;
  init ();
  Coqtop.init_toploop opts stm_opts injections

let usage = Boot.Usage.{
  executable_name = "coqworker";
  extra_args = "";
  extra_options = ("\n" ^ "coqworker" ^ " specific options:\
\n  --xml_format=Ppcmds    serialize pretty printing messages using the std_ppcmds format\n");
}

let start ~init ~loop =
  let open Coqtop in
  let custom = {
    parse_extra = worker_parse_extra;
    usage;
    initial_args = Coqargs.default;
    init_extra = worker_init init;
    run = (fun ((),_) ~opts:_ (_state : Vernac.State.t) ->
      (* the state is not used since the worker will receive one from master *)
      loop ());
  } in
  start_coq custom
