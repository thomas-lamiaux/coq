(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

let make_flag key v =
  let r = ref v in
  let () =
    Goptions.declare_bool_option {
      optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = key;
      optread  = (fun () -> !r);
      optwrite = (fun b -> r := b);
    }
  in
  r

(* detyping + extern + random stuff *)
let raw_print = make_flag ["Printing";"All"] false

(* detyping + extern + a few extra things (eg About) *)
(* XXX why does extern look at this flag? *)
let print_universes = make_flag ["Printing";"Universes"] false

(* detyping *)
let { Goptions.get = print_sort_quality } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Sort";"Qualities"]
    ~value:true
    ()

(* detyping *)
let print_evar_arguments = make_flag ["Printing";"Existential";"Instances"] false

(* detyping *)
let { Goptions.get = print_wildcard } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Wildcard"]
    ~value:true
    ()

(* detyping *)
let { Goptions.get = fast_name_generation } =
  Goptions.declare_bool_option_and_ref
    ~key:["Fast";"Name";"Printing"]
    ~value:false
    ()

(* detyping *)
let { Goptions.get = synthetize_type } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Synth"]
    ~value:true
    ()

(* detyping *)
let { Goptions.get = print_matching } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Matching"]
    ~value:true
    ()

(* detyping *)
let { Goptions.get = print_primproj_params } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Primitive";"Projection";"Parameters"]
    ~value:false
    ()

(* detyping *)
let { Goptions.get = print_unfolded_primproj_asmatch } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Unfolded";"Projection";"As";"Match"]
    ~value:false
    ()

(* detyping *)
let { Goptions.get = print_match_paramunivs } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Match";"All";"Subterms"]
    ~value:false
    ()

(* detyping *)
let { Goptions.get = print_relevances } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Relevance";"Marks"]
    ~value:false
    ()

(* detyping.ml but extern time *)
let { Goptions.get = print_factorize_match_patterns } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Factorizable";"Match";"Patterns"]
    ~value:true
    ()

(* detyping.ml but extern time *)
let print_allow_match_default_clause = make_flag ["Printing";"Allow";"Match";"Default";"Clause"] true

(* extern *)
let print_coercions = make_flag ["Printing";"Coercions"] false

(* extern + ppconstr *)
let print_parentheses = make_flag ["Printing";"Parentheses"] false

(* constant for now, TODO expose as a new option *)
(* extern *)
let print_implicits_explicit_args () = false

(* extern *)
let print_implicits = make_flag ["Printing";"Implicit"] false

(* extern *)
let print_implicits_defensive = make_flag ["Printing";"Implicit";"Defensive"] true

(* extern *)
let print_projections = make_flag ["Printing";"Projections"] false

(* extern *)
let print_no_symbol = ref false

let () =
  (* Printing Notations uses a negated ref for convenience in Himsg.explicit_flags *)
  Goptions.declare_bool_option
    { optstage = Summary.Stage.Interp;
      optdepr  = None;
      optkey   = ["Printing";"Notations"];
      optread  = (fun () -> not !print_no_symbol);
      optwrite = (fun b ->  print_no_symbol := not b);
    }

(* extern *)
let print_raw_literal = make_flag ["Printing";"Raw";"Literals"] false

(* extern *)
let { Goptions.get = print_use_implicit_types } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Use";"Implicit";"Types"]
    ~value:true
    ()

(* extern *)
let { Goptions.get = get_record_print } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Records"]
    ~value:true
    ()

(* extern *)
let { Goptions.get = print_float } =
  Goptions.declare_bool_option_and_ref
    ~key:["Printing";"Float"]
    ~value:true
    ()

module Detype = struct
  type t = {
    universes : bool;
    qualities : bool;
    relevances : bool;
    evar_instances : bool;
    wildcard : bool;
    fast_names : bool;
    synth_match_return : bool;
    matching : bool;
    primproj_params : bool;
    unfolded_primproj_as_match : bool;
    match_paramunivs : bool;
    always_regular_match_style : bool;
    (* XXX is there a better word than "nonpropositional"? *)
    nonpropositional_letin_types : bool;
  }

  let current_ignore_raw () = {
    universes = !print_universes;
    qualities = print_sort_quality();
    relevances = print_relevances();
    evar_instances = !print_evar_arguments;
    wildcard = print_wildcard();
    fast_names = fast_name_generation();
    synth_match_return = synthetize_type();
    matching = print_matching();
    primproj_params = print_primproj_params();
    unfolded_primproj_as_match = print_unfolded_primproj_asmatch();
    match_paramunivs = print_match_paramunivs();

    (* not yet exposed (except through Printing All) *)
    always_regular_match_style = false;
    nonpropositional_letin_types = false;
  }

  let make_raw flags = {
    flags with
    synth_match_return = false;
    always_regular_match_style = true;
    matching = false;
    nonpropositional_letin_types = true;
  }

  let current () =
    let flags = current_ignore_raw () in
    if !raw_print then make_raw flags else flags

end

module Extern = struct
  module FactorizeEqns = struct
    type t = {
      factorize_match_patterns : bool;
      allow_match_default_clause : bool;
    }

    let current_ignore_raw () = {
      factorize_match_patterns = print_factorize_match_patterns();
      allow_match_default_clause = !print_allow_match_default_clause;
    }

    (* all flags are overridden, but for forwards compat we still take
       the base flags *)
    let make_raw _flags = {
      factorize_match_patterns = false;
      allow_match_default_clause = false;
    }

    let current () =
      let flags = current_ignore_raw() in
      if !raw_print then make_raw flags else flags
  end

  type t = {
    use_implicit_types : bool;
    records : bool;
    (* XXX include the Printing Record & Printing Constructor tables
       here instead of force_record_constructors? *)
    force_record_constructors : bool;
    implicits : bool;
    implicits_explicit_args : bool;
    implicits_defensive : bool;
    coercions : bool;
    parentheses : bool;
    notations : bool;
    raw_literals : bool;
    projections : bool;
    float : bool;
    factorize_eqns : FactorizeEqns.t;
    (* XXX depth? *)
  }

  let current_ignore_raw () = {
    use_implicit_types = print_use_implicit_types();
    records = get_record_print();
    implicits = !print_implicits;
    implicits_explicit_args = print_implicits_explicit_args();
    implicits_defensive = !print_implicits_defensive;
    coercions = !print_coercions;
    parentheses = !print_parentheses;
    notations = not !print_no_symbol;
    raw_literals = !print_raw_literal;
    projections = !print_projections;
    float = print_float();
    factorize_eqns = FactorizeEqns.current_ignore_raw();

    (* not yet exposed (except through Printing All) *)
    force_record_constructors = false;
  }

  let make_raw flags = {
    flags with
    use_implicit_types = false;
    implicits = true;
    implicits_explicit_args = false;
    coercions = true;
    force_record_constructors = true;
    raw_literals = true;
    notations = false;
    projections = false;
    factorize_eqns = FactorizeEqns.make_raw flags.factorize_eqns;
  }

  let current () =
    let flags = current_ignore_raw() in
    if !raw_print then make_raw flags else flags
end


type t = {
  detype : Detype.t;
  extern : Extern.t;
}

let make_raw flags = {
  detype = Detype.make_raw flags.detype;
  extern = Extern.make_raw flags.extern;
}

let current () = {
  detype = Detype.current();
  extern = Extern.current();
}

let current_ignore_raw () = {
  detype = Detype.current_ignore_raw();
  extern = Extern.current_ignore_raw();
}
