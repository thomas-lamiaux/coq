- **Deprecated:**
  syntactic classes parsing terms (`constr`, `lconstr`, etc.)
  taking more than one :n:`@scope_key` argument without qualifying it with `delimiters`
  (e.g. `constr(type, function)` should be `constr(delimiters(type, function))`
  but a single argument like `constr(type)` is not deprecated).
  See :n:`@ltac2_constr_synclass_arg`
  (`#21285 <https://github.com/rocq-prover/rocq/pull/21285>`_,
  by Gaëtan Gilbert).
