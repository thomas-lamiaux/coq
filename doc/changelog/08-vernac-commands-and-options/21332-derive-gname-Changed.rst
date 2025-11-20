- **Changed:**
  :cmd:`Derive` names the existential variables it generates according using the name of the constant they will define
  (e.g. `Derive X in X as x` binds `X` to an evar named `?X` instead of an anonymous evar (which would print as `?Goal`))
  (`#21332 <https://github.com/rocq-prover/rocq/pull/21332>`_,
  by Gaëtan Gilbert).
