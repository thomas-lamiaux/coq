- **Changed:**
  rewriting schemes for `eq·` and `eq_true` are explicitly declared in `Init.Logic`
  instead of dynamically when a tactic needs them.
  For instance `EqdepFacts.internal_eq_rew_dep` does not exist anymore and instead `Logic.eq_rew_dep` is available
  (`#21248 <https://github.com/rocq-prover/rocq/pull/21248>`_,
  by Gaëtan Gilbert).
