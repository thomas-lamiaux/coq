- **Fixed:**
  ``EConstr.contract_case`` no longer anomalies when Case branches
  contain evar-backed Lambda bodies (e.g., from ``Constr.in_context``)
  (`#22058 <https://github.com/rocq-prover/rocq/issues/22058>`_,
  by Jason Gross).
