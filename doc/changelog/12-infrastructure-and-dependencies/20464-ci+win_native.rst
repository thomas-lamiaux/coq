- **Added:** Experimental support for native Windows builds.
  Rocq can now build and run under a native Windows environment using
  the new native Windows support in Opam 2.3. This setup is tested in
  CI, running a large part of the test suite. Beware this support is
  still experimental, and some problem may arise on Unix-specific
  tools. Note that RocqIDE is still not supported (c.f. `#20631
  <https://github.com/rocq-prover/rocq/issues/20631>`_) (`#20464
  <https://github.com/rocq-prover/rocq/pull/20464>`_, by Emilio Jesus
  Gallego Arias, Gaëtan Gilbert, David Allsopp, Ali Caglayan, Jason
  Gross, the Opam team, the @setup-ocaml team, the OCaml team).
