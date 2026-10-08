Debugging from Rocq toplevel using OCaml toplevel
======================================================

1. Launch bytecode version of Rocq (`dune exec -- rocq repl-with-drop`)
2. Access OCaml toplevel using vernacular command `Drop.`
3. Use `#trace` to tell which function(s) to trace,
   or type any other OCaml toplevel commands or OCaml expressions
4. Go back to Rocq toplevel with `#quit;;` or `#go;;`
5. Test your Rocq command and observe the result of tracing your functions
6. Freely switch from Rocq to OCaml toplevels with `Drop.` and `#quit;;`/`#go;;`

> [!NOTE]
> To access plugin modules in the OCaml toplevel, you have to
> use names such as `Ltac_plugin__Tacinterp`.

> [!TIP]
> To remove high-level pretty-printing features (coercions,
> notations, ...), use `Set Printing All`. It will affect the `#trace`
> printers too.


Debugging with ocamldebug from Emacs or command line
====================================================

See [build-system.dune.md#ocamldebug](build-system.dune.md#ocamldebug)

Global gprof-based profiling
============================

Rocq must be configured with option `-profile`.

1. Run native Rocq which must end normally (use `Quit` or option `-batch`)
2. `gprof ./coqtop gmon.out`

Per function profiling
======================

See the documentation in `lib/newProfile.mli`.

Finding repeated fixpoint guard checks
=====================================

The `guard-check` debug component records successful checks of individual
fixpoint bodies. It is disabled by default. For a library built with a generated
Makefile, enable it for every compiler invocation and summarize the combined log:

```bash
make clean
make -j4 COQEXTRAFLAGS="-d guard-check" all > guard-build.log 2>&1
python3 /path/to/rocq/dev/tools/guard-check-stats.py --root "$PWD" guard-build.log > guard-checks.md
```

No `.v` files need editing. Command-line Make variables propagate to recursive
Make invocations, including libraries with several subdirectories. If the build
already needs `COQEXTRAFLAGS`, retain those flags alongside `-d guard-check`.
Ensure the build uses the instrumented Rocq executable. Incremental builds only
measure recompiled files; clean first to cover the whole library. Check the build
exit status before treating its log as a complete library measurement.

The script prints **File name | Fixpoint name | Number of guard checks**. It
accepts multiple log filenames, or stdin when no filenames are provided. Paths
are retained by default; `--root` shortens paths within a source directory.
Logs with no recorded checks produce an empty table. Files with zero checks do
not have event records and are absent from the table. Supplying the same log
twice, or concatenating two builds, counts both runs.

For a single file, use `rocq compile -d guard-check file.v`. Within a file,
`Set Debug "guard-check".` and `Set Debug "-guard-check".` select an interval.
Collected records are printed at compiler exit, even if the component was
subsequently disabled or compilation failed. This collection/reporting path is
for `rocq compile`, rather than interactive proof sessions. Records have the form
`ROCQ_GUARD_CHECK {"file":"...","name":"..."}`; the script also accepts the
compiler's `Debug:` prefix.

One event means one successfully checked fixpoint body, not one unique definition
or one complete type check. Repeated occurrences and successful checks during
tactic attempts that later backtrack are retained. A mutual block contributes
one event for each body that passes. Rejected checks, cofixpoints, and checks
disabled by typing flags are excluded. Names are local binder names, not global
constant identifiers: unrelated binders with the same name in the same file
share a row, and anonymous binders are printed as `_`. The table is a diagnostic
for investigating unexpectedly frequent checking, not proof that each counted
check is avoidable. This workflow collects no compilation timings.
