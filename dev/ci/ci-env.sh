#!/usr/bin/env bash

if which cygpath >/dev/null 2>&1; then OCAMLFINDSEP=\;; else OCAMLFINDSEP=:; fi

# We can remove setting ROCQLIB and ROCQRUNTIMELIB from here, but better to
# wait until we have merged the coq.boot patch so we can do this in a
# more controlled way.
if [ -n "${GITLAB_CI}" ];
then
    # Gitlab build, Rocq installed into `_install_ci`
    export COQBIN="$PWD/_install_ci/bin"
    export OCAMLPATH="$PWD/_install_ci/lib$OCAMLFINDSEP$OCAMLPATH"
    export PATH="$PWD/_install_ci/bin:$PATH"

    # Where we install external binaries and ocaml libraries
    # also generally used for dune install --prefix so needs to match coq's expected user-contrib path
    CI_INSTALL_DIR="$PWD/_install_ci"

    export CI_BRANCH="$CI_COMMIT_REF_NAME"
    if [[ ${CI_BRANCH#pr-} =~ ^[0-9]*$ ]]
    then
        export CI_PULL_REQUEST="${CI_BRANCH#pr-}"
    fi
elif [ -d "$PWD/_build/install/default/" ];
then
    # Full Dune build, we basically do what `dune exec --` does
    export OCAMLPATH="$PWD/_build/install/default/lib/$OCAMLFINDSEP$OCAMLPATH"
    export COQBIN="$PWD/_build/install/default/bin"
    export ROCQLIB="$PWD/_build/install/default/lib/coq"
    export ROCQRUNTIMELIB="$PWD/_build/install/default/lib/rocq-runtime"

    CI_INSTALL_DIR="$PWD/_build/install/default/"

    CI_BRANCH="$(git rev-parse --abbrev-ref HEAD)"
    export CI_BRANCH
fi

export PATH="$COQBIN:$PATH"

# Rocq's tools need an ending slash :S, we should fix them.
export COQBIN="$COQBIN/"
