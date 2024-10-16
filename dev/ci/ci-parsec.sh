#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download parsec

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/parsec"
  dune build -p coq-parsec @install
  dune install -p coq-parsec --prefix=$CI_INSTALL_DIR
)
