#!/usr/bin/env bash

set -e

ci_dir="$(dirname "$0")"
. "${ci_dir}/ci-common.sh"

git_download rocq_extraction_scala

if [ "$DOWNLOAD_ONLY" ]; then exit 0; fi

( cd "${CI_BUILD_DIR}/rocq_extraction_scala"
  dune build @install @runtest -p rocq-extraction-scala
)
