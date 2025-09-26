#!/usr/bin/env bash

CI_QUIET=1

set +x

ci_dir="$(dirname "$0")"
. "${ci_dir}/scripts/ci-common.sh"

# [git_reset <project>] will reset the repository for <project> to the upstream branch
git_reset()
{
  local project=$1
  local dest="${CI_BUILD_DIR}/$project"
  local ref_var="${project}_CI_REF"
  local ref="${!ref_var}"

  echo "Resetting $project..."

  if [ ! -d "$dest" ]; then
    echo "Warning: reset of $project skipped because $dest does not exist."
  else
    # TODO: properly handle submodules
    pushd "$dest" > /dev/null
    # check that the reference is an actual branch
    local ref_hash=$(git rev-parse --verify --quiet "refs/heads/$ref")
    if [ -n "$ref_hash" ]; then
      git reset --hard --quiet
      git checkout $ref --quiet
      git reset --hard "origin/$ref" --quiet
      echo "$project reset to $ref ($ref_hash)"
    fi
    popd > /dev/null
  fi
}

git_reset_all() {
  for project in "${projects[@]}"; do
    if [ -d "${CI_BUILD_DIR}/$project" ]; then
      git_reset $project
    fi
  done
}

if [ -n "$1" ]; then
  git_reset "$1"
else
  git_reset_all
fi
