#!/usr/bin/env bash

SECONDS=0
echo "Starting build." | logger -t lean4web

# Operate in the directory where this file is located
cd $(dirname $0)

# Updating Mathlib: We follow the instructions at
# https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency#updating-mathlib4
# Additionally, we had once problems with the `lake-manifest` when a new dependency got added
# to `mathlib`, therefore we now delete it every time for good measure.
( cd LeanProject &&
  lake update -R &&
  lake build)

  # note: mathlib has now a post-update hook that modifies the `lean-toolchain`
  # and calls `lake exe cache get`. Therefore these two steps are currently superfluous.

duration=$SECONDS
echo "Finished in $(($duration / 60)):$(($duration % 60)) min."
echo "Finished in $(($duration / 60)):$(($duration % 60)) min." | logger -t lean4web
