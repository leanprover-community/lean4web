#!/usr/bin/env bash

SECONDS=0
echo "Starting build." | logger -t lean4web

# Operate in the directory where this file is located
cd $(dirname $0)

# Updating Mathlib: We follow the instructions at
# https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency#updating-mathlib4
# Additionally, we had once problems with the `lake-manifest` when a new dependency got added
# to `mathlib`, therefore we now delete it every time for good measure.
(cd LeanProject &&
  rm -f ./lake-manifest.json &&
  curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain &&
  lake update &&
  lake exe cache get &&
  lake build)

# Copy info about new versions to the client.
./copy_versions.sh

duration=$SECONDS
echo "Finished in $(($duration / 60)):$(($duration % 60)) min."
echo "Finished in $(($duration / 60)):$(($duration % 60)) min." | logger -t lean4web
