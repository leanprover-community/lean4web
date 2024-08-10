#!/usr/bin/env bash

# Operate in the directory where this file is located
cd $(dirname $0)

# Updating Mathlib: We follow the instructions at
# https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency#updating-mathlib4

# Note: we had once problems with the `lake-manifest` when a new dependency got added
# to `mathlib`, we may need to add `rm lake-manifest.json` again if that's still a problem.

# currently the mathlib post-update-hook is not good enough to update the lean-toolchain.
# things break if the new lakefile is not valid in the old lean version
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain

# note: mathlib has now a post-update hook that modifies the `lean-toolchain`
# and calls `lake exe cache get`.

lake update -R
lake build
lake build Batteries
