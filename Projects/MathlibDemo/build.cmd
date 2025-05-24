REM @echo off
setlocal enabledelayedexpansion

REM Operate in the directory where this file is located
cd /d "%~dp0"

REM Updating Mathlib: We follow the instructions at
REM https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency#updating-mathlib4

REM Note: we had once problems with the `lake-manifest` when a new dependency got added
REM to `mathlib`, we may need to add `rm lake-manifest.json` again if that's still a problem.

REM currently the mathlib post-update-hook is not good enough to update the lean-toolchain.
REM things break if the new lakefile is not valid in the old lean version
curl -L https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain

REM note: mathlib has now a post-update hook that modifies the `lean-toolchain`
REM and calls `lake exe cache get`.

lake update -R
lake build
lake build Batteries
