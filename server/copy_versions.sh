#!/usr/bin/env sh

# Operate in the directory where this file is located
cd $(dirname $0)

# Copy relevant version info to the client to display Lean & mathlib version
# TODO: This is a bit hacky...
leanV=$( cat LeanProject/lean-toolchain | sed 's/.*://' )
currDate=$( date +"%s" )

cat LeanProject/lake-manifest.json | jq --arg d "$currDate" '. |= . + {time: $d}' | jq --arg leanV "$leanV" '.packages |= [{git: {name: "Lean", url: "https://github.com/leanprover/lean4-nightly/", rev: $leanV}}] + .' > ../client/public/package_versions.json

mkdir -p "../client/dist"
cp ../client/public/package_versions.json ../client/dist/package_versions.json
