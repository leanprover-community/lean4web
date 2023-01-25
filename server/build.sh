#!/usr/bin/env sh

# Operate in the directory where this file is located
cd $(dirname $0)

(cd LeanProject &&
  lake update && # download latest mathlib
  cp ./lake-packages/mathlib/lean-toolchain . # copy lean version of mathlib
  lake exe cache get
  lake build)

# Build elan image if not already present
docker build --pull --rm -f lean.Dockerfile -t lean:latest .

# Copy info about new versions to the client.
./copy_versions.sh
