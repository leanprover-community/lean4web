#!/usr/bin/env sh

# Operate in the directory where this file is located
cd $(dirname $0)

(cd LeanProject && lake build)

# Build elan image if not already present
docker build --pull --rm -f lean.Dockerfile -t lean:latest .
