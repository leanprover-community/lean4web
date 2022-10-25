#!/usr/bin/env sh

# Operate in the directory where this file is located
cd $(dirname $0)

# Build elan image if not already present
docker build --pull --rm -f elan.Dockerfile -t elan:latest .
