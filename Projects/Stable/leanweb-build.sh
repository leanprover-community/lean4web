#!/usr/bin/env bash

# Operate in the directory where this file is located
cd $(dirname $0)

lake update -R
lake build
