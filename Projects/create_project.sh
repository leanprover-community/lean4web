#!/bin/bash
# Exit on error
set -e

cd "$(dirname "$0")"

# Check if version argument is provided
if [ -z "$1" ]; then
    echo "Error: Please provide a Lean version number"
    echo "Usage: $0 <version>"
    exit 1
fi

lean_version=$1

# Validate version format and add 'v' prefix if missing
if [[ ! $lean_version =~ ^v?4\.[0-9]+\.[0-9]+$ ]]; then
    echo "Error: Invalid version format. Must be v4.x.x or 4.x.x"
    exit 1
fi

# Add 'v' prefix if missing
[[ $lean_version != v* ]] && lean_version="v$lean_version"

# Check if version directory already exists
if [ -d "$lean_version" ]; then
    read -p "Directory $lean_version already exists. Overwrite? (y/N) " -n 1 -r
    echo
    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        echo "Operation cancelled."
        exit 1
    fi
fi

# Create temporary directory
temp_dir=$(mktemp -d)
trap 'rm -rf "$temp_dir"' EXIT

echo "Creating new Lean 4 project of version $lean_version..."
pushd "$temp_dir"

# Create new project
lake new lean4web math.lean

pushd lean4web

# Set lean-toolchain version
echo leanprover/lean4:$lean_version > lean-toolchain

# Update lakefile.lean
echo "Updating lakefile.lean..."
cat > lakefile.lean << EOF
import Lake
open Lake DSL

package «lean4web» where
  -- add any additional package configuration options here

require mathlib from git
   "https://github.com/leanprover-community/mathlib4.git" @ "$lean_version"

@[default_target]
lean_lib «Lean4web» where
  -- add any library configuration options here
EOF

# Update dependencies and build
echo "Updating dependencies..."
lake update -R || { echo "Error: lake update failed"; exit 1; }

echo "Getting cache..."
lake exe cache get || { echo "Error: cache download failed"; exit 1; }

echo "Building project..."
lake build || { echo "Error: build failed"; exit 1; }

# If everything succeeded, move to final location
popd
popd

rm -rf "$lean_version" 2>/dev/null || true
mv "$temp_dir/lean4web" "$lean_version"

echo "Setup completed successfully!"