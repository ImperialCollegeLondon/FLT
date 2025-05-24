#!/usr/bin/env bash

# Exit immediately if a command exits with a non-zero status,
# treat unset variables as an error, and ensure errors in pipelines are not masked.
set -euo pipefail

# Build HTML documentation for FLT
# The output will be located in docs/docs

# Create a temporary docbuild folder
mkdir -p docbuild

# Template lakefile.toml
cat << EOF > docbuild/lakefile.toml
name = "docbuild"
reservoir = false
version = "0.1.0"
packagesDir = "../.lake/packages"

[[require]]
name = "FLT"
path = "../"

[[require]]
scope = "leanprover"
name = "doc-gen4"
rev = "e23a86e721fd18baa5c11e9b65aa508a8f9aa136"
EOF

# Initialise docbuild as a Lean project
cd docbuild

# Disable an error message due to a non-blocking bug. See Zulip
MATHLIB_NO_CACHE_ON_UPDATE=1 ~/.elan/bin/lake update

# Build the docs
DISABLE_EQUATIONS=1 ~/.elan/bin/lake build FLT:docs

# Copy documentation to `docs/docs`
cd ../
sudo chown -R runner docs
cp -r docbuild/.lake/build/doc docs/docs
