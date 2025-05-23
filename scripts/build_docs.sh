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
rev = "$(< lean-toolchain cut -f 2 -d: )"
EOF

# Initialise docbuild as a Lean project
cd docbuild

# Disable an error message due to a non-blocking bug. See Zulip
# (note added by kmb : no idea what that "See Zulip" is referring to but Bhavik
# suggests that we should be updating doc-gen4 rather than FLT here in order to prevent
# the "build project API documentation" step of CI from taking 42 minutes on
# e.g. PR 523 despite not bumping mathlib)
MATHLIB_NO_CACHE_ON_UPDATE=1 ~/.elan/bin/lake update doc-gen4

# Build the docs
~/.elan/bin/lake build FLT:docs

# Copy documentation to `docs/docs`
cd ../
sudo chown -R runner docs
cp -r docbuild/.lake/build/doc docs/docs
