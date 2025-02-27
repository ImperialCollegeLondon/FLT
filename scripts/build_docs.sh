# Build HTML documentation for FLT
# The output will be located in docs/docs

# Template lakefile.toml
template() {
  cat <<EOF
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
rev = "TOOLCHAIN"
EOF
}

# Create a temporary docbuild folder
mkdir -p docbuild

# Equip docbuild with the template lakefile.toml
template > docbuild/lakefile.toml

# Substitute the toolchain from lean-toolchain into docbuild/lakefile.toml
sed -i s/TOOLCHAIN/`grep -oP 'v4\..*' lean-toolchain`/ docbuild/lakefile.toml

# Fetch the docs cache if it exists
mkdir -p docs/docs
mv docs/docs docbuild/.lake/build/doc

# Initialise docbuild as a Lean project
cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 # Disable an error message due to a non-blocking bug. See Zulip
~/.elan/bin/lake update FLT
~/.elan/bin/lake exe cache get

# Build the docs
~/.elan/bin/lake build FLT:docs

# Move them out of docbuild
cd ../
rm -rf docs/docs
mv docbuild/.lake/build/doc docs/docs

# Clean up after ourselves
rm -rf docbuild
