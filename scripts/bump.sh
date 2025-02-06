# Update the mathlib version inside the main project
lake update mathlib
# Update the doc-gen version inside the docbuild project
cd docbuild
lake update FLT
rm lean-toolchain
rm lake-manifest.json
cd ..
