# Update the mathlib version inside the main project
lake update mathlib
# Update the doc-gen version inside the docbuild project
cd docbuild
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update FLT
rm lean-toolchain
rm lake-manifest.json
cd ..
