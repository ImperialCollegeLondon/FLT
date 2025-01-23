# Update the mathlib version inside the main project
lake update mathlib
# Update the doc-gen version inside the docbuild project
cd docbuild
lake update doc-gen4
cd ..
