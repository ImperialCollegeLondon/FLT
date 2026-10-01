#!/usr/bin/env bash

################################################################################
# TEST SCRIPT TO RUN BEFORE PUSHING CHANGES
#
# This script ensures that the key components of the Lean project are functional
# before changes are pushed to the repository by checking that:
# 1. You are in the correct directory;
# 2. The project builds successfully;
# 3. The blueprint is successfully generated in both PDF and web versions;
# 4. LaTeX declarations in the blueprint match Lean declarations in the codebase.
################################################################################

# Ensure the script is in the outermost 'FLT' folder
echo "Checking if you are in the correct directory..."
if [ ! -f lakefile.toml ]; then
  echo "❌ Error: This doesn't appear to be the outermost 'FLT' directory.
        Please run this script from the correct folder."
  exit 1
else
  echo "✅ Correct directory detected."
fi

# Get Mathlib cache
echo "Attempting to get Mathlib cache..."
if ! lake exe cache get; then
  echo "❌ Error: Failed to get Mathlib cache. Continuing without cache."
else
  echo "✅ Mathlib cache successfully retrieved."
fi

# Build the project
echo "Building the project..."
if ! lake build FLT; then
  echo "❌ Error: Project build failed. Please check the code for errors."
  exit 1
else
  echo "✅ Project build completed successfully."
fi

# The blueprint toolchain is optional: most contributors don't have leanblueprint
# installed, and the blueprint CI step is currently disabled while the blueprint
# migrates to Verso, so only run these steps when the tool is available.
if command -v leanblueprint >/dev/null 2>&1; then
  # Generate the PDF version of the blueprint
  echo "Generating PDF version of the blueprint..."
  if ! leanblueprint pdf; then
    echo "❌ Error: Failed to generate PDF version of the blueprint."
    exit 1
  else
    echo "✅ PDF version of the blueprint generated successfully."
  fi

  # Generate the web version of the blueprint
  echo "Generating web version of the blueprint..."
  if ! leanblueprint web; then
    echo "❌ Error: Failed to generate web version of the blueprint."
    exit 1
  else
    echo "✅ Web version of the blueprint generated successfully."
  fi

  # Check declarations
  echo "Checking if Lean declarations in the blueprint match the codebase..."
  if ! lake exe checkdecls blueprint/lean_decls; then
    echo "❌ Error: Some declarations in the blueprint do not match Lean declarations in the codebase."
    exit 1
  else
    echo "✅ All declarations match successfully."
  fi
else
  echo "⏭️  leanblueprint not found — skipping blueprint PDF/web generation and declaration checks."
fi

# Final message on test completion
echo "🎉 All steps completed successfully! You are ready to push."
