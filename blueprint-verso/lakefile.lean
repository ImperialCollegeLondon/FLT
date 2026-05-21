import Lake
open Lake DSL

-- The FLT Verso blueprint is a self-contained Lake package nested in the FLT
-- repository. It deliberately does not touch FLT's own `lakefile.toml`.
--
-- Dependency resolution note: Verso and Mathlib pin different versions of
-- ProofWidgets and plausible. A later `require` wins, so `require FLT` is
-- listed after `VersoBlueprint`, and ProofWidgets / plausible are pinned
-- explicitly last to exactly the versions FLT's Mathlib uses. This keeps
-- `lake exe cache get` able to find Mathlib's prebuilt cache instead of
-- triggering a full Mathlib rebuild.

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"v4.30.0"
require FLT from ".."
require proofwidgets from git
  "https://github.com/leanprover-community/ProofWidgets4"@"v0.0.98"
require plausible from git
  "https://github.com/leanprover-community/plausible"@"293af9b2a383eed4d04d66b898d608d0a44b750f"

package FLTBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib FLTBlueprint where

lean_exe «blueprint-gen» where
  root := `FLTBlueprintMain
