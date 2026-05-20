import Lake
open Lake DSL

-- The FLT Verso blueprint is a self-contained Lake package nested in the FLT
-- repository. It deliberately does not touch FLT's own `lakefile.toml`.
--
-- Phase 2: to link Blueprint nodes to real FLT declarations, add
--   require FLT from ".."
-- *before* the VersoBlueprint require below, so that FLT's mathlib pins
-- (e.g. ProofWidgets) win during dependency resolution.

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"v4.30.0"

package FLTBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib FLTBlueprint where

lean_exe «blueprint-gen» where
  root := `FLTBlueprintMain
