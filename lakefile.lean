
import Lake
open Lake DSL

package «FLT» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,           -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,            -- no "assume a typo is a new variable"
    ⟨`relaxedAutoImplicit, false⟩,     -- no "assume a typo is a new variable"
    ⟨`linter.style.longLine, true⟩,    -- no lines longer than 100 chars
    ⟨`linter.oldObtain, true⟩,         -- no "stream of consciousness `obtain`"
    ⟨`linter.style.cases, true⟩,       -- no `cases'` tactic
    ⟨`linter.style.refine, true⟩,      -- no `refine'` tactic
    ⟨`linter.style.multiGoal, true⟩,   -- no multiple active goals
    ⟨`linter.flexible, true⟩,          -- no rigid tactic after flexible tactic
  ]

  -- Server options like maxSynthPendingDepth go here:
  moreServerOptions := #[
    ⟨`maxSynthPendingDepth, .ofNat 3⟩
  ]

-- Require mathlib as a dependency
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git"

@[default_target]
lean_lib «FLT» where
  globs := #[.submodules `FLT, .submodules `FermatsLastTheorem]
