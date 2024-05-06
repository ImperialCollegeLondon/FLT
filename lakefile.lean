import Lake
open Lake DSL

package FLT where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩, -- switch off auto-implicit
    ⟨`relaxedAutoImplicit, false⟩ -- switch off relaxed auto-implicit
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

-- This is run only if we're in `dev` mode. This is so not everyone has to build doc-gen
meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib FLT where
  globs := #[
    .andSubmodules `FLT
  ]
