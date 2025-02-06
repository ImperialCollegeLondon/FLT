import Lake
open Lake DSL

package FLT where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩, -- switch off auto-implicit
    ⟨`relaxedAutoImplicit, false⟩ -- switch off relaxed auto-implicit
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "stable"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

@[default_target]
lean_lib FLT where
  globs := #[
    .andSubmodules `FLT
  ]
