import Mathlib
import FLT.Deformations.Basic

variable {𝓞 : Type*} [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable {G : Type*} [Group G]

variable {A : 𝓒 𝓞}

variable {W : Type*} [AddCommMonoid W] [Module A W] [Module.Free A W] [Module.Finite A W]

-- Proposition 2.6 in Smit & Lenstra
lemma baseChange_of_traces_mem : ∃ W', ∃ ρ' : Representation A G W',
  Representation.tprod' ρ' A ≃ₐ[A[G]] ρ = sorry
