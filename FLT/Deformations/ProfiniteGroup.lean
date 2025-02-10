import Mathlib
import FLT.Deformations.Lift
import FLT.Deformations.Topology.Algebra.Category.ProfiniteGrp.Basic

universe u

open ProfiniteGrp

namespace Deformations

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

variable {V : Type u} [AddCommMonoid V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]

section G_profinite -- Section 3.2 Smit & Lenstra

variable {G : ProfiniteGrp}

variable (ρbar : Representation (𝓴 𝓞) G V)

lemma ker_isOpen : IsOpen (X := G) (MonoidHom.ker ρbar) := sorry

local notation3:max "k" => (⟨MonoidHom.ker ρbar, ker_isOpen ρbar⟩ : OpenSubgroup G)
local notation3:max "Hs" => OpenAvoidingDecomposition G k
local notation3:max "G_to_Hs" => OpenAvoidingDecomposition.diagonalMap_homeo G k

-- Proposition 2.5 in G Profinite
theorem Lift.functor_isCorepresentable_profinite :
    (Lift.functor 𝓞 ρbar).IsCorepresentable := by
  sorry

end G_profinite

end Deformations
