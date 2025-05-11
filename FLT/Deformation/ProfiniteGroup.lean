import Mathlib
import FLT.Deformation.BaseCat
import FLT.Deformation.Lift
import FLT.Deformation.Deformation
import FLT.Deformation.Topology.Algebra.Category.ProfiniteGrp.Basic
import FLT.Deformation.ContinuousRepresentation.IsTopologicalModule

#exit
universe u

open ProfiniteGrp

namespace Deformation

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

variable {V : Type u} [AddCommGroup V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]

section G_profinite -- Section 3.2 Smit & Lenstra

variable {G : ProfiniteGrp}

variable (ρbar : ContinuousRepresentation (𝓴 𝓞) G V)

lemma ker_isOpen : IsOpen (X := G) (MonoidHom.ker ρbar.1) := sorry

local notation3:max "k" => (⟨MonoidHom.ker ρbar, ker_isOpen ρbar⟩ : OpenSubgroup G)
local notation3:max "Hs" => OpenAvoidingDecomposition G k
local notation3:max "G_to_Hs" => OpenAvoidingDecomposition.diagonalMap_homeo G k

-- Proposition 2.5 in G Profinite
theorem Lift.functor_isCorepresentable_profinite :
    (Lift.functor 𝓞 ρbar).IsCorepresentable := by
  sorry

end G_profinite

end Deformation
