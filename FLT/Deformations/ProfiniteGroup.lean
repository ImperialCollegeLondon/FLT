import Mathlib
import FLT.Deformations.Lift

namespace Deformations

variable {𝓞 : Type*} [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

variable {V : Type*} [AddCommMonoid V] [Module (𝓴 𝓞) V] [Module.Free (𝓴 𝓞) V] [Module.Finite (𝓴 𝓞) V]

variable {G : Type*} [Group G] [TopologicalSpace G] [TopologicalGroup G]

variable (ρbar : Representation (𝓴 𝓞) G V)
section G_profinite -- Section 3.2 Smit & Lenstra

-- Proposition 2.5 in G Finite
theorem Lift.functor_isCorepresentable_profinite : (Lift.functor 𝓞 ρbar).IsCorepresentable := sorry
end G_profinite

end Deformations
