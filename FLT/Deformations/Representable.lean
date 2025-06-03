import FLT.Init
import FLT.Deformations.LiftFunctor
import FLT.Deformations.RepresentationTheory.Irreducible

open CategoryTheory IsLocalRing

namespace Deformation

universe u

variable (n : Type) [Fintype n] [DecidableEq n] (G : Type u) [Group G] [TopologicalSpace G]
variable [T0Space G] [TotallyDisconnectedSpace G] [CompactSpace G] -- profinite
variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
  [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞] -- complete noetherian local
variable (ρ : (repnFunctor n G 𝓞).obj .residueField) [(toRepresentation ρ).IsAbsolutelyIrreducible]

lemma isCorepresentable_deformationFunctor :
    (deformationFunctor n G 𝓞 ρ).toFunctor.IsCorepresentable := by
  sorry -- de Smit and Lenstra, Proposition 2.3 (1).
