import FLT.Deformations.RepresentationTheory.Subrepresentation
import FLT.Mathlib.RepresentationTheory.Basic

namespace Representation

variable {G : Type*} [Group G]

variable {A : Type*} [CommRing A]

variable {W : Type*} [AddCommMonoid W] [Module A W]

class Irreducible (ρ : Representation A G W) : Prop where
  irreducible : IsSimpleOrder (Subrepresentation ρ)

class AbsolutelyIrreducible (ρ : Representation A G W) : Prop where
  absolutelyIrreducible : ∀ A', ∀ _ : CommRing A', ∀ _ : Algebra A A',
    ∀ _ : Function.Injective (algebraMap A A'), Irreducible (A' ⊗ᵣ' ρ)

end Representation
