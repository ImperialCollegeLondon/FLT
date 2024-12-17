import FLT.Deformations.RepresentationTheory.Subrepresentation
import FLT.Mathlib.RepresentationTheory.Basic

namespace Representation

variable {G : Type*} [Group G]

variable {k : Type*} [Field k]

variable {W : Type*} [AddCommMonoid W] [Module k W]

class Irreducible (ρ : Representation k G W) : Prop where
  irreducible : IsSimpleOrder (Subrepresentation ρ)

class AbsolutelyIrreducible (ρ : Representation k G W) : Prop where
  absolutelyIrreducible : ∀ k', ∀ _ : Field k', ∀ _ : Algebra k k',
    ∀ _ : Function.Injective (algebraMap k k'), Irreducible (k' ⊗ᵣ' ρ)

end Representation
