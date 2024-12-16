import Mathlib
import FLT.Deformations.RepresentationTheory.Subrepresentation

namespace Representation

open scoped TensorProduct

variable {G : Type*} [Group G]

variable {A : Type*} [CommRing A]

variable {W : Type*} [AddCommMonoid W] [Module A W]

noncomputable def tprod' (A' : Type*) [CommRing A'] [Algebra A A']
  (ρ : Representation A G W): Representation A G (A' ⊗[A] W) := sorry

notation R "⊗ᵣ[" A "]" ρ => Representation.tprod' (A := A) R ρ
notation ρ "⊗ᵣ" ρ' => Representation.tprod ρ ρ'

class Irreducible (ρ : Representation A G W) : Prop where
  irreducible : IsSimpleOrder (Subrepresentation ρ)

class AbsolutelyIrreducible (ρ : Representation A G W) : Prop where
  absolutelyIrreducible :
    ∀ A', ∃ _ : CommRing A', ∀ _ : Algebra A A',
    Irreducible (A' ⊗ᵣ[A] ρ)

end Representation
