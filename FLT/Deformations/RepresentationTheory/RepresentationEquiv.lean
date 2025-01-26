import FLT.Deformations.RepresentationTheory.Subrepresentation
import FLT.Mathlib.RepresentationTheory.Basic

namespace Representation

variable {R V V' G: Type*} [CommSemiring R]
  [AddCommMonoid V] [Module R V]
  [AddCommMonoid V'] [Module R V']
  [Group G]

variable (ρ : Representation R G V)
variable (ρ' : Representation R G V')

structure RepresentationEquiv : Type _ where
  map : V ≃ₗ[R] V'
  comm : ∀ g : G, map ∘ (ρ g) = (ρ' g) ∘ map

def IsRepresentationEquiv : Prop := Nonempty (RepresentationEquiv ρ ρ')

notation ρ "≃ᵣ" ρ' => RepresentationEquiv ρ ρ'

end Representation
