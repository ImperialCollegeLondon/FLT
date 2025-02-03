import Mathlib
import FLT.Deformations.Basic
import FLT.Deformations.RepresentationTheory.Subrepresentation
import FLT.Deformations.RepresentationTheory.Irreducible
import FLT.Deformations.RepresentationTheory.RepresentationEquiv
import FLT.Mathlib.Algebra.Category.Ring.Basic
import FLT.Mathlib.RepresentationTheory.Basic

open scoped TensorProduct Representation CategoryTheory

variable {𝓞 : Type*} [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable {G : Type*} [Group G]

variable {A : 𝓒 𝓞}

variable {W : Type*} [AddCommMonoid W] [Module A W] [Module.Free A W] [Module.Finite A W]

variable (ρ : Representation A G W)

def ρbar (ρ : Representation A G W) : Representation (𝓴 A) G ((𝓴 A) ⊗[A] W) := sorry

-- Proposition 2.6 in Smit & Lenstra
lemma baseChange_of_traces_mem (A' : 𝓒 𝓞) [Algebra A' A] (hinj : Function.Injective (algebraMap A' A))
    (htraces : ∀ g : G, ∃ a : A'.obj, (algebraMap A' A) a = LinearMap.trace A W (ρ g))
    (habs_irred : Representation.IsAbsolutelyIrreducible (ρbar ρ))
        : ∃ W', ∃ _ : AddCommMonoid W', ∃ _ : Module A' W', ∃ ρ' : Representation A' G W',
        ∃ iso : ρ ≃ᵣ A ⊗ᵣ' ρ', True :=
    sorry
