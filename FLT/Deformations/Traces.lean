import Mathlib
import FLT.Deformations.Basic
import FLT.Deformations.RepresentationTheory.Subrepresentation
import FLT.Deformations.RepresentationTheory.RepresentationEquiv
import FLT.Mathlib.Algebra.Category.Ring.Basic

open scoped TensorProduct Representation

variable {𝓞 : Type*} [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
local notation3:max "𝓴" 𝓞 => (IsLocalRing.ResidueField 𝓞)

variable {G : Type*} [Group G]

variable {A : 𝓒 𝓞}

variable {W : Type*} [AddCommMonoid W] [Module A W] [Module.Free A W] [Module.Finite A W]

variable (ρ : Representation A G W)

-- Proposition 2.6 in Smit & Lenstra
lemma baseChange_of_traces_mem (A' : 𝓒 𝓞) (ι : A' →+* A) (hinj : Function.Injective ι)
    [Algebra A' A] (halg : algebraMap A' A = ι)
    (htraces : ∀ g : G, ∃ a : (A' : CommRingCat), ι a = LinearMap.trace A W (ρ g))
    : ∃ W', ∃ _ : AddCommMonoid W', ∃ _ : Module A' W', ∃ ρ' : Representation A' G W',
    ∃ iso : True, True := sorry-- (Representation.tprod' (G := G) (W := W') (A := A') A ρ') ≃ᵣ ρ, _ := sorry
