import FLT.GaloisRepresentation.HardlyRamified.Defs

namespace GaloisRepresentation.IsHardlyRamified

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

universe u

def has_trivial_quotient (k : Type*) {K : Type*} [Field k] [Field K] {V : Type*}
  [AddCommGroup V] [TopologicalSpace k] [IsTopologicalRing k]
  [Module k V] [Module.Finite k V] [Module.Free k V] (ρ : GaloisRep K k V) : Prop :=
  ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
    ∀ g : Γ K, ∀ v : V, π (ρ g v) = π v

/-- A mod 3 hardly ramified representation is an extension of trivial by cyclo -/
-- Probably `Field k` can be replaced with `(3 : k) = 0`
theorem mod_three {k : Type u} [Fintype k] [Field k] [Algebra ℤ_[3] k] --
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    has_trivial_quotient k ρ := by
  sorry

end GaloisRepresentation.IsHardlyRamified
