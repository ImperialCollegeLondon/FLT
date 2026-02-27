import FLT.GaloisRepresentation.HardlyRamified.Defs

namespace GaloisRepresentation.IsHardlyRamified

universe u v

variable {k : Type u} [Finite k] [Field k]
    [TopologicalSpace k] [DiscreteTopology k]
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime] [Algebra ℤ_[p] k]
    [IsLocalHom (algebraMap ℤ_[p] k)]
    (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2)

open TensorProduct

/--
An irreducible mod p hardly ramified representation lifts to a p-adic one.
-/
theorem lifts (ρ : GaloisRep ℚ k V) (hρirred : ρ.IsIrreducible)
    (hρ : IsHardlyRamified hpodd hV ρ) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R)
      (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : IsDomain R) (_ : Algebra ℤ_[p] R) (_ : IsLocalHom (algebraMap ℤ_[p] R))
      (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R)
      (_ : IsModuleTopology ℤ_[p] R)
      (_ : Algebra R k) (_ : IsScalarTower ℤ_[p] R k) (_ : ContinuousSMul R k)
      (W : Type v) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
      (_ : Module.Free R W) (hW : Module.rank R W = 2)
      (σ : GaloisRep ℚ R W) (r : k ⊗[R] W ≃ₗ[k] V),
    IsHardlyRamified hpodd hW σ ∧ (σ.baseChange k).conj r = ρ := sorry

end IsHardlyRamified

end GaloisRepresentation
