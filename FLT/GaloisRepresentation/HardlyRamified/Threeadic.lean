import FLT.GaloisRepresentation.HardlyRamified.Defs
import FLT.GaloisRepresentation.HardlyRamified.ModThree -- will be needed for proof
import Mathlib.RingTheory.Ideal.Int

noncomputable def toNatPrime
  (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
  {p : ℕ // Nat.Prime p} := by
  refine ⟨Ideal.absNorm (Ideal.under ℤ v.asIdeal), ?_⟩
  have vnezero : NeZero v.asIdeal := ⟨v.ne_bot⟩
  apply Nat.absNorm_under_prime

namespace GaloisRepresentation.IsHardlyRamified

local notation "Frob" => Field.AbsoluteGaloisGroup.adicArithFrob

-- TODO -- make some API for "I have a rank 1 quotient where Galois acts trivially"
-- e.g. this implies trace(Frob_p) is (1+p)

/--
A 3-adic hardly ramified representation has trace(Frob_p) = 1 + p for all p ≠ 2,3
-/

theorem three_adic {R : Type*} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∀ v (hp5 : 5 ≤ (toNatPrime v).val),
      (ρ.toLocal v (Frob v)).charpoly =
      (Polynomial.X - (1 : Polynomial R)) * (Polynomial.X - ((toNatPrime v) : Polynomial R)) :=
      sorry

end GaloisRepresentation.IsHardlyRamified
