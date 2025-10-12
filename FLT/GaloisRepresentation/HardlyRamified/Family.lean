import FLT.GaloisRepresentation.HardlyRamified.Defs

/-

# Ideas

The proof that a p-adic rep spreads out into a compatible family of ell-adic reps:
does it give us a number field M and reps to GL_2(M_lambda)? Or do we need M_lambda-bar?
I think we might do, esp in the reducible case.

section Compatible

/-In this section, the predicate  `IsCompatible` is defined-/

variable (A K L B : Type ) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L]

instance (K : Type) [Field K] [NumberField K] (P : {Q : Ideal (𝓞 K)| Ideal.IsMaximal Q}) :
    Ideal.IsMaximal (P : Ideal (𝓞 K)) := by
    cases' P with P hP
    exact hP

instance [NumberField K] : ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], Fintype ((𝓞 K) ⧸ P) := by
  intro P _
  infer_instance

/--A `PadicGaloisFamily` is compatible if, for all but finitely many primes, the characteristic
polynomials induced by the family are all equal.-/
def IsCompatible {K : Type} [Field K] [NumberField K]
    {E : Type} [Field E] [NumberField E] {n : ℕ} (fam : PadicGaloisFamily K E n) : Prop :=
  ∃ (S : Finset {Q : Ideal (𝓞 K) // Ideal.IsMaximal Q}),
  ∀ P ∉ S,
  ∃ (Hₚ : Polynomial E),
  ∀ (l : Ideal (𝓞 K)) (_ : Ideal.IsMaximal l)
  (_ : PrimeLyingAbove l ≠ PrimeLyingAbove (P : Ideal (𝓞 K)))
  (χ : E →+* AlgebraicClosure (ℚ_[PrimeLyingAbove l]))
  (Fₚ : ((AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K))) (_ : IsFrobenius' K _ Fₚ P),
  ((Polynomial.map χ Hₚ) = Matrix.charpoly ((fam (PrimeLyingAbove l) χ Fₚ) :
    Matrix (Fin n) (Fin n) (AlgebraicClosure (ℚ_[PrimeLyingAbove l]))))

end Compatible

-/
namespace GaloisRepresentation.IsHardlyRamified

open GaloisRepresentation IsDedekindDomain NumberField

universe u v

-- let ρ : G_ℚ → GL_2(R) be hardly ramified, where R is the integers in a finite
-- extension of ℚ_p
variable {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    {R : Type u} [CommRing R] [Algebra ℤ_[p] R] [IsDomain R]
    [Module.Finite ℤ_[p] R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] [IsModuleTopology ℤ_[p] R]
    {V : Type v} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [Module.Free R V] (hv : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified hpodd hv ρ)

-- Then `ρ` lives in a compatible family of Galois representations
theorem mem_compatibleFamily : ∃ (M : Type v) (_ : Field M) (_ : NumberField M)
    (σ : (P : HeightOneSpectrum (𝓞 M)) → FramedGaloisRep ℚ ), 2+2=4 := sorry

-- A p-adic hardly ramified extension spreads out into a compatible family
-- of ell-adic ones -- TODO

end GaloisRepresentation.IsHardlyRamified
