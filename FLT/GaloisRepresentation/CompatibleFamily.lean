import Mathlib.Tactic
import FLT.GaloisRepresentation.PadicGaloisRep
import FLT.GaloisRepresentation.AssociatedPrime
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Discriminant
import Mathlib.RingTheory.IntegralRestrict
import Mathlib.RingTheory.Ideal.QuotientOperations
import Mathlib.NumberTheory.RamificationInertia
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
/-!
# Compatible Families of p-adic Galois Representations

A family of p-adic Galois representations is compatible if, for almost all
primes, a correseponding characteristic polynomial is the same on Frobenius automorphisms

## Main definitions and results
* `IsFrobenius'` : a proposition on Frobenius elements
* `IsCompatible` : a proposition on `PadicGaloisFamily` to state compatability

### Implementation details
* `IsFrobenius'` should be deprecated and replaced with `IsFrobenius`
* section
-/
open NumberField

set_option maxHeartbeats 4000000

namespace CompatibleFamily

variable {p : ℕ}[Fact (p.Prime)]

noncomputable section FrobeniusFinite

/-This section defines `IsFrobeniusFinite`, a predicate on Frobenius elements of `L ≃ₐ[K] L`
where `L/K` is finite dimensional-/

variable (A K L B : Type) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [FiniteDimensional K L]

variable {A B}

/-- An ideal `Q` of `B`, is invariant under a `A`-algebra equivalence from `B` to `B` iff
its image is itself-/
def IsInvariant (f : (B ≃ₐ[A] B)) (Q : Ideal B) : Prop := (Q = Q.comap (f.symm : B →+* B))

lemma comap_symm (f : (B ≃ₐ[A] B)) (Q : Ideal B)  : (Q.comap (f.symm : B →+* B) = Q.map f) :=
  Ideal.comap_symm _ _

variable (B)

/-- When `L` is finite dimensional over `K`, a `K`-algebra equivalence from `L` to `L` is
Frobenius for a maximal ideal downstairs if there exists a invariant maximal ideal upstairs above it
that induces a Frobenius map on the residue field `B ⧸ Q`. -/
def IsFrobeniusFinite (g : (L ≃ₐ[K] L)) (P : Ideal A) [Ideal.IsMaximal P] : Prop :=
  ∃ (Q : Ideal B) (h : IsInvariant ((galRestrict A K L B) g) Q), (Ideal.IsMaximal Q) ∧
  ((Ideal.map (algebraMap A B) P) ≤ Q) ∧
  (((Ideal.quotientEquivAlg Q Q ((galRestrict A K L B) g)
  (by erw [← comap_symm]; exact h)) : (B ⧸ Q) → (B ⧸ Q)) =
  fun x => x ^ (Nat.card (A ⧸ P)))

end FrobeniusFinite

section IsFrobenius
/-This section defines `IsFrobenius'` and `IsFrobenius`, propositions for Frobenius elements
of `L ≃ₐ[K] L` when the extension `L/K` isn't necessarily finite. See `IsFrobeniusAgrees.lean`
for an attempt at proving `IsFrobenius'` agrees with `IsFrobeniusFinite` when `K` and `L` are
number fields-/

variable (A K L B : Type ) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] -- not necessarily finite dimensional

open NumberField

lemma AlgEquiv_restrict_to_domain_equals_id (h1 : Normal K L) :
    AlgEquiv.restrictNormalHom (F := K) L  = MonoidHom.id _ := by
  ext a l
  simpa only [Algebra.id.map_eq_id, RingHom.id_apply, AlgHom.coe_coe] using
    AlgHom.restrictNormal_commutes (E := L) (F := K) (K₁ := L) (K₂ := L) a l

lemma AlgEquiv_restrict_to_domain_fix (h1 : Normal K L) (g : (L ≃ₐ[K] L)) :
    AlgEquiv.restrictNormalHom (F := K) L g =  g := by
  rw [AlgEquiv_restrict_to_domain_equals_id K L h1]
  rfl

/--Takes an ideal upstairs and brings it downstairs in a AKLB setup-/
def ToDownstairs  (Q : Ideal B) : Ideal A := Q.comap (algebraMap A B)

/-Depreciation note: eventually we want to state these in full generality, removing as many
instances of `NumberField` as possible. It seems like the following setup will be useful:

variable (A K L B : Type ) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] (not : ¬ (IsField A)) [Nontrivial A] [Ring.DimensionLEOne A]
    [∀ (P : Ideal A) [P.IsMaximal], Fintype (A ⧸ P)] [Infinite A]

the local case of `Fintype_Quot_of_IsMaximal` has been formalised by
María Inés de Frutos Fernández and Filippo A. E. Nuccio at
https://github.com/mariainesdff/LocalClassFieldTheory/blob/master/LocalClassFieldTheory/DiscreteValuationRing/ResidueField.lean -/

variable {A}

lemma IsMaximal_not_eq_bot [NumberField K] (Q : Ideal (𝓞 K)) [Ideal.IsMaximal Q] : Q ≠ ⊥ :=
  Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (RingOfIntegers.not_isField K)

lemma NumberField_Ideal_IsPrime_iff_IsMaximal  [NumberField K]
    (Q : Ideal (𝓞 K)) (h1: Q ≠ ⊥) : Ideal.IsPrime Q ↔ Ideal.IsMaximal Q := by
  constructor
  · intro h
    exact Ideal.IsPrime.isMaximal h h1
  · intro h
    exact Ideal.IsMaximal.isPrime h

instance Fintype_Quot_of_IsMaximal [NumberField K] (P : Ideal (𝓞 K)) [Ideal.IsMaximal P] : Fintype ((𝓞 K) ⧸ P) := by
  sorry

instance : Infinite (𝓞 K) := sorry

lemma ring_of_integers_not_Fintype [NumberField K] : ¬ (Finite (𝓞 K)) := Infinite.not_finite

lemma ne_bot_algebraMap_comap_ne_bot' (Q : Ideal B) [Ideal.IsMaximal Q] [Fintype (B ⧸ Q)]
    [Infinite A] :
    Ideal.comap (algebraMap A B) Q ≠ ⊥ := by
  by_contra hQ
  have h2 : Ideal.comap (algebraMap A B) Q ≤ Ideal.comap (algebraMap A B) Q :=
    Eq.le rfl
  let f := Ideal.quotientMap Q (algebraMap A B) h2
  have hf : Function.Injective (Ideal.quotientMap Q (algebraMap A B) h2) :=
    @Ideal.quotientMap_injective A _ B _ Q (algebraMap A B)
  have h3 : Fintype (A ⧸ Ideal.comap (algebraMap A B) Q) := Fintype.ofInjective f hf
  rw [hQ] at h3
  have h4 : Fintype A :=
    @Fintype.ofEquiv _ (A ⧸ ⊥) h3 (@QuotientAddGroup.quotientBot A _).toEquiv
  exact Fintype.false h4

lemma ne_bot_algebraMap_comap_ne_bot [NumberField K] [NumberField L]
    (Q : Ideal (𝓞 L)) [Ideal.IsMaximal Q] : Ideal.comap (algebraMap (𝓞 K) (𝓞 L)) Q ≠ ⊥ := by
  exact ne_bot_algebraMap_comap_ne_bot' ((𝓞 L)) Q

lemma IsMaximal_comap_IsMaximal' [NumberField K] [NumberField L]
    (Q : Ideal (𝓞 L)) [Ideal.IsMaximal Q] :
    Ideal.IsMaximal (Q.comap (algebraMap (𝓞 K) (𝓞 L))) := by
  rw [← NumberField_Ideal_IsPrime_iff_IsMaximal] at *
  · exact Ideal.IsPrime.comap (algebraMap (𝓞 K) (𝓞 L))
  · have h : Q ≠ ⊥ := IsMaximal_not_eq_bot L Q
    exact h
  · exact ne_bot_algebraMap_comap_ne_bot K L Q

lemma IsMaximal_ToDownstairs_IsMaximal [NumberField K] [NumberField L]
    (Q : Ideal (𝓞 L)) [Ideal.IsMaximal Q] : Ideal.IsMaximal (ToDownstairs (𝓞 K) (𝓞 L) Q) := by
  rw [ToDownstairs]
  exact IsMaximal_comap_IsMaximal' K L Q

instance [NumberField K] [NumberField L] [Algebra K L] : Algebra (𝓞 K) L :=
  RingHom.toAlgebra ((algebraMap _ _ : K →+* L).comp (algebraMap _ _ : 𝓞 K →+* K))

instance [NumberField K] [NumberField L] [Algebra K L] : IsScalarTower (𝓞 K) K L :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

instance [NumberField K] [NumberField L] [Algebra K L] : IsScalarTower (𝓞 K) (𝓞 L) L :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

instance (k l : Type) [Field k] [Field l] [NumberField k] [NumberField l] [Algebra k l] :
    IsIntegralClosure ((𝓞 l)) ((𝓞 k)) l := sorry -- a missing theorem, needs a proof

/-- Predicate on Frobenius elements for number fields. Should be depreciated to use `IsFrobenius`
instead.-/
def IsFrobenius' [NumberField K] (g : (L ≃ₐ[K] L)) (P : Ideal (𝓞 K)) [Ideal.IsMaximal P] : Prop :=
  ∀(N : Type) [Field N] [NumberField N] [Algebra K N] [FiniteDimensional K N] [IsGalois K N]
  [Algebra N L] [IsScalarTower K N L],
  IsFrobeniusFinite K N (𝓞 N) (AlgEquiv.restrictNormalHom N g) P

/--A predicate on Frobenius elements in a higher level of generality-/
def IsFrobenius (g : (L ≃ₐ[K] L)) (P : Ideal A) [Ideal.IsMaximal P] : Prop :=
  ∀ (N: Type) [Field N] [Algebra K N] [Algebra A N] [FiniteDimensional K N]
  [IsGalois K N] [IsScalarTower A K N] [Algebra N L] [IsScalarTower K N L],
  ∃ (C : Type) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C N)
  (_ : IsScalarTower A C N) (_ :IsIntegralClosure C A N),
  IsFrobeniusFinite K N C (AlgEquiv.restrictNormalHom N g) P

instance (p : Nat.Primes) : Fact (Nat.Prime p) := by
  cases' p with p hp
  constructor
  exact hp

end IsFrobenius

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

section charpoly_stuff

/-This section proves a few results about characteristic polynomials that are needed to prove
compatibility of certain classes of families.
`charpoly_eq_of_IsSimilar` seems so basic it must already be in Mathlib but I wasn't able to find
it.
-/

lemma charmatrix_one (n : ℕ) (R : Type) [CommRing R] : Matrix.charmatrix 1 =
    Matrix.scalar (Fin n) ((Polynomial.X : Polynomial R) - 1) := by
  unfold Matrix.charmatrix
  simp only [Matrix.scalar_apply, map_one, map_sub]

lemma charpoly_one_eq (n : ℕ) (R : Type) [CommRing R] :
    Matrix.charpoly (1 : Matrix (Fin n) (Fin n) R) = ((Polynomial.X : Polynomial R) - 1) ^ n := by
  unfold Matrix.charpoly
  rw [charmatrix_one]
  rw [Matrix.scalar_apply, Matrix.det_diagonal]
  simp only [Finset.prod_const, Finset.card_fin]

lemma map_one_to_one (n : ℕ) {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    Polynomial.map f (Matrix.charpoly (1 : Matrix (Fin n) (Fin n) R)) =
      Matrix.charpoly (1 : Matrix (Fin n) (Fin n) S) := by
  rw [charpoly_one_eq, charpoly_one_eq]
  simp only [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]

/--Two square matrices are similar if they are conjugate-/
def IsSimilar {n : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin n) (Fin n) R) : Prop := ∃ (P : GL (Fin n) R), A = P⁻¹ * B * P

lemma IsConj_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {g h : R} (h1 : IsConj g h) :
    IsConj (f g) (f h) := by
  unfold IsConj SemiconjBy at *
  cases' h1 with c hc
  use Units.map f c
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [← RingHom.map_mul, hc, RingHom.map_mul]

lemma ring_lemma {R : Type} [Ring R] (A B C D : R) : (C * A * D) - C * B * D = C * (A - B) * D := by
  rw [mul_sub_left_distrib, mul_sub_right_distrib]

lemma c_det_comm {n : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin n) (Fin n) R) :
    Matrix.det ((Polynomial.C : R →+* Polynomial R).mapMatrix A) = Polynomial.C (Matrix.det A) :=
  (RingHom.map_det Polynomial.C A).symm

lemma c_eval2 {R : Type} [CommRing R] (a b : R) :
    a = Polynomial.eval₂ (RingHom.id R) b (Polynomial.C a) := by
  rw [Polynomial.eval₂_C]
  rfl

/-The idea for `charpoly_eq_of_IsSimilar` is that
det (xI - P⁻¹AP) = det(P⁻¹(xI)P -P⁻¹AP) = det(P⁻¹(xI - A)P) = det(P⁻¹)det(xI - A)det(P)
= det(P)⁻¹ det(xI - A)det(P) = det(xI - A)

This second to last equality seems to be causing an issue. P⁻¹ has to be coerced to a matrix over
R[X] but invertibility here is not defined as far as I can tell.
It seems that to finish it, we need a nice map that goes from the matrices
over R[X] which come from applying Polynomial.C back to matrices over R by sending
it to the original matrix. Maybe define a new class for the domain of this map. -/

lemma charpoly_eq_of_IsSimilar {n : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin n) (Fin n) R) (h : IsSimilar A B) :
    Matrix.charpoly A = Matrix.charpoly B := by
  unfold Matrix.charpoly Matrix.charmatrix IsSimilar at *
  cases' h with P hP
  rw [hP]
  let Q1 := (Polynomial.C : R →+* Polynomial R).mapMatrix (P⁻¹ : Matrix (Fin n) (Fin n) R)
  let Q2 := (Polynomial.C : R →+* Polynomial R).mapMatrix (P : Matrix (Fin n) (Fin n) R)
  have h1 : (Matrix.scalar (Fin n)) (@Polynomial.X R _) = Q1 *
      ((Matrix.scalar (Fin n)) Polynomial.X) * Q2 := by sorry
  have h2 : (RingHom.mapMatrix Polynomial.C)
      ((↑P⁻¹ : Matrix (Fin n) (Fin n) R) * B * (↑P : Matrix (Fin n) (Fin n) R)) =
      Q1 * ((RingHom.mapMatrix Polynomial.C) B) * Q2 := by sorry -- simp only [Matrix.coe_units_inv, Matrix.map_mul,
--        RingHom.mapMatrix_apply]
  rw [h1, h2, ring_lemma, Matrix.det_mul, Matrix.det_mul]
  sorry

lemma IsSimilar_of_IsConj {n : ℕ} {R S : Type} [Group R] [CommRing S] {g h : R}
    (f : R →* (GL (Fin n) S)) (h1 : IsConj g h) :
    IsSimilar ((f g) : Matrix (Fin n) (Fin n) S) (f h) := by
  cases' h1 with c hc
  have h2 : g = c⁻¹ * h * c := by
    rw [mul_assoc]
    rw [← hc]
    simp only [Units.val_inv_eq_inv_val, inv_mul_cancel_left]
  use f c
  rw [h2]
  simp only [Units.val_inv_eq_inv_val, map_mul, map_inv, Units.val_mul, Matrix.coe_units_inv]

end charpoly_stuff

section TrivialFamily

variable (A K L B : Type ) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L]

/--The `PadicGaloisFamily` given by associating every prime, and ring homomorphism with the
constant map sending everything to 1-/
noncomputable def TrivialFamily (K: Type) [Field K] [NumberField K] (E : Type) [Field E] [NumberField E]
    (n : ℕ) :
    PadicGaloisFamily K E n :=
  fun p hp _ ↦ {
    toFun := fun _ ↦ 1
    map_one' := by
      rfl
    map_mul' := by
      simp only [mul_one, forall_const]
    continuous_toFun := by
      dsimp only [OneHom.toFun_eq_coe, OneHom.coe_mk]
      exact continuous_const
    }

lemma TrivialFamily_IsCompatible {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E]
    {n : ℕ} : IsCompatible (TrivialFamily K E n) := by
  use ⊥
  intro _ _
  use (Polynomial.X - 1) ^ n
  intro l _ _ χ Fₚ _
  have h : ↑((TrivialFamily K E n (↑(PrimeLyingAbove l)) χ) Fₚ) = 1 := rfl
  rw [h]
  rw [← charpoly_one_eq]
  exact map_one_to_one n χ

end TrivialFamily

section FamilyFromHomSetup

variable (A K L B : Type ) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L]

/--The `PadicGaloisFamily` induced from a homomorphism `(L ≃ₐ[K] L) →* (GL (Fin n) E)` -/
noncomputable def FamilyFromHom {n : ℕ} {K: Type} [Field K] [NumberField K]
    {E : Type} [Field E] [NumberField E] (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L][IsGalois K L] [IsScalarTower K L (AlgebraicClosure K)]
    (ρ: (L ≃ₐ[K] L) →* (GL (Fin n) E)) :
    PadicGaloisFamily K E n :=
  fun p hp ψ ↦ ({
    toFun := MonoidHom.comp (MonoidHom.comp
      (GLMap E (AlgebraicClosure (ℚ_[p])) n ψ) ρ) (AlgEquiv.restrictNormalHom L)
    map_one' :=
      MonoidHom.map_one (MonoidHom.comp (MonoidHom.comp (GLMap E (AlgebraicClosure ℚ_[p]) n ψ) ρ)
          (AlgEquiv.restrictNormalHom L))
    map_mul' := fun x y =>
      map_mul (MonoidHom.comp (MonoidHom.comp (GLMap E (AlgebraicClosure ℚ_[p]) n ψ) ρ)
          (AlgEquiv.restrictNormalHom L))
        x y
    continuous_toFun :=  by
      have hg : Continuous ((AlgEquiv.restrictNormalHom L) :
          ((AlgebraicClosure K)≃ₐ[K](AlgebraicClosure K)) → (L ≃ₐ[K] L)) := by
        exact gal_restrict_cont K (AlgebraicClosure K) L
      have hcomp : Continuous (MonoidHom.comp (GLMap E (AlgebraicClosure (ℚ_[p])) n ψ) ρ) := by
        exact continuous_of_discreteTopology
      dsimp
      exact Continuous.comp hcomp hg
  } : ContinuousMonoidHom ((AlgebraicClosure K)≃ₐ[K](AlgebraicClosure K))
  (GL  (Fin n) (AlgebraicClosure (ℚ_[p]))))

/-This is a black box for me conjugacy in the unramified case is probably another final project's
worth of work-/
theorem conj_if_not_divide_disc [NumberField K] [NumberField L] (g : L ≃ₐ[K] L) (h : L ≃ₐ[K] L)
    (P : Ideal (𝓞 K)) [Ideal.IsMaximal P] (h1 : ¬ ((PrimeLyingAbove P : ℤ) ∣ discr L))
    (h2 : IsFrobenius' K L g P) (h3 : IsFrobenius' K L h P):
    IsConj g h := by sorry

lemma NumberField_of_FiniteDimensional [NumberField K] [FiniteDimensional K L] :
    NumberField L :=
  have foo : CharZero L := by
        have hinj : Function.Injective (algebraMap K L) :=
          NoZeroSMulDivisors.algebraMap_injective K L
        apply (RingHom.charZero_iff hinj).1
        exact algebraRat.charZero K
  { to_charZero := foo
    to_finiteDimensional := by apply Module.Finite.trans K L
  }

/- `Intermediate_of_IsFrobenius` should use whatever ends up making
`IsFrobeniusAgrees.IsFrobenius'_agrees_NumberField` work + seems to rely on some instances that
look like they should hold
-/
lemma Intermediate_of_IsFrobenius' {K: Type} [Field K] [NumberField K]
    (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsGalois K L] [IsScalarTower K L (AlgebraicClosure K)]
    (g : (AlgebraicClosure K) ≃ₐ[K] (AlgebraicClosure K)) (P : Ideal (𝓞 K)) [Ideal.IsMaximal P]
    (h : IsFrobenius' K (AlgebraicClosure K) g P) :
    IsFrobenius' K L (AlgEquiv.restrictNormalHom L g) P := by
  intro N N1 N2 N3 N4 N5 N6 N7
  have N9 : Algebra N (AlgebraicClosure K) := by sorry
  have N10 : IsScalarTower K N (AlgebraicClosure K) := by sorry
  have : ((AlgEquiv.restrictNormalHom N) g) =
      (AlgEquiv.restrictNormalHom N) ((AlgEquiv.restrictNormalHom L) g) := by sorry
  specialize h N
  rw [← this]
  exact h
  /-need some composition of restrictNormalHoms to have a commutative diagram, looks reasonable
  this would probably be needed in `IsFrobeniusAgrees`-/

instance NumberField_CommRing (E : Type) [Field E] [NumberField E] : CommRing E := Field.toCommRing

end FamilyFromHomSetup

section FamilyFromHom

/--The set of maximal ideals whose corresponding prime number divides the discriminant of the
upstairs field-/
def specialset (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] :
    Set ({Q : Ideal (𝓞 K) // Ideal.IsMaximal Q}) := {Q | ((PrimeLyingAbove Q.1 : ℤ ) ∣ discr L)}

/-`charpoly_GLMap` is probably a couple of lemmas away from being done. Find a way of applying
`f : R →*+ S` to `R[X]` and then extending this to matrices.-/
lemma charpoly_GLMap {n : ℕ} {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (x : GL (Fin n) R) :
    Polynomial.map f (@Matrix.charpoly _ _ (Fin n) _ _ x) =
     @Matrix.charpoly S _ (Fin n) _ _ (GLMap R S n f x) := by
--  simp only [RingHom.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe, RingHom.mapMatrix_apply]
  unfold Matrix.charpoly
  -- have h : (GLMap R S n f) x = ((RingHom.mapMatrix f) : GL (Fin n) R → GL (Fin n) S) x := by sorry
  sorry

/-In `FamilyFromHom_IsCompatible`, `h1` will follow from only finitely many prime ideals lying over
each prime number. The `sorry` in each of the other two cases should be resolved by a theorem
stating that Frobenius elements exist.-/

lemma FamilyFromHom_IsCompatible {n : ℕ} {K : Type} [Field K] [NumberField K]
    {E : Type} [Field E] [NumberField E] (L : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [IsGalois K L] [IsScalarTower K L (AlgebraicClosure K)]
    (ρ: (L ≃ₐ[K] L) →* (GL (Fin n) E)) : IsCompatible (FamilyFromHom L ρ) := by
  have foo : NumberField L := NumberField_of_FiniteDimensional K ↥L
  have h1 : Set.Finite (specialset K L) := by sorry
  use h1.toFinset
  intro P hP
  let g : (L ≃ₐ[K] L) := by sorry
  have hfrob : IsFrobenius' K L g P := by sorry
  use (Matrix.charpoly ((ρ g) : Matrix (Fin n) (Fin n) E) : Polynomial E)
  intro l hl _ χ h hfrob'
  let h' := AlgEquiv.restrictNormalHom L h
  have h'f : IsFrobenius' K L h' P :=
    Intermediate_of_IsFrobenius' L h (↑P) hfrob'
  have hP1 : Fintype ((𝓞 K) ⧸ (P : Ideal (𝓞 K))) := Fintype_Quot_of_IsMaximal K P
  have hP2 : ¬ ((PrimeLyingAbove (P : Ideal (𝓞 K)) : ℤ) ∣ discr L) := by
    by_contra div
    apply hP
    simp only [Set.Finite.mem_toFinset]
    rw [specialset]
    exact div
  have h2 : IsConj g h' := conj_if_not_divide_disc K (↥L) g h' (↑P) hP2 hfrob h'f
  have h3 : @Matrix.charpoly E _ (Fin n) _ _ (ρ g) =
      @Matrix.charpoly E _ (Fin n) _ _ (ρ h') := by
    have h : IsSimilar ((ρ g) : Matrix (Fin n) (Fin n) E) (ρ h' : Matrix (Fin n) (Fin n) E) :=
      IsSimilar_of_IsConj ρ h2
    exact @charpoly_eq_of_IsSimilar n E (NumberField_CommRing E)
      ((ρ g) : Matrix (Fin n) (Fin n) E) ((ρ h')) h
  rw [h3]
  --simp only
  rw [charpoly_GLMap]
  --simp only [MonoidHom.coe_comp, Function.comp_apply]
  rfl

end FamilyFromHom
