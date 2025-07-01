/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Andrew Yang, Matthew Jasper
-/
import FLT.Mathlib.RingTheory.Localization.BaseChange -- removing this breaks a simp proof
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!

The general "AKLB" set-up. `K` is the field of fractions of the Dedekind domain `A`,
`L/K` is a finite separable extension, and `B` is the integral closure of `A` in `L`.

-/

namespace IsDedekindDomain.HeightOneSpectrum

section BaseChange

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsIntegral A B] [IsDedekindDomain B]
    [IsFractionRing B L]

variable (v : HeightOneSpectrum A)

variable {B L} in
/-- If B/A is an integral extension of Dedekind domains, `comap w` is the pullback
of the nonzero prime `w` to `A`. -/
def comap (w : HeightOneSpectrum B) : HeightOneSpectrum A where
  asIdeal := w.asIdeal.comap (algebraMap A B)
  isPrime := Ideal.comap_isPrime (algebraMap A B) w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

variable {A} in
/-- If `B` is an `A`-algebra and `v : HeightOneSpectrum A` is a nonzero prime,
then `v.Extension B` is the subtype of `HeightOneSpeectrum B` consisting of valuations of `B`
which restrict to `v`. -/
def Extension (v : HeightOneSpectrum A) := {w : HeightOneSpectrum B // w.comap A = v}

lemma mk_count_factors_map
    (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) (I : Ideal A) [DecidableEq (Associates (Ideal A))]
  [DecidableEq (Associates (Ideal B))] [∀ p : Associates (Ideal A), Decidable (Irreducible p)]
  [∀ p : Associates (Ideal B), Decidable (Irreducible p)] :
    (Associates.mk w.asIdeal).count (Associates.mk (Ideal.map (algebraMap A B) I)).factors =
    Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal *
      (Associates.mk (comap A w).asIdeal).count (Associates.mk I).factors := by
  classical
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [Associates.mk_zero, Ideal.zero_eq_bot, Ideal.map_bot, ← Ideal.zero_eq_bot,
      Associates.mk_zero]
    simp [Associates.count, Associates.factors_zero, w.associates_irreducible,
      associates_irreducible (comap A w), Associates.bcount]
  | h₂ I hI =>
    obtain rfl : I = ⊤ := by simpa using hI
    simp only [Ideal.map_top]
    simp only [← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one]
    rw [Associates.count_zero (associates_irreducible _),
      Associates.count_zero (associates_irreducible _), mul_zero]
  | h₃ I p hI hp IH =>
    simp only [Ideal.map_mul, ← Associates.mk_mul_mk]
    have hp_bot : p ≠ ⊥ := hp.ne_zero
    have hp_bot' := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hp_bot
    have hI_bot := (Ideal.map_eq_bot_iff_of_injective hAB).not.mpr hI
    rw [Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot) (Associates.mk_ne_zero.mpr hI)
      (associates_irreducible _), Associates.count_mul (Associates.mk_ne_zero.mpr hp_bot')
      (Associates.mk_ne_zero.mpr hI_bot) (associates_irreducible _)]
    simp only [IH, mul_add]
    congr 1
    by_cases hw : (w.comap A).asIdeal = p
    · have : Irreducible (Associates.mk p) := Associates.irreducible_mk.mpr hp.irreducible
      rw [hw, Associates.factors_self this, Associates.count_some this]
      simp only [Multiset.nodup_singleton, Multiset.mem_singleton, Multiset.count_eq_one_of_mem,
        mul_one]
      rw [count_associates_factors_eq hp_bot' w.2 w.3,
        Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hp_bot' w.2 w.3]
    · have : (Associates.mk (comap A w).asIdeal).count (Associates.mk p).factors = 0 :=
        Associates.count_eq_zero_of_ne (associates_irreducible _)
          (Associates.irreducible_mk.mpr hp.irreducible)
          (by rwa [ne_eq, Associates.mk_eq_mk_iff_associated, associated_iff_eq])
      rw [this, mul_zero, eq_comm]
      by_contra H
      rw [eq_comm, ← ne_eq, Associates.count_ne_zero_iff_dvd hp_bot' (irreducible w),
        Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap] at H
      apply hw (((Ideal.isPrime_of_prime hp).isMaximal hp_bot).eq_of_le (comap A w).2.ne_top H).symm

lemma ramificationIdx_ne_zero (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) :
    Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal ≠ 0 :=
  Ideal.IsDedekindDomain.ramificationIdx_ne_zero
    ((Ideal.map_eq_bot_iff_of_injective hAB).not.mpr (comap A w).3) w.2 Ideal.map_comap_le

/-- If w | v then for a ∈ A we have w(a)=v(a)^e where e is the ramification index. -/
lemma intValuation_comap (hAB : Function.Injective (algebraMap A B))
    (w : HeightOneSpectrum B) (x : A) :
    (comap A w).intValuation x ^
    (Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal) =
    w.intValuation (algebraMap A B x) := by
  classical
  have h_ne_zero := ramificationIdx_ne_zero A B hAB w
  by_cases hx : x = 0
  · simpa [hx]
  simp only [intValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
  change (ite _ _ _) ^ _ = ite _ _ _
  rw [map_eq_zero_iff _ hAB, if_neg hx, if_neg hx, ← Set.image_singleton, ← Ideal.map_span,
    mk_count_factors_map _ _ hAB, mul_comm]
  simp

omit [IsIntegralClosure B A L] in
/-- If w | v then for x ∈ K we have w(x)=v(x)^e where e is the ramification index. -/
lemma valuation_comap (w : HeightOneSpectrum B) (x : K) :
    (comap A w).valuation K x ^
      (Ideal.ramificationIdx (algebraMap A B) (comap A w).asIdeal w.asIdeal) =
    w.valuation L (algebraMap K L x) := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  simp [valuation, ← IsScalarTower.algebraMap_apply A K L, IsScalarTower.algebraMap_apply A B L,
    ← intValuation_comap A B (algebraMap_injective_of_field_isFractionRing A B K L), div_pow]

include K L in
omit [IsDedekindDomain A] [IsIntegralClosure B A L]
    [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
lemma noZeroSMulDivisors [IsDomain B] : NoZeroSMulDivisors A B := by
  have := FaithfulSMul.of_field_isFractionRing A B K L
  infer_instance

include K L in
omit [IsIntegralClosure B A L] [IsFractionRing B L] in
/-- There are only finitely many nonzero primes of B above a nonzero prime of A. -/
theorem Extension.finite (v : HeightOneSpectrum A) : Finite (v.Extension B) := by
  have := noZeroSMulDivisors A K L B
  rw [Extension, ← Set.coe_setOf]
  rw [@Set.finite_coe_iff]
  have := primesOver_finite v.asIdeal B
  refine Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal) ?_ ?_
  · refine Set.Finite.subset this ?_
    simp only [Set.subset_def, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    rintro w rfl
    simp only [Ideal.primesOver, Set.mem_setOf_eq, isPrime, true_and]
    constructor
    simp [Ideal.under_def, comap]
  · intro x hx y hy hxy
    rwa [← @HeightOneSpectrum.ext_iff] at hxy

end BaseChange

end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain

open scoped TensorProduct

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsAlgebraic K L]

/-- The canonical `K`-linear isomorphism `L ≅ K ⊗ B`. -/
noncomputable def LinearEquivTensorProduct :
    L ≃ₗ[K] K ⊗[A] B :=
  let f := LocalizedModule.equivTensorProduct (nonZeroDivisors A) B
  have := IsIntegralClosure.isLocalization A K L B
  have : IsLocalizedModule (nonZeroDivisors A) (IsScalarTower.toAlgHom A B L).toLinearMap :=
    inferInstance
  let g : LocalizedModule (nonZeroDivisors A) B ≃ₗ[A] L := @IsLocalizedModule.iso
      _ _ (nonZeroDivisors A) _ _ _ _ _ _ (IsScalarTower.toAlgHom A B L) this
  let h := TensorProduct.congr (Localization.algEquiv (nonZeroDivisors A) K) (LinearEquiv.refl A B)
  LinearEquiv.extendScalarsOfIsLocalization (nonZeroDivisors A) K
    <| g.symm.trans (f.restrictScalars A) |>.trans h

lemma LinearEquivTensorProduct_symm_one_tmul (b : B) :
    (LinearEquivTensorProduct A K L B).symm (1 ⊗ₜ b) =
    (algebraMap _ _ b) := by
  have : (SemilinearEquivClass.semilinearEquiv (Localization.algEquiv (nonZeroDivisors A) K)).symm
      1 = 1 :=
    map_one (Localization.algEquiv (nonZeroDivisors A) K).symm
  simp [LinearEquivTensorProduct, this]

lemma LinearEquivTensorProduct_symm_tmul (k : K) (b : B) :
    (LinearEquivTensorProduct A K L B).symm (k ⊗ₜ b) =
    k • (algebraMap _ _ b) := by
  have : k ⊗ₜ b = k • (1 ⊗ₜ b : K ⊗[A] B) := by
    simp [TensorProduct.smul_tmul']
  rw [this, LinearEquiv.map_smul, LinearEquivTensorProduct_symm_one_tmul]

variable (M : Type*) [AddCommGroup M] [Module K M] [Module A M] [IsScalarTower A K M]

/-- The canonical `A`-linear isomorphism `L ⊗ M ≅ B ⊗ M` for any `K`-module `M`. -/
noncomputable def LinearEquivTensorProductModule : L ⊗[K] M ≃ₗ[A] B ⊗[A] M :=
  let f₁ : L ⊗[K] M ≃ₗ[A] L ⊗[A] M := IsLocalization.moduleTensorEquiv (nonZeroDivisors A) K L M
    |>.restrictScalars A
  let f₂ : L ≃ₗ[A] B ⊗[A] K := LinearEquivTensorProduct A K L B
    |>.restrictScalars A
    |>.trans (TensorProduct.comm A K B)
  let f₃ : L ⊗[A] M ≃ₗ[A] (B ⊗[A] K) ⊗[A] M := TensorProduct.congr f₂ (LinearEquiv.refl A M)
  let f₄ : (B ⊗[A] K) ⊗[A] M ≃ₗ[A] B ⊗[A] (K ⊗[A] M) :=
    TensorProduct.assoc A B K M
  let f₅ : B ⊗[A] (K ⊗[A] M) ≃ₗ[A] B ⊗[A] M := TensorProduct.congr (LinearEquiv.refl A B)
    (IsLocalization.moduleLid (nonZeroDivisors A) K M |>.restrictScalars A)
  f₁.trans f₃ |>.trans f₄ |>.trans f₅

lemma LinearEquivTensorProductModule_symm_tmul (b : B) (m : M) :
    (LinearEquivTensorProductModule A K L B M).symm (b ⊗ₜ m) = (algebraMap B L b) ⊗ₜ m := by
  simp [LinearEquivTensorProductModule, LinearEquivTensorProduct_symm_one_tmul]

lemma LinearEquivTensorProductModule_tmul (b : B) (m : M) :
    (LinearEquivTensorProductModule A K L B M) ((algebraMap B L b) ⊗ₜ m) = b ⊗ₜ m := by
  rw [← LinearEquiv.eq_symm_apply, LinearEquivTensorProductModule_symm_tmul]

end IsDedekindDomain
