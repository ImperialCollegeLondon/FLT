import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.NumberField.FinitePlaces
import FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation

open IsDedekindDomain HeightOneSpectrum adicCompletion NumberField UniformSpace.Completion

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

variable {R : Type*} [CommRing R] [Algebra R ℚ] [IsIntegralClosure R ℤ ℚ]

namespace Rat.HeightOneSpectrum.IsIntegralClosure

instance : Module.Free ℤ R := .of_equiv (IsIntegralClosure.intEquiv R).toIntLinearEquiv.symm

instance : Module.Finite ℤ R := .equiv (IsIntegralClosure.intEquiv R).toIntLinearEquiv.symm

instance : IsPrincipalIdealRing R := .of_surjective _ (IsIntegralClosure.intEquiv R).symm.surjective

@[simp]
theorem intEquiv_apply_coe (z : R) :
    (IsIntegralClosure.intEquiv R z : R) = z := by
  obtain ⟨z, rfl⟩ := (IsIntegralClosure.intEquiv R).symm.surjective z
  simp

end IsIntegralClosure

theorem pow_natGenerator_dvd_iff (v : HeightOneSpectrum R) {n : ℕ} (m : ℕ) :
    natGenerator v ^ m ∣ n ↔ ↑n ∈ (v.asIdeal.map (IsIntegralClosure.intEquiv R)) ^ m := by
  rw [← span_natGenerator, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact Int.ofNat_dvd.symm

variable [IsDedekindDomain R]

theorem natGenerator_eq_absNorm (v : HeightOneSpectrum R) :
    natGenerator v = Ideal.absNorm v.asIdeal := by
  rw [natGenerator]
  conv_lhs =>
    enter[1, 1]
    rw [← Int.ideal_span_absNorm_eq_self (Ideal.map (IsIntegralClosure.intEquiv R) v.asIdeal)]
  rw [Int.natAbs_eq_iff_associated.2 <| Submodule.IsPrincipal.associated_generator_span_self _]
  obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal v.asIdeal
  simp only [hg, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton,
    Ideal.absNorm_span_singleton, Algebra.norm_self, MonoidHom.id_apply]
  rw [← Algebra.norm_eq_of_ringEquiv (IsIntegralClosure.intEquiv R) (by ext; simp)]
  simp [-Nat.cast_natAbs]

theorem intValuation_eq_padicValuation_iff_multiplicity_eq_multiplicity {x : R}
    (v : HeightOneSpectrum R) (hx : x ≠ 0) :
    intValuation v x = padicValuation (primesEquiv v) (IsIntegralClosure.intEquiv R x) ↔
      multiplicity v.asIdeal (Ideal.span {x}) = multiplicity (primesEquiv v).1
        (IsIntegralClosure.intEquiv R x).natAbs := by
  simp [intValuation_eq_coe_neg_multiplicity _ hx, padicValuation, hx,
    padicValInt, padicValNat_def <| Int.natAbs_ne_zero.2 <|
      (IsIntegralClosure.intEquiv R).map_ne_zero_iff.2 hx]

variable [IsFractionRing R ℚ]

theorem valuation_apply_coe_eq_padicValuation (x : R)
    (v : HeightOneSpectrum R) :
    v.valuation ℚ (algebraMap R ℚ x) = padicValuation (primesEquiv v)
      (IsIntegralClosure.intEquiv R x) := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [intValuation_eq_padicValuation_iff_multiplicity_eq_multiplicity v hx]
    exact multiplicity_eq_of_emultiplicity_eq <| emultiplicity_eq_emultiplicity_iff.2
      fun n ↦ by simp [primesEquiv, pow_natGenerator_dvd_iff v n, ← Ideal.map_pow]

theorem valuation_apply_eq_padicValuation (v : HeightOneSpectrum R) (x : ℚ) :
    v.valuation ℚ x = padicValuation (primesEquiv v) x := by
  obtain ⟨⟨n, d, hd⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) x
  obtain rfl : x = IsLocalization.mk' ℚ n ⟨d, hd⟩ := IsLocalization.eq_mk'_iff_mul_eq.mpr hx
  simp [IsFractionRing.mk'_eq_div, map_div₀, valuation_apply_coe_eq_padicValuation,
    IsIntegralClosure.intEquiv, RingOfIntegers.equiv]

theorem adicCompletion.padicEquiv_cast
    (v : IsDedekindDomain.HeightOneSpectrum R) (x : WithVal (v.valuation ℚ)) :
    (padicEquiv v) x = Padic.withValRingEquiv (mapEquiv (withValEquiv v) x) := by
  rfl

-- Only have `Norm (v.adicCompletion ℚ)` for `R = 𝓞 ℚ` so specialise from here

lemma adicCompletion.padicEquiv_norm_coe_eq
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (x : WithVal (v.valuation ℚ)) :
    ‖(padicEquiv v) x‖ = ‖algebraMap _ (v.adicCompletion ℚ) x‖ := by
  rw [padicEquiv_cast v x, mapEquiv_coe, Padic.coe_withValRingEquiv,
    extension_coe (
      by simpa using Padic.isUniformInducing_cast_withVal (p := primesEquiv v) |>.uniformContinuous
    )]
  change _ = ‖FinitePlace.embedding v x‖
  rw [FinitePlace.norm_def']
  rcases eq_or_ne x 0 with rfl | hx
  · simp [withValEquiv, Valuation.IsEquiv.uniformEquiv]
  · simp [padicValuation, withValEquiv, Valuation.IsEquiv.uniformEquiv,
      valuation_apply_eq_padicValuation, hx, primesEquiv, natGenerator_eq_absNorm v]
    -- TODO: need to fix some defeq abuse upstream in FinitePlace.norm_def' to avoid the next line
    rfl

lemma adicCompletion.padicEquiv_norm_eq
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) :
    ‖(padicEquiv v) x‖ = ‖x‖ := by
  induction x using induction_on with
  | hp => apply isClosed_eq <;> fun_prop
  | ih => simp [padicEquiv_norm_coe_eq v, UniformSpace.Completion.algebraMap_def]

end Rat.HeightOneSpectrum
