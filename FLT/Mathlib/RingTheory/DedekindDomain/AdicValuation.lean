import Mathlib.RingTheory.DedekindDomain.AdicValuation

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

variable (R K : Type*) [CommRing R] [Field K] [IsDedekindDomain R] [Algebra R K]
    [IsFractionRing R K] in
theorem mem_integers_of_valuation_le_one (x : K)
    (h : ∀ v : HeightOneSpectrum R, v.valuation x ≤ 1) : x ∈ (algebraMap R K).range := by
  obtain ⟨⟨n, d, hd⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors R) x
  obtain rfl : x = IsLocalization.mk' K n ⟨d, hd⟩ := IsLocalization.eq_mk'_iff_mul_eq.mpr hx
  have hd0 := nonZeroDivisors.ne_zero hd
  obtain rfl | hn0 := eq_or_ne n 0
  · simp
  suffices Ideal.span {d} ∣ (Ideal.span {n} : Ideal R) by
    obtain ⟨z, rfl⟩ := Ideal.span_singleton_le_span_singleton.1 (Ideal.le_of_dvd this)
    use z
    rw [map_mul, mul_comm,mul_eq_mul_left_iff] at hx
    cases' hx with h h
    · exact h.symm
    · simp [hd0] at h
  classical
  have ine : ∀ {r : R}, r ≠ 0 → Ideal.span {r} ≠ ⊥ := fun {r} ↦ mt Ideal.span_singleton_eq_bot.mp
  rw [← Associates.mk_le_mk_iff_dvd, ← Associates.factors_le, Associates.factors_mk _ (ine hn0),
    Associates.factors_mk _ (ine hd0), WithTop.coe_le_coe, Multiset.le_iff_count]
  rintro ⟨v, hv⟩
  obtain ⟨v, rfl⟩ := Associates.mk_surjective v
  have hv' := hv
  rw [Associates.irreducible_mk, irreducible_iff_prime] at hv
  specialize h ⟨v, Ideal.isPrime_of_prime hv, hv.ne_zero⟩
  simp_rw [valuation_of_mk', intValuation, ← Valuation.toFun_eq_coe,
    intValuationDef_if_neg _ hn0, intValuationDef_if_neg _ hd0, ← WithZero.coe_div,
    ← WithZero.coe_one, WithZero.coe_le_coe, Associates.factors_mk _ (ine hn0),
    Associates.factors_mk _ (ine hd0), Associates.count_some hv'] at h
  simpa using h
