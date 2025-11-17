import FLT.DedekindDomain.FiniteAdeleRing.BaseChange
import FLT.Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.Padics.RingHoms

open IsDedekindDomain NumberField PadicInt RestrictedProduct

namespace IsDedekindDomain.HeightOneSpectrum

-- From pending mathlib PR #30576
/-- A generator in `ℕ` of a prime ideal of `𝓞 ℚ`. -/
noncomputable def natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) : ℕ :=
  Submodule.IsPrincipal.generator (v.asIdeal.map Rat.ringOfIntegersEquiv) |>.natAbs

-- From pending mathlib PR #30576
instance (v : HeightOneSpectrum (𝓞 ℚ)) : Fact v.natGenerator.Prime :=
  ⟨Int.prime_iff_natAbs_prime.1 <|
    Submodule.IsPrincipal.prime_generator_of_isPrime _
      ((Ideal.map_eq_bot_iff_of_injective Rat.ringOfIntegersEquiv.injective).not.2 v.ne_bot)⟩

-- From pending mathlib PR #30576
/-- The `ℚ`-algebra equivalence between `v.adicCompletion ℚ` and `ℚ_[v.natGenerator]`, where
`v : HeightOneSpectrum (𝓞 ℚ)`. -/
def padicEquiv (v : HeightOneSpectrum (𝓞 ℚ)) :
    v.adicCompletion ℚ ≃ₐ[ℚ] ℚ_[v.natGenerator] := sorry

-- From pending mathlib PR #30576
theorem padicEquiv_bijOn (v : HeightOneSpectrum (𝓞 ℚ)) :
    Set.BijOn (IsDedekindDomain.HeightOneSpectrum.padicEquiv v) (v.adicCompletionIntegers ℚ)
      (PadicInt.subring v.natGenerator) := by
  sorry

/-- The prime ideal of `𝓞 ℚ` constructed from a prime in `ℕ`. -/
def ofNatPrime {p : ℕ} (hp : p.Prime) : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {Rat.ringOfIntegersEquiv.symm p}
  isPrime := by
    have : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by simp [hp.ne_zero])).2 (Nat.prime_iff_prime_int.1 hp)
    have := Ideal.map_isPrime_of_equiv (I := Ideal.span {(p : ℤ)}) Rat.ringOfIntegersEquiv.symm
    simpa [Ideal.map_span] using this
  ne_bot := by simp [hp.ne_zero]

/-- The equivalence between prime ideals of `𝓞 ℚ` and primes in `ℕ`. -/
noncomputable def ratEquiv :
    HeightOneSpectrum (𝓞 ℚ) ≃ Nat.Primes where
  toFun v := ⟨v.natGenerator, Fact.out⟩
  invFun p := ofNatPrime p.2
  left_inv v := by
    simp only [ofNatPrime, natGenerator, ← Set.image_singleton, ← Ideal.map_span]
    ext; simp
  right_inv p := by
    simp [ofNatPrime, natGenerator, Ideal.map_span, Set.image_singleton, map_natCast,
      Int.associated_iff_natAbs.1 (Submodule.IsPrincipal.associated_generator_span_self (p : ℤ))]

end IsDedekindDomain.HeightOneSpectrum

namespace Padic

theorem setOf_norm_one_lt_finite (x : ℚ) :
    {p : Nat.Primes | 1 < ‖(x : ℚ_[p])‖}.Finite := by
  apply Set.Finite.subset _ fun p ↦ mt (Padic.norm_rat_le_one) ∘ not_le.2
  apply Set.Finite.of_finite_image _ Nat.Primes.coe_nat_injective.injOn
  apply Set.Finite.subset (s := x.den.primeFactors) (by simp)
  exact fun _ ⟨_, _, _⟩ ↦ by aesop

end Padic

namespace RestrictedProduct

theorem padic_valuation_neg_of_mem_indexSupport
    {x : Πʳ (p : Nat.Primes), [ℚ_[p], subring p]} {p : Nat.Primes} (hp : p ∈ x.indexSupport) :
    (x p).valuation < 0 := by
  contrapose! hp
  simpa [Padic.norm_le_one_iff_val_nonneg]

/-- The smallest positive natural `n : ℕ` for which `x p * n` is a `p`-adic integer for all `p`. -/
noncomputable def padicNatDen
    (x : Πʳ (p : Nat.Primes), [ℚ_[p], subring p]) : ℕ :=
  ∏ p ∈ x.indexSupport, p.1 ^ (x p).valuation.natAbs

theorem padicNatDen_ne_zero (x : Πʳ (p : Nat.Primes), [ℚ_[p], subring p]) :
    x.padicNatDen ≠ 0 := by
  rw [padicNatDen, Finset.prod_ne_zero_iff]
  intro p hp
  simp [p.2.ne_zero]

theorem padicNatDen_norm_of_mem {x : Πʳ (p : Nat.Primes), [ℚ_[p], subring p]} {p : Nat.Primes}
    (hp : p ∈ x.indexSupport) :
    ‖(x.padicNatDen : ℚ_[p])‖ = (p.1 : ℝ) ^ (-((x p).valuation.natAbs : ℤ)) := by
  simp only [padicNatDen, Nat.cast_prod, norm_prod, Nat.cast_pow, norm_pow]
  rw [Finset.prod_eq_single_of_mem p hp]
  · simp [← zpow_natCast, abs_eq_neg_self.2 (padic_valuation_neg_of_mem_indexSupport hp).le]
  · intro q hq hpq
    rw [Padic.norm_natCast_eq_one_iff.2]
    · simp
    · exact (Nat.coprime_primes p.2 q.2).2 (by simpa [Subtype.val_inj] using hpq.symm)

theorem padicNatDen_norm_of_notMem {x : Πʳ (p : Nat.Primes), [ℚ_[p], subring p]} {p : Nat.Primes}
    (hp : p ∉ x.indexSupport) :
    ‖(x.padicNatDen : ℚ_[p])‖ = 1 := by
  simp only [padicNatDen, Nat.cast_prod, norm_prod, Nat.cast_pow, norm_pow]
  refine Finset.prod_eq_one fun q hq ↦ ?_
  rw [(Padic.norm_natCast_eq_one_iff).2]
  · simp
  · exact (Nat.coprime_primes p.2 q.2).2
      (by simpa [Subtype.val_inj] using ne_of_mem_of_not_mem hq hp |>.symm)

theorem padicNatDen_norm_mul_le_one (x : Πʳ (p : Nat.Primes), [ℚ_[p], subring p]) (p : Nat.Primes) :
    ‖(x.padicNatDen : ℚ) * x p‖ ≤  1 := by
  by_cases hp : p ∈ x.indexSupport
  · by_cases hx : x p = 0
    · simp [hx]
    · simp only [Rat.cast_natCast, norm_mul, padicNatDen_norm_of_mem hp, Nat.cast_natAbs,
        abs_eq_neg_self.2 (padic_valuation_neg_of_mem_indexSupport hp).le, Int.cast_neg,
        Int.cast_eq, neg_neg, Padic.norm_eq_zpow_neg_valuation hx, zpow_neg]
      rw [mul_inv_cancel₀ (zpow_ne_zero _ (by simp [p.2.ne_zero]))]
  · simp_all [padicNatDen_norm_of_notMem hp]

/-- The element of `(p : Nat.Primes) → ℤ_[p]` obtained by multiplying by `padicNatDen`. -/
noncomputable def padicNum (x : Πʳ (p : Nat.Primes), [ℚ_[p], subring p]) (p : Nat.Primes) : ℤ_[p] :=
  ⟨x.padicNatDen * x p, x.padicNatDen_norm_mul_le_one p⟩

theorem padic_exists_sub_mem_padicInt
    (x : Πʳ (p : Nat.Primes), [ℚ_[p], subring p]) :
    ∃ q : ℚ, ∀ p : Nat.Primes, q - x p ∈ subring p := by
  -- At `p` for which `x p` is non-integral cast `x.padicNum` to `ZMod (p ^ (x p).valuation.natAbs)`
  let padicNum_bar (p : x.indexSupport) : ZMod (p ^ (x p).valuation.natAbs) :=
    PadicInt.toZModPow (x p).valuation.natAbs (x.padicNum p)
  let a : x.indexSupport → ℕ := fun p ↦ p ^ (x p).valuation.natAbs
  have ha : Pairwise fun i j ↦ (a i).Coprime (a j) :=
    fun p q h ↦ Nat.coprime_pow_primes _ _ p.1.2 q.1.2 (by simpa [Subtype.val_inj] using h)
  -- Use Chinese Remainder Theorem to lift `padicNum_bar` to an integer `X : ℤ`
  obtain ⟨X, hX⟩ := Ideal.exists_forall_sub_mem_ideal
    (fun _ _ h ↦ (Ideal.isCoprime_span_singleton_iff _ _).2 ((ha h).cast (R := ℤ)))
    (fun p ↦ (padicNum_bar p).val)
  -- `X - x.padicNum p` is divisible by `p ^ (x p).valuation.natAbs` for all `p ∈ x.indexSupport`
  have h_sub_mem (p : x.indexSupport) :
      (X - x.padicNum p : ℤ_[p]) ∈ Ideal.span {(p ^ (x p).valuation.natAbs : ℤ_[p])} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_intCast, ← id_eq (toZModPow _ _),
      ← ZMod.cast_id', ← ZMod.intCast_cast, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd,
      ← ZMod.natCast_val, ← Ideal.mem_span_singleton]
    exact hX p
  -- so `X / x.padicNatDen` works
  use X / x.padicNatDen
  intro p
  by_cases hp : p ∈ x.indexSupport
  · have : X / x.padicNatDen - x p = (X - x.padicNatDen * x p) / x.padicNatDen := by
      ring_nf
      rw [mul_inv_cancel₀ (by simpa using x.padicNatDen_ne_zero), one_mul]
    simp only [Rat.cast_div, Rat.cast_natCast, PadicInt.mem_subring_iff, Rat.cast_intCast,
      this, norm_div, ge_iff_le]
    have h : ‖X - x.padicNatDen * x p‖ ≤ ‖(x.padicNatDen : ℚ_[p])‖ := by
      rw [padicNatDen_norm_of_mem hp]
      simpa using (PadicInt.norm_le_pow_iff_mem_span_pow _ _).2 (h_sub_mem ⟨p, hp⟩)
    grw [h]
    exact div_self (by simp [x.padicNatDen_ne_zero]) |>.le
  · apply Subring.sub_mem _ _ (by simpa using hp)
    simpa [padicNatDen_norm_of_notMem hp] using Padic.norm_int_le_one _

noncomputable instance : Algebra ℚ (Πʳ (p : Nat.Primes), [ℚ_[p], subring p]) :=
  let f : RingHom ℚ (Πʳ (p : Nat.Primes), [ℚ_[p], subring p]) := {
    toFun k := ⟨fun i ↦ k, by simpa using Padic.setOf_norm_one_lt_finite k⟩
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl
  }
  f.toAlgebra

theorem padic_exists_sub_mem_structureSubring
    (a : Πʳ (p : Nat.Primes), [ℚ_[p], subring p]) :
    ∃ q : ℚ, a - algebraMap ℚ _ q ∈ structureSubring _ _ _ := by
  obtain ⟨r, hr⟩ := padic_exists_sub_mem_padicInt a
  exact ⟨r, mem_structureSubring_iff.2 fun p ↦ by simpa using Subring.neg_mem _ (hr p)⟩

end RestrictedProduct
