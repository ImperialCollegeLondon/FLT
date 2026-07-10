/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Valuative relations

Material destined for Mathlib.
-/

@[expose] public section

namespace ValuativeRel

variable {R : Type*} [Ring R] [ValuativeRel R]

/-- Naturals have valuation at most `1`: they lie in the integer subring
`(valuation R).integer` of the valuation. -/
theorem valuation_natCast_le_one (m : ℕ) : valuation R (m : R) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp (natCast_mem (valuation R).integer m)

/-- Integers have valuation at most `1`: they lie in the integer subring
`(valuation R).integer` of the valuation. -/
theorem valuation_intCast_le_one (m : ℤ) : valuation R (m : R) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp (intCast_mem (valuation R).integer m)

/-- Powers of an element of the open unit disc become arbitrarily small. This is where the
rank-one hypothesis on the value group enters (via the strictly monotone embedding into
`ℝ≥0` provided by `IsRankLeOne`, where the statement is the usual archimedean one): an
abstract value group of higher rank need not be archimedean, and the statement would be
false. -/
theorem exists_pow_valuation_lt [IsRankLeOne R] (q : R) (hq : valuation R q < 1)
    (γ : (ValueGroupWithZero R)ˣ) : ∃ N : ℕ, valuation R q ^ N < γ := by
  rcases eq_or_ne (valuation R q) 0 with h0 | h0
  · exact ⟨1, by simp [h0]⟩
  · obtain ⟨s⟩ := IsRankLeOne.nonempty (R := R)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
      (show 0 < s.emb γ by simpa using s.strictMono (zero_lt_iff.mpr γ.ne_zero))
      (show s.emb (valuation R q) < 1 by simpa using s.strictMono hq)
    exact ⟨N, s.strictMono.lt_iff_lt.mp (by rwa [map_pow])⟩

/-! ### Bridging the adic and canonical valuations

Mathlib's reduction theory of elliptic curves is phrased in the adic valuation attached to
the maximal ideal of the discrete valuation ring `𝒪[K]`
(`IsDedekindDomain.HeightOneSpectrum.valuation`), while the Tate curve files work with the
canonical `ValuativeRel` valuation of `K`. On integral elements the two agree on the only
distinctions that matter — `< 1` (maximal-ideal membership, i.e. non-unitality) and `= 1`
(unitality) — and the two lemmas below convert between them in both directions.
-/

section AdicValuation

variable {K : Type*} [Field K] [ValuativeRel K]
  [IsDiscreteValuationRing (valuation K).integer] [IsFractionRing (valuation K).integer K]

/-- On an integral element, the adic valuation attached to the maximal ideal of `𝒪[K]` is
less than `1` exactly when the canonical valuation is: both detect membership in the
maximal ideal, i.e. non-unitality in `𝒪[K]`. -/
theorem adicValuation_lt_one_iff {x : (valuation K).integer} :
    (IsDiscreteValuationRing.maximalIdeal (valuation K).integer).valuation K
        (algebraMap (valuation K).integer K x) < 1 ↔
      valuation K (algebraMap (valuation K).integer K x) < 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  exact ⟨fun h ↦ Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp
      (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp h)),
    fun h ↦ (IsLocalRing.mem_maximalIdeal _).mpr
      (mem_nonunits_iff.mpr (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr h))⟩

/-- On an integral element, the adic valuation attached to the maximal ideal of `𝒪[K]`
equals `1` exactly when the canonical valuation does: both detect unitality in `𝒪[K]`. -/
theorem adicValuation_eq_one_iff {x : (valuation K).integer} :
    (IsDiscreteValuationRing.maximalIdeal (valuation K).integer).valuation K
        (algebraMap (valuation K).integer K x) = 1 ↔
      valuation K (algebraMap (valuation K).integer K x) = 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  exact ⟨fun h ↦ (Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mp
      (by
        by_contra hne
        exact h ((IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hne))),
    fun h hmem ↦ mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)
      ((Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mpr h)⟩

end AdicValuation

end ValuativeRel

namespace ValuativeExtension

open ValuativeRel

/-! ### Transfer of the valuation along a valuative extension

A valuative extension `A → B` preserves `≤ 1`, `< 1` and `= 1` of the valuation: the
induced map of value groups `mapValueGroupWithZero` is a strictly monotone
monoid-with-zero homomorphism sending `valuation A x` to `valuation B (algebraMap A B x)`.
Equivalently, `algebraMap A B` maps the ring of integers `𝒪[A]` into `𝒪[B]`, its maximal
ideal into that of `𝒪[B]`, and units to units.
-/

variable {A B : Type*} [CommRing A] [Ring B] [ValuativeRel A] [ValuativeRel B]
  [Algebra A B] [ValuativeExtension A B]

/-- A valuative extension maps the closed unit disc into the closed unit disc; in other
words, `algebraMap A B` maps the ring of integers `𝒪[A]` into `𝒪[B]`. -/
theorem valuation_algebraMap_le_one {x : A} (hx : valuation A x ≤ 1) :
    valuation B (algebraMap A B x) ≤ 1 := by
  simpa using (mapValueGroupWithZero_strictMono (A := A) (B := B)).monotone hx

/-- A valuative extension maps the open unit disc into the open unit disc; in other
words, `algebraMap A B` maps the maximal ideal of `𝒪[A]` into that of `𝒪[B]`. -/
theorem valuation_algebraMap_lt_one {x : A} (hx : valuation A x < 1) :
    valuation B (algebraMap A B x) < 1 := by
  simpa using mapValueGroupWithZero_strictMono (A := A) (B := B) hx

/-- A valuative extension maps the unit circle into the unit circle; in other words,
`algebraMap A B` maps units of `𝒪[A]` to units of `𝒪[B]`. -/
theorem valuation_algebraMap_eq_one {x : A} (hx : valuation A x = 1) :
    valuation B (algebraMap A B x) = 1 := by
  rw [← mapValueGroupWithZero_valuation (B := B) x, hx, map_one]

end ValuativeExtension
