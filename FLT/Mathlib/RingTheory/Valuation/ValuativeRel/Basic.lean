/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
module

public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Valuative relations

Material destined for Mathlib.
-/

@[expose] public section

namespace ValuativeRel

variable {R : Type*} [Ring R] [ValuativeRel R]

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
  · exact ⟨1, by rw [h0, pow_one]; exact zero_lt_iff.mpr γ.ne_zero⟩
  · obtain ⟨s⟩ := IsRankLeOne.nonempty (R := R)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
      (show 0 < s.emb γ from by simpa using s.strictMono (zero_lt_iff.mpr γ.ne_zero))
      (show s.emb (valuation R q) < 1 from by simpa using s.strictMono hq)
    exact ⟨N, s.strictMono.lt_iff_lt.mp (by rwa [map_pow])⟩

end ValuativeRel
