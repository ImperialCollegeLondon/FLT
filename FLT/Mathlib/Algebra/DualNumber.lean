import Mathlib

open IsLocalRing

namespace DualNumber

lemma maximalIdeal_pow {k} [Field k] :
    maximalIdeal (DualNumber k) ^ 2 = ⊥ := by
  rw [← le_bot_iff, pow_two, Ideal.mul_le]
  rintro ⟨ra, rb⟩ hr ⟨sa, sb⟩ hs
  simp only [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst,
    TrivSqZeroExt.fst_mk, isUnit_iff_ne_zero, ne_eq, not_not] at hr hs
  ext <;> simp [hr, hs]
