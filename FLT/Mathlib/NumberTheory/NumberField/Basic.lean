import Mathlib.NumberTheory.NumberField.Basic

open scoped NumberField

-- Mathlib PR #20544
theorem Rat.ringOfIntegersEquiv_eq_algebraMap (z : 𝓞 ℚ) :
    (Rat.ringOfIntegersEquiv z : ℚ) = algebraMap (𝓞 ℚ) ℚ z := by
  obtain ⟨z, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective z
  simp
