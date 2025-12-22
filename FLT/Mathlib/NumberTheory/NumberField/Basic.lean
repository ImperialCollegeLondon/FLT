import Mathlib.NumberTheory.NumberField.Basic

theorem Rat.ringOfIntegersEquiv_symm_coe (x : ℤ) :
    (ringOfIntegersEquiv.symm x : ℚ) = ↑x :=
  eq_intCast ringOfIntegersEquiv.symm _ ▸ rfl
