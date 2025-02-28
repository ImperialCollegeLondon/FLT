import Mathlib.Topology.Algebra.Valued.ValuationTopology

variable {F : Type*} [Field F]

@[simp]
lemma Valued.isUnit_valuationSubring_iff {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Valued F Γ₀] {x : Valued.v.valuationSubring} :
    IsUnit x ↔ Valued.v (x.val : F) = 1 := by
  convert Valuation.Integers.isUnit_iff_valuation_eq_one _
  exact Valuation.integer.integers _
