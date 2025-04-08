import Mathlib.Topology.Algebra.Valued.ValuationTopology

variable {F : Type*} [Field F]

@[simp]
lemma Valued.isUnit_valuationSubring_iff {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [Valued F Γ₀] {x : Valued.v.valuationSubring} :
    IsUnit x ↔ Valued.v (x.val : F) = 1 := by
  convert Valuation.Integers.isUnit_iff_valuation_eq_one _
  exact Valuation.integer.integers _

/-- The unit ball of a valued ring is closed. -/
theorem Valued.integer_isClosed ( R : Type* ) {Γ₀ : Type*} [Ring R]
    [LinearOrderedCommGroupWithZero Γ₀] [_i : Valued R Γ₀] : IsClosed (_i.v.integer : Set R) := by
  rw [← Subring.coe_toAddSubgroup]
  apply AddSubgroup.isClosed_of_isOpen
  apply integer_isOpen

/-- The valuation subring of a valued field is closed. -/
theorem Valued.valuationSubring_isClosed {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    [hv : Valued F Γ₀] :
    IsClosed (hv.v.valuationSubring : Set F) :=
  integer_isClosed F
