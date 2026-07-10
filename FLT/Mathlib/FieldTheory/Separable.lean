/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude
-/
module

public import Mathlib.FieldTheory.Separable

/-!
# Non-separable polynomials share a monic factor with their derivative

Material for `Mathlib.FieldTheory.Separable`.
-/

@[expose] public section

open Polynomial

/-- A nonzero polynomial over a field that is not separable has a monic common divisor of
positive degree with its derivative, namely its normalized gcd with the derivative. -/
theorem Polynomial.exists_monic_dvd_dvd_derivative_of_not_separable {k : Type*} [Field k]
    {p : k[X]} (hp : p ≠ 0) (hns : ¬p.Separable) :
    ∃ q : k[X], q.Monic ∧ 0 < q.natDegree ∧ q ∣ p ∧ q ∣ derivative p := by
  classical
  rw [separable_def, ← EuclideanDomain.gcd_isUnit_iff] at hns
  have hg0 : EuclideanDomain.gcd p (derivative p) ≠ 0 := fun h ↦
    hp (zero_dvd_iff.mp (h ▸ EuclideanDomain.gcd_dvd_left p (derivative p)))
  exact ⟨normalize (EuclideanDomain.gcd p (derivative p)), monic_normalize hg0,
    (monic_normalize hg0).natDegree_pos.mpr fun h ↦ hns (normalize_eq_one.mp h),
    normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_left _ _),
    normalize_dvd_iff.mpr (EuclideanDomain.gcd_dvd_right _ _)⟩

end
