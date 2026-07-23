/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.Algebra.Polynomial.Splits

/-!
# Polynomials of degree at most two split once they have a root

Material for `Mathlib.Algebra.Polynomial.Splits`.
-/

@[expose] public section

namespace Polynomial

/-- A polynomial of degree at most `2` over a field splits as soon as it has a root: the root
splits off a linear factor and the cofactor is linear. -/
theorem Splits.of_natDegree_le_two_of_isRoot {k : Type*} [Field k] {p : k[X]}
    (hdeg : p.natDegree ≤ 2) {x : k} (hx : p.IsRoot x) : p.Splits := by
  rcases eq_or_ne p 0 with rfl | hp0
  · exact .zero
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hx
  have hq0 : q ≠ 0 := fun h ↦ hp0 (by rw [hq, h, mul_zero])
  have hqdeg : q.natDegree ≤ 1 := by
    rw [hq, natDegree_mul (X_sub_C_ne_zero x) hq0, natDegree_X_sub_C] at hdeg
    lia
  rw [hq]
  exact (Splits.of_natDegree_le_one (natDegree_X_sub_C x).le).mul (.of_natDegree_le_one hqdeg)

end Polynomial

end
