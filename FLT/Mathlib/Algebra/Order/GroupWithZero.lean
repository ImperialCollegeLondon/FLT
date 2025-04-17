import Mathlib.Algebra.Order.GroupWithZero.Canonical

namespace WithZero

lemma exists_ne_zero_and_lt {G : Type*} [LinearOrder G] [NoMinOrder G]
  {x : WithZero G} (hx : x ≠ 0) :
    ∃ y, y ≠ 0 ∧ y < x := by
  obtain ⟨z, hlt⟩ := exists_lt (WithZero.unzero hx)
  rw [← WithZero.coe_lt_coe, WithZero.coe_unzero hx] at hlt
  use z, WithZero.coe_ne_zero

lemma exists_ne_zero_and_le_and_le {G : Type*} [LinearOrder G]
  {x y : WithZero G} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z, z ≠ 0 ∧ z ≤ x ∧ z ≤ y := by
  let z := x ⊓ y
  use z
  constructor
  . unfold z
    intro hz
    rw [min_eq_iff] at hz
    tauto
  . constructor <;> simp_all [z]

lemma exists_ne_zero_and_lt_and_lt {G : Type*} [LinearOrder G] [NoMinOrder G]
  {x y : WithZero G} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z, z ≠ 0 ∧ z < x ∧ z < y := by
  obtain ⟨z', hnz', hzx, hzy⟩ := exists_ne_zero_and_le_and_le hx hy
  obtain ⟨z, hnz, hlt⟩ := exists_ne_zero_and_lt hnz'
  use z, hnz
  constructor <;> exact lt_of_lt_of_le hlt ‹z' ≤ _›

end WithZero
