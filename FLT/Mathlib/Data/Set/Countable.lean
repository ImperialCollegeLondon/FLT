import Mathlib.Data.Set.Countable

-- should be upstreamed
lemma Countable.of_countable_fibres {X Y : Type*} {f : X → Y} [Countable Y]
    (h : ∀ (y : Y), (f ⁻¹' {y}).Countable) : Countable X := by
  simp_rw [← Set.countable_univ_iff, ← Set.preimage_univ (f := f), ← Set.iUnion_of_singleton,
    Set.preimage_iUnion, Set.countable_iUnion ‹_›]
