import Mathlib.Order.Filter.Cofinite

-- TODO upstream
lemma Filter.cofinite.sets.countable (ι : Type*) [Countable ι] :
    (Filter.cofinite : Filter ι).sets.Countable :=
  Set.Countable.mono (fun _ h ↦ h) <|
  Set.Countable.preimage_of_injOn Set.Countable.setOf_finite compl_bijective.1.injOn

instance (ι : Type*) [Countable ι] : Countable (.cofinite : Filter ι).sets := by
  rw [Set.countable_coe_iff]
  exact Filter.cofinite.sets.countable ι
