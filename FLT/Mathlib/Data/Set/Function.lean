import Mathlib.Data.Set.Function

theorem Set.codRestrict_range_surjective {α ι : Type*} (f : ι → α) :
    ((Set.range f).codRestrict f fun _ => by simp).Surjective := by
  rintro ⟨b, ⟨a, rfl⟩⟩
  exact ⟨a, rfl⟩
