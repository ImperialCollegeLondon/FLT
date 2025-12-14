import Mathlib.Data.Real.Archimedean

-- golf
theorem Real.exists_floor' (x : ℝ) : ∃ ub : ℤ, (ub : ℝ) ≤ x ∧ ∀ z : ℤ, (z : ℝ) ≤ x → z ≤ ub :=
  ⟨⌊x⌋, Int.floor_le x, fun _ ↦ Int.le_floor.mpr⟩

lemma Int.eq_floor {a : ℝ} {b : ℤ} (h1 : 0 ≤ a - b) (h2 : a - b < 1) : b = ⌊a⌋ := by
  rw [eq_comm, Int.floor_eq_iff]
  grind
