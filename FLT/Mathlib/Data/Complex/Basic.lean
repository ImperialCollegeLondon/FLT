import Mathlib.Data.Complex.Basic

open Set

namespace Complex
variable {s t : Set ℝ}

open Set

lemma «forall» {p : ℂ → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ := by aesop
lemma «exists» {p : ℂ → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ := by aesop

@[simp] lemma reProdIm_nonempty : (s ×ℂ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := by
  simp [Set.Nonempty, reProdIm, Complex.exists]

@[simp] lemma reProdIm_eq_empty : s ×ℂ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp [← not_nonempty_iff_eq_empty, reProdIm_nonempty, -not_and, not_and_or]

end Complex
