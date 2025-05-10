import Mathlib.Data.Subtype

theorem Subtype.map_ne {α β : Sort*} {p : α → Prop} {q : β → Prop} (f g : α → β)
    (h₁ : ∀ (a : α), p a → q (f a)) (h₂ : ∀ (a : α), p a → q (g a))
    (h₃ : ∀ (a₁ a₂ : α), p a₁ → p a₂ → f a₁ ≠ g a₂) :
    ∀ x y, Subtype.map f h₁ x ≠ Subtype.map g h₂ y := by
  simp only [Subtype.map_def, ne_eq, Subtype.mk.injEq]
  exact fun x y => h₃ _ _ x.2 y.2
