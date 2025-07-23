import Mathlib.Data.Subtype

theorem Subtype.map_ne {α β : Sort*} {p : α → Prop} {q : β → Prop} {f g : α → β}
    (h₁ : ∀ a : α, p a → q (f a)) (h₂ : ∀ a : α, p a → q (g a))
    (x y : Subtype p) :
    map f h₁ x ≠ map g h₂ y ↔ f x ≠ g y :=
  .not ⟨congr_arg Subtype.val, (Subtype.ext ·)⟩
