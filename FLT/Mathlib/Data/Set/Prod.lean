import Mathlib.Data.Set.Prod

namespace Set

variable {ι : Type*} {α : ι → Type*} {s₁ s₂ : Set ι} {t : ∀ i, Set (α i)} {i : ι}

theorem pi_subset_of_superset (h : s₁ ⊆ s₂) : pi s₂ t ⊆ pi s₁ t := fun _ hx i hi ↦ hx i <| h hi

end Set
