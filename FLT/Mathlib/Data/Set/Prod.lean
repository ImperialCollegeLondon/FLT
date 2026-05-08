/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper, Kevin Buzzard
-/
module

public import Mathlib.Data.Set.Operations

/-!
# Prod

Material destined for Mathlib.
-/

@[expose] public section

namespace Set

variable {ι : Type*} {α : ι → Type*} {s₁ s₂ : Set ι} {t : ∀ i, Set (α i)} {i : ι}

theorem pi_subset_pi_of_superset (h : s₁ ⊆ s₂) : pi s₂ t ⊆ pi s₁ t :=
  fun _ hx i hi ↦ hx i <| h hi

end Set
