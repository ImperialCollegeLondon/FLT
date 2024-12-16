import Mathlib

variable {R : Type*} [Semiring R]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {p p' : Submodule R M}

variable {P : M → Prop}

@[simp high]
lemma Submodule.forall_mem_sup : (∀ x ∈ p ⊔ p', P x) ↔ (∀ x₁ ∈ p, ∀ x₂ ∈ p', P (x₁ + x₂)) := by
  simp [Submodule.mem_sup]
  aesop

@[simp high]
lemma Submodule.exists_mem_sup : (∃ x ∈ p ⊔ p', P x) ↔ (∃ x₁ ∈ p, ∃ x₂ ∈ p', P (x₁ + x₂)) := by
  simp [Submodule.mem_sup]

#min_imports
