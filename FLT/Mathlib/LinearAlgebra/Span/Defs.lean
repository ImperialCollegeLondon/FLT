import Mathlib.LinearAlgebra.Span.Defs

open Pointwise

variable {R : Type*} [Semiring R]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {p p' : Submodule R M}

variable {P : M → Prop}

namespace Submodule

@[simp high]
lemma forall_mem_sup : (∀ x ∈ p ⊔ p', P x) ↔ (∀ x₁ ∈ p, ∀ x₂ ∈ p', P (x₁ + x₂)) := by
  simp [mem_sup]
  aesop

@[simp high]
lemma exists_mem_sup : (∃ x ∈ p ⊔ p', P x) ↔ (∃ x₁ ∈ p, ∃ x₂ ∈ p', P (x₁ + x₂)) := by
  simp [mem_sup]

@[simp, norm_cast]
lemma coe_sup' : ↑(p ⊔ p') = (p : Set M) + (p' : Set M) := by
  simp [coe_sup]

end Submodule
