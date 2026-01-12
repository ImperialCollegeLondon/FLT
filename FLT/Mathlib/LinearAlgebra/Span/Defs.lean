import Mathlib.LinearAlgebra.Span.Defs

open Pointwise

variable {R : Type*} [Semiring R]

variable {M : Type*} [AddCommMonoid M] [Module R M]

variable {p p' : Submodule R M}

variable {P : M → Prop}

namespace Submodule

@[simp, norm_cast]
lemma coe_sup' : ↑(p ⊔ p') = (p : Set M) + (p' : Set M) := by
  simp [coe_sup]

end Submodule
