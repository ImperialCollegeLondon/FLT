import Mathlib.RingTheory.Ideal.Operations

open scoped Pointwise
variable (R : Type*) [CommSemiring R]

theorem Submodule.smul_one_eq_span (x : R) : x • (1 : Submodule R R) = Ideal.span {x} := by
  rw [← Submodule.singleton_set_smul, Ideal.one_eq_top, Submodule.set_smul_top_eq_span]
