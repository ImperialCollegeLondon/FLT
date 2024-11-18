import Mathlib.LinearAlgebra.Determinant

namespace LinearMap
variable {R : Type*} [CommRing R]

variable (R) in
@[simp] lemma det_mul (a : R) : (mul R R a).det = a := by
  sorry
