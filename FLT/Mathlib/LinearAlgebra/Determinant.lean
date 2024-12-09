import Mathlib.LinearAlgebra.Determinant

namespace LinearMap
variable {R : Type*} [CommRing R]

@[simp] lemma det_mul (a : R) : (mul R R a).det = a := by
  classical
  rw [det_eq_det_toMatrix_of_finset (s := {1}) ⟨(Finsupp.LinearEquiv.finsuppUnique R R _).symm⟩,
    Matrix.det_unique]
  change a * _ = a
  simp
