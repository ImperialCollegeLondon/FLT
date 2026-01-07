import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Hom

open TensorProduct in
def AlgHom.rTensor {R : Type*} [CommSemiring R] (M : Type*) {N : Type*}
    {P : Type*} [AddCommMonoid M] [Semiring N] [Semiring P] [Module R M]
    [Algebra R N] [Algebra R P] (f : N →ₐ[R] P) :
  N ⊗[R] M →ₛₗ[f.toRingHom] P ⊗[R] M := {
    __ := LinearMap.rTensor M f
    map_smul' n x := by
      induction x with
      | zero => simp
      | tmul x y =>
        rw [smul_tmul']
        change (LinearMap.rTensor M f.toLinearMap) _ = _
        rw [LinearMap.rTensor_tmul]
        rw [smul_eq_mul]
        change f (n * x) ⊗ₜ[R] y = _
        rw [map_mul]
        rfl
      | add x y _ _ => simp_all
  }
