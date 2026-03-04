import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.Algebra.Hom

open TensorProduct
/--
The base extension of an R-algebra homomorphism `f : N → P` to an  `f`-semilinear
map `N ⊗[R] M → P ⊗[R] M`.
-/
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

lemma AlgHom.rTensor_map_smul {R : Type*} [CommSemiring R] (M : Type*) {N : Type*}
    {P : Type*} [AddCommMonoid M] [Semiring N] [Semiring P] [Module R M]
    [Algebra R N] [Algebra R P] (f : N →ₐ[R] P) (n : N) (nm : N ⊗[R] M) :
    AlgHom.rTensor M f (n • nm) = f n • AlgHom.rTensor M f nm :=
  MulActionHom.map_smul' (AlgHom.rTensor M f).toMulActionHom n nm
