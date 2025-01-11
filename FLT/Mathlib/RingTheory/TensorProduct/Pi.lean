import Mathlib.RingTheory.TensorProduct.Pi
import FLT.Mathlib.LinearAlgebra.TensorProduct.Pi

theorem Algebra.TensorProduct.piScalarRight_symm_apply_of_algebraMap (R S N ι : Type*)
    [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring N] [Algebra R N] [Algebra S N]
    [IsScalarTower R S N] [Fintype ι] [DecidableEq ι] (x : ι → R) :
    (TensorProduct.piScalarRight R S N ι).symm (fun i => algebraMap _ _ (x i)) =
      1 ⊗ₜ[R] (∑ i, Pi.single i (x i)) := by
  simp only [_root_.TensorProduct.piScalarRight_symm_apply, LinearMap.lsum_apply,
    LinearMap.coeFn_sum, LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.coe_proj,
    Finset.sum_apply, Function.comp_apply, Function.eval, Algebra.algebraMap_eq_smul_one,
    TensorProduct.smul_tmul, ← TensorProduct.tmul_sum, ← Pi.single_smul, smul_eq_mul, mul_one]
