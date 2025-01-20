import Mathlib.RingTheory.TensorProduct.Pi

theorem Algebra.TensorProduct.piScalarRight_symm_apply_of_algebraMap (R S N ι : Type*)
    [CommSemiring R] [CommSemiring S] [Algebra R S] [Semiring N] [Algebra R N] [Algebra S N]
    [IsScalarTower R S N] [Fintype ι] [DecidableEq ι] (x : ι → R) :
    (TensorProduct.piScalarRight R S N ι).symm (fun i => algebraMap _ _ (x i)) =
      1 ⊗ₜ[R] (∑ i, Pi.single i (x i)) := by
  simp [LinearEquiv.symm_apply_eq, algebraMap_eq_smul_one]
