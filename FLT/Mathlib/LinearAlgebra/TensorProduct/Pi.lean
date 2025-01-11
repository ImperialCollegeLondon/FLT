import Mathlib.LinearAlgebra.TensorProduct.Pi

theorem TensorProduct.piScalarRight_symm_apply (R S N ι : Type*) [CommSemiring R]
    [CommSemiring S] [Algebra R S] [AddCommMonoid N] [Module R N] [Module S N]
    [IsScalarTower R S N] [Fintype ι] [DecidableEq ι] (x : ι → N) :
    (TensorProduct.piScalarRight R S N ι).symm x = (LinearMap.lsum S (fun _ => N) S (fun i => {
      toFun := fun n => n ⊗ₜ[R] Pi.single i (1 : R)
      map_add' := fun _ _ => by simp [add_tmul]
      map_smul' := fun _ _ => rfl
    }) x) := rfl
