/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Yanqiao Zhou, Jujian Zhang
-/

import Mathlib.RingTheory.TensorProduct
-- import Mathlib.RingTheory.Bialgebra
import FLT.for_mathlib.Coalgebra.Sweedler

/-!
# Tensor Product of Coalgebras

Suppose `A, B` are `R`-coalgebras, then `A ⊗ B` has a natural `R`-coalgebra strucutre
induced by those of `A` and `B`.

-/

open TensorProduct BigOperators

namespace Coalgebra

variable (R A B : Type*) [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
variable [AddCommMonoid B] [Module R B] [Coalgebra R B]

set_option maxHeartbeats 500000 in
noncomputable instance : Coalgebra R (A ⊗[R] B) :=
let e : (A ⊗[R] B) ⊗[R] (A ⊗[R] B) ⊗[R] A ⊗[R] B ≃ₗ[R] (A ⊗[R] A ⊗[R] A) ⊗[R] B ⊗[R] B ⊗[R] B :=
  congr (.refl R _) (tensorTensorTensorComm R _ _ _ _) ≪≫ₗ tensorTensorTensorComm R _ _ _ _
{ comul := tensorTensorTensorComm R A A B B ∘ₗ map comul comul
  counit := TensorProduct.lid R R ∘ₗ map counit counit
  coassoc := by
    convert congr_arg e.symm.toLinearMap.comp
      congr(TensorProduct.map $(coassoc (R := R) (A := A)) $(coassoc (R := R) (A := B))) <;>
    ext <;>
    simpa [comul_repr, tmul_sum, sum_tmul, map_sum] using
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
  rTensor_counit_comp_comul := by
    have EQ := congr_arg ((TensorProduct.assoc R R A B).toLinearMap ∘ₗ
      ((TensorProduct.lid R B).toLinearMap.lTensor _)).comp
        congr(TensorProduct.map
          $(rTensor_counit_comp_comul (R := R) (A := A))
          $(rTensor_counit_comp_comul (R := R) (A := B)))
    convert EQ <;>
    ext <;>
    simp [comul_repr, tmul_sum, sum_tmul, map_sum, tmul_smul, Finset.smul_sum, smul_tmul', mul_comm]
  lTensor_counit_comp_comul := by
    have EQ :=
      congr_arg ((TensorProduct.assoc R A B R).symm.toLinearMap ∘ₗ
        (TensorProduct.rid R A).toLinearMap.rTensor _).comp
        congr(TensorProduct.map
          $(lTensor_counit_comp_comul (R := R) (A := A))
          $(lTensor_counit_comp_comul (R := R) (A := B)))
    convert EQ <;>
    ext <;>
    simp [comul_repr, tmul_sum, sum_tmul, map_sum, Finset.smul_sum, smul_tmul', smul_tmul,
      mul_comm] }

end Coalgebra
