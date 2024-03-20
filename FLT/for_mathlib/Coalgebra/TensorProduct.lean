/-
Copyright (c) 2024 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Yanqiao Zhou, Jujian Zhang
-/

import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Bialgebra
import FLT.for_mathlib.Coalgebra.Sweedler

/-!

# Tensor Product of Coalgebras

Suppose `A, B` are `R`-coalgebras. Then `A ⊗[R] B` has a natural `R`-coalgebra structure.

If furthermore `A` and `B` are `R`-bialgebras, then `A ⊗[R] B` has a natural
`R`-bialgebra structure.

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

lemma TensorProduct.comul_def :
    Coalgebra.comul (R := R) (A := A ⊗[R] B) =
    tensorTensorTensorComm R A A B B ∘ₗ map comul comul :=
  rfl

lemma TensorProduct.counit_def :
    Coalgebra.counit (R := R) (A := A ⊗[R] B) = TensorProduct.lid R R ∘ₗ map counit counit :=
  rfl

variable {R A B}

lemma TensorProduct.comul_apply_repr (a : A) (b : B) {ιA ιB : Type*}
    (sA : Finset ιA) (sB : Finset ιB)
    (xA yA : ιA → A) (repr_a : comul a = ∑ i in sA, xA i ⊗ₜ[R] yA i)
    (xB yB : ιB → B) (repr_b : comul b = ∑ i in sB, xB i ⊗ₜ[R] yB i) :
    comul (a ⊗ₜ[R] b) = ∑ i in sA, ∑ j in sB, (xA i ⊗ₜ xB j) ⊗ₜ[R] (yA i ⊗ₜ yB j) := by
  simpa [TensorProduct.comul_def, repr_a, repr_b, map_sum, sum_tmul, tmul_sum] using Finset.sum_comm

lemma TensorProduct.comul_apply_repr' (a : A) (b : B) {ιA ιB : Type*}
    (sA : Finset ιA) (sB : Finset ιB)
    (xA yA : ιA → A) (repr_a : comul a = ∑ i in sA, xA i ⊗ₜ[R] yA i)
    (xB yB : ιB → B) (repr_b : comul b = ∑ i in sB, xB i ⊗ₜ[R] yB i) :
    comul (a ⊗ₜ[R] b) = ∑ j in sB, ∑ i in sA, (xA i ⊗ₜ xB j) ⊗ₜ[R] (yA i ⊗ₜ yB j) := by
  simp [TensorProduct.comul_def, repr_a, repr_b, map_sum, sum_tmul, tmul_sum]

lemma TensorProduct.comul_apply_repr'' (a : A) (b : B) {ιA ιB : Type*}
    (sA : Finset ιA) (sB : Finset ιB)
    (xA yA : ιA → A) (repr_a : comul a = ∑ i in sA, xA i ⊗ₜ[R] yA i)
    (xB yB : ιB → B) (repr_b : comul b = ∑ i in sB, xB i ⊗ₜ[R] yB i) :
    comul (a ⊗ₜ[R] b) = ∑ i in sA ×ˢ sB, (xA i.1 ⊗ₜ xB i.2) ⊗ₜ[R] (yA i.1 ⊗ₜ yB i.2) := by
  rw [TensorProduct.comul_apply_repr (repr_a := repr_a) (repr_b := repr_b), Finset.sum_product]

end Coalgebra

namespace Bialgebra

variable (R A B : Type*) [CommSemiring R]
variable [Semiring A] [Bialgebra R A]
variable [Semiring B] [Bialgebra R B]

noncomputable instance : Bialgebra R (A ⊗[R] B) where
  counit_one := by simp [show (1 : A ⊗[R] B) = 1 ⊗ₜ 1 from rfl, Coalgebra.TensorProduct.counit_def]
  mul_compr₂_counit := by
    ext
    simp only [Coalgebra.TensorProduct.counit_def, AlgebraTensorModule.curry_apply, curry_apply,
      LinearMap.coe_restrictScalars, LinearMap.compr₂_apply, LinearMap.mul_apply',
      Algebra.TensorProduct.tmul_mul_tmul, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, map_tmul, counit_mul, lid_tmul, smul_eq_mul, LinearMap.compl₁₂_apply]
    ring
  comul_one := by
    rw [show (1 : A ⊗[R] B) = 1 ⊗ₜ 1 from rfl, Coalgebra.TensorProduct.comul_def,
      LinearMap.comp_apply, map_tmul, comul_one, comul_one]
    rfl
  mul_compr₂_comul := by
    let e : (A →ₗ[R] A ⊗[R] A) ⊗[R] (B →ₗ[R] B ⊗[R] B) →ₗ[R]
      A ⊗[R] B →ₗ[R] (A ⊗[R] B) ⊗[R] A ⊗[R] B :=
    (tensorTensorTensorComm R A A B B).toLinearMap.compRight ∘ₗ homTensorHomMap _ _ _ _ _

    convert congr_arg e.comp
      congr(map $(mul_compr₂_comul (R := R) (A := A)) $(mul_compr₂_comul (R := R) (A := B)))
    · ext a b a' b'
      simpa only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
        LinearMap.compr₂_apply, LinearMap.mul_apply', Algebra.TensorProduct.tmul_mul_tmul,
        LinearMap.coe_comp, Function.comp_apply, map_tmul, homTensorHomMap_apply,
        LinearMap.compRight_apply, LinearEquiv.coe_coe, Coalgebra.comul_repr (a := a * a'),
        Coalgebra.comul_repr (a := b * b'), tmul_sum, sum_tmul, map_sum,
        tensorTensorTensorComm_tmul, e] using Coalgebra.TensorProduct.comul_apply_repr'
        (repr_a := Coalgebra.comul_repr _) (repr_b := Coalgebra.comul_repr _)

    · ext a b a' b'
      simpa only [Coalgebra.TensorProduct.comul_def, AlgebraTensorModule.curry_apply, curry_apply,
        LinearMap.coe_restrictScalars, LinearMap.compl₁₂_apply, LinearMap.coe_comp,
        LinearEquiv.coe_coe, Function.comp_apply, map_tmul, Coalgebra.comul_repr, tmul_sum,
        sum_tmul, map_sum, tensorTensorTensorComm_tmul, LinearMap.coeFn_sum, Finset.sum_apply,
        LinearMap.mul_apply', Algebra.TensorProduct.tmul_mul_tmul, homTensorHomMap_apply,
        LinearMap.compRight_apply, e] using Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

end Bialgebra
