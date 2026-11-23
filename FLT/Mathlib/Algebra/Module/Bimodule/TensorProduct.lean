/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Mathlib.Algebra.Module.Bimodule.Defs
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor products as bimodules

For `R` a commutative semiring, `M` an `R`-module and `B` an `R`-algebra, this file makes
`M ⊗[R] B` a right `B`-module via `id_M ⊗ (· * b)`, that is
`(m ⊗ₜ c) <• b = m ⊗ₜ (c * b)`, and shows that any compatible left action on `M` then
makes `M ⊗[R] B` a bimodule.

This is the bimodule-world answer to the question underlying mathlib PR #39699
(`Algebra.TensorProduct.rightAlgebra`): the natural `B`-action on `M ⊗[R] B` is
`LinearMap.lTensor M (LinearMap.mulRight R b)`, which involves no `TensorProduct.comm`
(so no commutativity of `R` is being consumed in an essential way, and no swap to
`B ⊗[R] M`), and no `MulOpposite`. Right multiplication by `b` is left-`R`-linear
precisely because `B` is an `(R, B)`-bimodule — the same observation that makes
`rightAlgebra`'s `smul` work. Unlike `rightAlgebra`, which must be a `def` because
`Algebra B (A ⊗[R] B)` clashes with `Algebra A (A ⊗[R] B)` at `A = B`, the right-module
structure here can be a global *instance*: `RightModule B (M ⊗[R] B)` does not compete
with any left `Module` instance, because the two classes are unrelated by design.
-/

@[expose] public section

open scoped TensorProduct Bimodule

open LinearMap (lTensor mulRight)

namespace TensorProduct

variable {R M B : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [Semiring B] [Algebra R B]

/-- `M ⊗[R] B` is a right `B`-module, via `id_M ⊗ (· * b)`:
`(m ⊗ₜ c) <• b = m ⊗ₜ (c * b)`. -/
noncomputable instance rightModule : RightModule B (M ⊗[R] B) where
  rsmul x b := lTensor M (mulRight R b) x
  rsmul_one x := by rw [LinearMap.mulRight_one, LinearMap.lTensor_id, LinearMap.id_apply]
  rsmul_mul x b c := by rw [LinearMap.mulRight_mul, LinearMap.lTensor_comp, LinearMap.comp_apply]
  add_rsmul x y b := map_add _ x y
  rsmul_add x b c := by
    have : mulRight R (b + c) = mulRight R b + mulRight R c := by
      ext x
      simp [mul_add]
    rw [this, LinearMap.lTensor_add, LinearMap.add_apply]
  zero_rsmul b := map_zero _
  rsmul_zero x := by
    have : mulRight R (0 : B) = 0 := by
      ext x
      simp
    rw [this, LinearMap.lTensor_zero, LinearMap.zero_apply]

@[simp]
theorem rsmul_tmul (m : M) (c b : B) : (m ⊗ₜ[R] c) <• b = m ⊗ₜ (c * b) :=
  rfl

/-- Any left action on `M` commuting with the `R`-action makes `M ⊗[R] B` an
`(A, B)`-bimodule, for the left `A`-action through the `M` factor
(`TensorProduct.leftModule`) and the right `B`-action through the `B` factor. The two
sides act on different factors, so they commute with no hypotheses relating `A` and
`B`. -/
instance instBimodule {A : Type*} [Semiring A] [Module A M] [SMulCommClass R A M] :
    Bimodule A (M ⊗[R] B) B where
  smul_rsmul a x b := by
    induction x with
    | zero => simp
    | tmul m c => simp [smul_tmul']
    | add x y hx hy =>
      simp only [smul_add, add_rsmul] at *
      rw [hx, hy]

/-- The `#39699` special case: for `A` an `R`-algebra, `A ⊗[R] B` is an
`(A, B)`-bimodule — `A` acting through the left factor via `Algebra A (A ⊗[R] B)`, `B`
acting through the right factor. No commutation, no `MulOpposite`, no diamond at
`A = B`. -/
example {A : Type*} [Semiring A] [Algebra R A] : Bimodule A (A ⊗[R] B) B :=
  inferInstance

/-- The left `R`-structure and right `B`-structure make `M ⊗[R] B` an
`(R, B)`-bimodule. -/
example : Bimodule R (M ⊗[R] B) B :=
  inferInstance

end TensorProduct
