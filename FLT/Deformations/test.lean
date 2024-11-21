import Mathlib

open TensorProduct

universe u

variable (A : Type u) [CommRing A]
variable (W : Type u) [AddCommGroup W] [Module A W]

noncomputable def extend_ctts : W →+ (W ⊗[A] A) where
  toFun w := w ⊗ₜ (1 : A)
  map_zero' := by simp
  map_add' := by
    simp [TensorProduct.add_tmul]
