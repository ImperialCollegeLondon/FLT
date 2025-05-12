import Mathlib.Algebra.Module.Equiv.Defs

variable {R : Type*} [Semiring R] (M : Type*) [AddCommMonoid M] [Module R M]

def LinearEquiv.id : LinearEquiv (.id R) M M where
  toFun m := m
  map_add' := by simp
  map_smul' := by simp
  invFun m := m
  left_inv := by
    unfold Function.LeftInverse
    simp
  right_inv := by
    unfold Function.RightInverse
    unfold Function.LeftInverse
    simp

variable {M₁ : Type*} [AddCommMonoid M₁] [Module R M₁]
variable {M₂ : Type*} [AddCommMonoid M₂] [Module R M₂]
variable {M₃ : Type*} [AddCommMonoid M₃] [Module R M₃]

def LinearEquiv.comp' (φ₁ : LinearEquiv (.id R) M₁ M₂) (φ₂ : LinearEquiv (.id R) M₂ M₃) :
  LinearEquiv (.id R) M₁ M₃ where
    toFun m₁ := φ₂ (φ₁ m₁)
    map_add' := sorry
    map_smul' := sorry
    invFun m₃ := φ₁.symm (φ₂.symm m₃)
    left_inv := sorry
    right_inv := sorry
