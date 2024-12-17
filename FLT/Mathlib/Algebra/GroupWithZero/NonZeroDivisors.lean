import Mathlib.Algebra.GroupWithZero.NonZeroDivisors

open scoped nonZeroDivisors

variable {G₀ : Type*} [GroupWithZero G₀]

attribute [simp] mem_nonZeroDivisors_iff_ne_zero

@[simps]
noncomputable def nonZeroDivisorsEquivUnits : G₀⁰ ≃* G₀ˣ where
  toFun u := .mk0 _ <| mem_nonZeroDivisors_iff_ne_zero.1 u.2
  invFun u := ⟨u, u.isUnit.mem_nonZeroDivisors⟩
  left_inv u := rfl
  right_inv u := by simp
  map_mul' u v := by simp
