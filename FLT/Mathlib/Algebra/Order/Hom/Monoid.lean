import Mathlib.Algebra.Order.Hom.Monoid

/-!
This is https://github.com/leanprover-community/mathlib4/pull/18986
-/

namespace OrderMonoidIso
variable {α β : Type*} [OrderedCommMonoid α] [OrderedCommMonoid β]

def symm (e : α ≃*o β) : β ≃*o α where
  toMulEquiv := e.toMulEquiv.symm
  map_le_map_iff' := e.toOrderIso.symm.map_rel_iff

end OrderMonoidIso

/-- Any ordered group is isomorphic to the units of itself adjoined with `0`. -/
@[simps! toFun]
def OrderMonoidIso.unitsWithZero {α : Type*} [Group α] [Preorder α] : (WithZero α)ˣ ≃*o α where
  toMulEquiv := WithZero.unitsWithZeroEquiv
  map_le_map_iff' {a b} := by simp [WithZero.unitsWithZeroEquiv]; sorry
