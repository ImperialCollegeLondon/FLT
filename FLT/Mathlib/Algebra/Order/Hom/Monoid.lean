import Mathlib.Algebra.Order.Hom.Monoid

namespace OrderMonoidIso
variable {α β : Type*} [OrderedCommMonoid α] [OrderedCommMonoid β]

def symm (e : α ≃*o β) : β ≃*o α where
  toMulEquiv := e.toMulEquiv.symm
  map_le_map_iff' := e.toOrderIso.symm.map_rel_iff

end OrderMonoidIso
