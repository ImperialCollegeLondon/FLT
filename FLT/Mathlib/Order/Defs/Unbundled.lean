import Mathlib.Order.Defs.Unbundled
import Mathlib.Order.CompletePartialOrder

variable {ι : Type*} [instPreorder : Preorder ι]

variable [instDedidabeRel : DecidableRel LE.le (α := ι)] [instIsLinearOrder : IsLinearOrder ι LE.le]

instance : LinearOrder ι where
  le := LE.le
  le_refl := instIsLinearOrder.refl
  le_trans := instIsLinearOrder.trans
  le_antisymm := instIsLinearOrder.antisymm
  le_total := instIsLinearOrder.total
  toDecidableLE := instDedidabeRel
  lt_iff_le_not_le := instPreorder.lt_iff_le_not_le
