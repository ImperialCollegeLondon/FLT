import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib

namespace Subgroup

variable {α : Type*} [Group α]

lemma quotientMapOfLE_mul {s t : Subgroup α} [s.Normal] [t.Normal]
    (h : s ≤ t) (x y : α ⧸ s) :
    quotientMapOfLE h (x * y) = quotientMapOfLE h x * quotientMapOfLE h y :=
  sorry

end Subgroup
