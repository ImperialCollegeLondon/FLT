import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Algebra.Module.End

open scoped Pointwise

namespace AddSubgroup
variable {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]

@[simp] protected lemma smul_zero (s : AddSubgroup M) : (0 : R) • s = ⊥ :=
  show s.map (Module.toAddMonoidEnd _ _ 0) = ⊥ by simp

end AddSubgroup
