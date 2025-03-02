import Mathlib.GroupTheory.QuotientGroup.Basic

@[to_additive]
def QuotientGroup.mulEquiv {G H : Type*} [Group G] (N : Subgroup G)
    [N.Normal] [Group H] (M : Subgroup H) [M.Normal] (e : G ≃* H)
    (h : N = Subgroup.comap e M) :
    G ⧸ N ≃* H ⧸ M where
  __ := QuotientGroup.map N M e (le_of_eq h)
  invFun := QuotientGroup.map M N e.symm (by simp [h, Subgroup.comap_comap])
  left_inv := fun x => induction_on x (by simp)
  right_inv := fun x => induction_on x (by simp)
