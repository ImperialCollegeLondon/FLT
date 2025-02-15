import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import FLT.Mathlib.GroupTheory.QuotientGroup.Basic

@[to_additive]
def QuotientGroup.continuousMulEquiv {G H : Type*} [Group G] (N : Subgroup G)
    [N.Normal] [Group H] (M : Subgroup H) [M.Normal] [TopologicalSpace G]
    [TopologicalSpace H] (e : G ≃ₜ* H)
    (h : N = Subgroup.comap e M) :
    G ⧸ N ≃ₜ* H ⧸ M where
  __ := QuotientGroup.mulEquiv N M e h
  continuous_toFun := by
    apply continuous_quot_lift
    simp only [MonoidHom.coe_comp, coe_mk', MonoidHom.coe_coe]
    exact Continuous.comp continuous_quot_mk e.continuous
  continuous_invFun := by
    apply continuous_quot_lift
    simp only [MonoidHom.coe_comp, coe_mk', MonoidHom.coe_coe]
    exact Continuous.comp continuous_quot_mk e.symm.continuous
