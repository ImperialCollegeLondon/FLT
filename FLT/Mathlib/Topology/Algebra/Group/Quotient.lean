import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[to_additive]
def QuotientGroup.continuousMulEquiv {G H : Type*} [Group G] (N : Subgroup G)
    [N.Normal] [Group H] (M : Subgroup H) [M.Normal] [TopologicalSpace G]
    [TopologicalSpace H] (e : G ≃ₜ* H)
    (h : Subgroup.map e N = M) :
    G ⧸ N ≃ₜ* H ⧸ M where
  __ := QuotientGroup.congr N M e h
  continuous_toFun := by
    apply continuous_quot_lift
    simp only [MonoidHom.coe_comp, coe_mk', MonoidHom.coe_coe]
    exact Continuous.comp continuous_quot_mk e.continuous
  continuous_invFun := by
    apply continuous_quot_lift
    simp only [MonoidHom.coe_comp, coe_mk', MonoidHom.coe_coe]
    exact Continuous.comp continuous_quot_mk e.symm.continuous

theorem QuotientGroup.isOpenQuotientMap_rightrel_mk {G : Type*} [Group G] [TopologicalSpace G]
  [ContinuousMul G] (H : Subgroup G) : IsOpenQuotientMap (Quot.mk ⇑(QuotientGroup.rightRel H))
  := {surjective := Quot.mk_surjective, continuous := continuous_quot_mk,
      isOpenMap := isOpenMap_quotient_mk'_mul}
