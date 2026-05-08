/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Quotient

Material destined for Mathlib.
-/

@[expose] public section

/-- A continuous group isomorphism `e : G ≃ₜ* H` mapping `N ≤ G` onto `M ≤ H` descends
to a continuous group isomorphism `G ⧸ N ≃ₜ* H ⧸ M`. -/
@[to_additive /-- A continuous additive group isomorphism `e : G ≃ₜ+ H` mapping `N ≤ G`
onto `M ≤ H` descends to a continuous additive group isomorphism `G ⧸ N ≃ₜ+ H ⧸ M`. -/]
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
