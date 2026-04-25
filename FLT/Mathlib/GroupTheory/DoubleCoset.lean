module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Topology.Algebra.Group.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Actions
public import FLT.Mathlib.Topology.Algebra.Group.Quotient

@[expose] public section

theorem DoubleCoset.isOpen_doubleCoset {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (H K : Subgroup G) (hK : IsOpen (K : Set G)) (i : DoubleCoset.Quotient H K) :
    IsOpen (X := G) (doubleCoset (Quotient.out i) H K) := by
  simpa only [doubleCoset] using (IsOpen.mul_left hK)

theorem DoubleCoset.isOpen_doubleCoset_rightrel_mk {G : Type*} [Group G] [TopologicalSpace G]
    [ContinuousMul G] (H K : Subgroup G) (hK : IsOpen (K : Set G)) (i : DoubleCoset.Quotient H K) :
    IsOpen (Quot.mk ⇑(QuotientGroup.rightRel H) '' doubleCoset (Quotient.out i) H K) := by
  apply (QuotientGroup.isOpenQuotientMap_rightrel_mk H).isOpenMap
  exact DoubleCoset.isOpen_doubleCoset H K hK i
