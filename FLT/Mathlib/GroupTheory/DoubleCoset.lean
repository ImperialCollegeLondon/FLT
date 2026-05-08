/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram, Kevin Buzzard
-/
module

public import Mathlib.GroupTheory.DoubleCoset
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Constructions
import FLT.Mathlib.Topology.Algebra.Group.Quotient

/-!
# Double Coset

Material destined for Mathlib.
-/

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
