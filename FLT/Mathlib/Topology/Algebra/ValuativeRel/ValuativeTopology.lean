/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
module

public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# Valuative topologies

Material destined for Mathlib.
-/

@[expose] public section

open ValuativeRel

variable {K : Type*} [DivisionRing K] [ValuativeRel K] [TopologicalSpace K]
  [IsValuativeTopology K]

/-- A division ring with a valuative topology is Hausdorff: `{y : |y| < |x|}` is a
neighbourhood of `0` not containing `x`. (Mathlib has this for `Valued` fields,
`ValuedRing.separated`, but not for `IsValuativeTopology`.) -/
instance : T2Space K := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  refine ⟨{y | valuation K y < valuation K x}, ?_,
    fun h ↦ lt_irrefl _ (show valuation K x < valuation K x from h)⟩
  rw [IsValuativeTopology.mem_nhds_zero_iff]
  exact ⟨Units.mk0 (valuation K x) ((valuation K).ne_zero_iff.mpr hx), fun y hy ↦ hy⟩
