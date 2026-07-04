/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Algebra.Group.Basic

/-! # Lemmas about topological groups -/

public section

@[to_additive]
lemma continuous_iff_continuousAt_one
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M : Type*} {hom : Type*} [MulOneClass M]
    [TopologicalSpace M] [ContinuousMul M] [FunLike hom G M]
    [MonoidHomClass hom G M] {f : hom} : Continuous ⇑f ↔ ContinuousAt (⇑f) 1 :=
  ⟨Continuous.continuousAt, continuous_of_continuousAt_one _⟩

@[to_additive]
lemma MonoidHom.continuous_of_isOpen_ker {G H : Type*} [Group G] [MulOneClass H] {φ : G →* H}
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [ContinuousMul H]
    (hφ : IsOpen (φ.ker : Set G)) : Continuous φ := by
  refine continuous_of_continuousAt_one _ ?_
  intro U hU
  simp only [Filter.mem_map]
  exact Filter.mem_of_superset (hφ.mem_nhds (by simp)) (Set.preimage_mono
    (Set.singleton_subset_iff.mpr (mem_of_mem_nhds (by simpa using hU))))

@[to_additive]
lemma MonoidHom.continuous_iff_isOpen_ker {G H : Type*} [Group G] [MulOneClass H] {φ : G →* H}
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H] [DiscreteTopology H] :
    Continuous φ ↔ IsOpen (φ.ker : Set G) :=
  ⟨fun h ↦ (isOpen_discrete {1}).preimage h, MonoidHom.continuous_of_isOpen_ker⟩
