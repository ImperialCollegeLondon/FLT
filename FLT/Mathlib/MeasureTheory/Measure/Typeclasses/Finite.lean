/-
Copyright (c) 2025 David Ledvinka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Ledvinka
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Finite

Material destined for Mathlib.
-/

@[expose] public section

section IsOpenEmbeddingComap

open MeasureTheory Measure

lemma Topology.IsOpenEmbedding.isFiniteMeasureOnCompacts_comap {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {φ : X → Y} (hφ : IsOpenEmbedding φ) (μ : Measure Y) [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts (comap φ μ) where
  lt_top_of_isCompact K hK := by
    rw [MeasurableEmbedding.comap_apply hφ.measurableEmbedding]
    exact IsFiniteMeasureOnCompacts.lt_top_of_isCompact (hK.image hφ.continuous)

end IsOpenEmbeddingComap
