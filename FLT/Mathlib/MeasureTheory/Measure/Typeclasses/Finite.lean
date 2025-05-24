import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

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
