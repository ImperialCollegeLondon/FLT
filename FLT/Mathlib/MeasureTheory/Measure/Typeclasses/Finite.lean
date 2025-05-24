import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

section IsOpenEmbeddingComap

open MeasureTheory Measure

lemma Topology.IsOpenEmbedding.isFiniteMeasureOnCompacts_comap {G H : Type*}
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    {φ : G → H} (hφ : IsOpenEmbedding φ) (μ : Measure H) [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts (comap φ μ) where
  lt_top_of_isCompact K hK := by
    rw [MeasurableEmbedding.comap_apply hφ.measurableEmbedding]
    exact IsFiniteMeasureOnCompacts.lt_top_of_isCompact (hK.image hφ.continuous)

end IsOpenEmbeddingComap
