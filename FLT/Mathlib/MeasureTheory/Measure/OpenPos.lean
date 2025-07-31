import Mathlib.MeasureTheory.Measure.OpenPos

section IsOpenEmbeddingComap

open MeasureTheory Measure

lemma Topology.IsOpenEmbedding.IsOpenPosMeasure_comap {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {φ : X → Y} (hφ : IsOpenEmbedding φ) (μ : Measure Y) [IsOpenPosMeasure μ] :
    IsOpenPosMeasure (comap φ μ) where
  open_pos U hU Une := by
    rw [MeasurableEmbedding.comap_apply hφ.measurableEmbedding]
    exact IsOpenPosMeasure.open_pos _ (hφ.isOpen_iff_image_isOpen.mp hU) (Une.image φ)

end IsOpenEmbeddingComap
