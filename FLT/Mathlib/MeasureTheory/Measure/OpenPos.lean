import Mathlib.MeasureTheory.Measure.OpenPos


section IsOpenEmbeddingComap

open MeasureTheory Measure

lemma Topology.IsOpenEmbedding.IsOpenPosMeasure_comap {G H : Type*}
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    {φ : G → H} (hφ : IsOpenEmbedding φ) (μ : Measure H) [IsOpenPosMeasure μ] :
    IsOpenPosMeasure (comap φ μ) where
  open_pos := by
    intro U hU Une
    rw [MeasurableEmbedding.comap_apply hφ.measurableEmbedding]
    exact IsOpenPosMeasure.open_pos _ (hφ.isOpen_iff_image_isOpen.mp hU) (Une.image φ)

end IsOpenEmbeddingComap
