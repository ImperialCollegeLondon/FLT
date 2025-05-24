import Mathlib.MeasureTheory.Measure.Regular
import FLT.Mathlib.MeasureTheory.Measure.Typeclasses.Finite

section IsOpenEmbeddingComap

open MeasureTheory Measure

variable {X Y : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    {φ : X → Y}

namespace Topology.IsOpenEmbedding

lemma outerRegular_comap
    (hφ : IsOpenEmbedding φ) (μ : Measure Y) [OuterRegular μ] :
    OuterRegular (comap φ μ) where
  outerRegular A hA r hr := by
    rw [MeasurableEmbedding.comap_apply hφ.measurableEmbedding] at hr
    obtain ⟨U, hUA, Uopen, hμU⟩ :=
      OuterRegular.outerRegular (hφ.measurableEmbedding.measurableSet_image' hA) r hr
    use φ ⁻¹' U
    refine ⟨by rwa [Superset, ← Set.image_subset_iff], Uopen.preimage hφ.continuous, ?_⟩
    rw [MeasurableEmbedding.comap_apply hφ.measurableEmbedding]
    apply lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) hμU

lemma innerRegularWRT_comap
    (hφ : IsOpenEmbedding φ) {μ : Measure Y} (hμ : InnerRegularWRT μ IsCompact IsOpen) :
    InnerRegularWRT (comap φ μ) IsCompact IsOpen := by
  intro A hA r hr
  rw [MeasurableEmbedding.comap_apply hφ.measurableEmbedding] at hr
  obtain ⟨K, hKA, Kcompact, hμK⟩ := hμ (hφ.isOpen_iff_image_isOpen.mp hA) r hr
  have hK := subset_trans hKA (Set.image_subset_range _ _)
  use φ ⁻¹' K
  refine ⟨?_, hφ.isInducing.isCompact_preimage' Kcompact hK, ?_⟩
  · rw [← hφ.injective.preimage_image A]; exact Set.preimage_mono hKA
  · rwa [MeasurableEmbedding.comap_apply hφ.measurableEmbedding,
      Set.image_preimage_eq_iff.mpr hK]


lemma regular_comap
    (φ : X → Y) (hφ : IsOpenEmbedding φ) (μ : Measure Y) [Regular μ] :
    Regular (comap φ μ) where
  lt_top_of_isCompact := (hφ.isFiniteMeasureOnCompacts_comap μ).lt_top_of_isCompact
  outerRegular := (hφ.outerRegular_comap μ).outerRegular
  innerRegular := hφ.innerRegularWRT_comap Regular.innerRegular

end Topology.IsOpenEmbedding

end IsOpenEmbeddingComap
