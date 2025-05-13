import Mathlib.MeasureTheory.Measure.Haar.DistribChar

open MeasureTheory.Measure
open scoped NNReal Pointwise ENNReal

namespace MeasureTheory

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [LocallyCompactSpace A] [ContinuousConstSMul G A] {g : G}

variable [MeasurableSpace A] [BorelSpace A]

variable (μ : Measure A) [IsAddHaarMeasure μ]

variable (f : A → ℝ) (hf : Measurable f)

example : (distribHaarChar A g) * ∫ (a : A), f a ∂(comap (g • .) μ) = ∫ a, f a ∂μ := sorry
