-- thanks to Remy Degenne for the golf
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

open scoped NNReal ENNReal

namespace MeasureTheory.Measure

lemma nullMeasurableSet_smul_of_nullMeasurableSet {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (c : ℝ≥0) {s : Set X} (h : NullMeasurableSet s μ) :
    NullMeasurableSet s (c • μ) :=
  NullMeasurableSet.mono_ac h (AbsolutelyContinuous.rfl.smul_left c)

lemma nullMeasurableSet_smul_iff_nullMeasurableSet {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {c : ℝ≥0} (hc : 0 < c) {s : Set X} :
    NullMeasurableSet s (c • μ) ↔ NullMeasurableSet s μ := by
  refine ⟨?_, nullMeasurableSet_smul_of_nullMeasurableSet c⟩
  intro h
  apply nullMeasurableSet_smul_of_nullMeasurableSet c⁻¹ at h
  rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h

end MeasureTheory.Measure
