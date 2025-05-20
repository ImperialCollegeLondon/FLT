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

lemma comap_smul {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {f : X → Y} {c : ℝ≥0}
    {μ : Measure Y} : comap f (c • μ) = c • comap f μ := by
  obtain rfl | hc := eq_zero_or_pos c; · simp
  by_cases h : Function.Injective f ∧ ∀ (s : Set X), MeasurableSet s → NullMeasurableSet (f '' s) μ
  · ext s hs
    rw [comap_apply₀ f _ h.1 _ hs.nullMeasurableSet, smul_apply, smul_apply,
      comap_apply₀ f μ h.1 h.2 hs.nullMeasurableSet]
    simpa [nullMeasurableSet_smul_iff_nullMeasurableSet hc] using h.2
  · have h' : ¬ (Function.Injective f ∧
        ∀ (s : Set X), MeasurableSet s → NullMeasurableSet (f '' s) (c • μ)) := by
      simpa [nullMeasurableSet_smul_iff_nullMeasurableSet hc] using h
    simp [comap, dif_neg h, dif_neg h']

end MeasureTheory.Measure
