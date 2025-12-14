import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar

open MeasureTheory Measure in
@[to_additive]
lemma MeasureTheory.mulEquivHaarChar_symm {G : Type*} [Group G]
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] {φ : G ≃ₜ* G} :
    mulEquivHaarChar φ.symm = (mulEquivHaarChar φ)⁻¹ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  simp [← mulEquivHaarChar_trans]
