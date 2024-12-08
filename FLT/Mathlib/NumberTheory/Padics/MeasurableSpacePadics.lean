import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.NumberTheory.Padics.ProperSpace
import FLT.Mathlib.NumberTheory.Padics.PadicIntegers

open Topology TopologicalSpace MeasureTheory Measure
open scoped Pointwise

variable {p : ℕ} [Fact p.Prime]

instance : MeasurableSpace ℚ_[p] := borel _
instance : BorelSpace ℚ_[p] := ⟨rfl⟩

instance : MeasurableSpace ℤ_[p] := Subtype.instMeasurableSpace
instance : BorelSpace ℤ_[p] := Subtype.borelSpace _

lemma PadicInt.isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℤ_[p] → ℚ_[p]) := by
  refine IsOpen.isOpenEmbedding_subtypeVal (?_ : IsOpen {y : ℚ_[p] | ‖y‖ ≤ 1})
  simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
    IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero

lemma PadicInt.isMeasurableEmbedding_coe : MeasurableEmbedding ((↑) : ℤ_[p] → ℚ_[p]) := by
  convert PadicInt.isOpenEmbedding_coe.measurableEmbedding
  exact inferInstanceAs (BorelSpace ℤ_[p])

noncomputable instance : MeasureSpace ℤ_[p] := ⟨addHaarMeasure ⊤⟩

instance : IsAddHaarMeasure (volume : Measure ℤ_[p]) := isAddHaarMeasure_addHaarMeasure _

lemma PadicInt.volume_univ : volume (Set.univ : Set ℤ_[p]) = 1 := addHaarMeasure_self

-- should we more generally make a map from `CompactOpens` to `PositiveCompacts`?
private def Padic.unitBall_positiveCompact : PositiveCompacts ℚ_[p] where
  carrier := {y | ‖y‖ ≤ 1}
  isCompact' := by simpa only [Metric.closedBall, dist_zero_right] using
    isCompact_closedBall (0 : ℚ_[p]) 1
  interior_nonempty' := by
    rw [IsOpen.interior_eq]
    · exact ⟨0, by simp⟩
    · simpa only [Metric.closedBall, dist_zero_right] using
        IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero

noncomputable instance : MeasureSpace ℚ_[p] := ⟨addHaarMeasure Padic.unitBall_positiveCompact⟩

instance : IsAddHaarMeasure (volume : Measure ℚ_[p]) := isAddHaarMeasure_addHaarMeasure _

lemma Padic.volume_closedBall : volume {x : ℚ_[p] | ‖x‖ ≤ 1} = 1 := addHaarMeasure_self

lemma PadicInt.volume_smul (x : nonZeroDivisors ℤ_[p]) :
    volume (x • ⊤ : Set ℤ_[p]) = ‖x.1‖₊⁻¹ := sorry

lemma Padic.volume_smul (x : ℚ_[p]ˣ) : volume (x • {y : ℚ_[p] | ‖y‖ ≤ 1}) = ‖(x:ℚ_[p])‖₊⁻¹ :=
  sorry
