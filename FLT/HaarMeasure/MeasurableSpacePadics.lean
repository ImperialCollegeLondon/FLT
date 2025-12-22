/-
Copyright (c) 2024 Yaël Dillies, David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, David Loeffler
-/
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.Padics.ProperSpace
import FLT.Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Measurability and measures on the p-adics

This file endows `ℤ_[p]` and `ℚ_[p]` with their Borel sigma-algebra and their Haar measure that
makes `ℤ_[p]` (or the copy of `ℤ_[p]` inside `ℚ_[p]`) have norm `1`.
-/

open MeasureTheory Measure TopologicalSpace Topology

variable {p : ℕ} [Fact p.Prime]

namespace Padic

instance instMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
instance instBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

-- Should we more generally make a map from `CompactOpens` to `PositiveCompacts`?
private def unitBall_positiveCompact : PositiveCompacts ℚ_[p] where
  carrier := {y | ‖y‖ ≤ 1}
  isCompact' := by simpa only [Metric.closedBall, dist_zero_right] using
    isCompact_closedBall (0 : ℚ_[p]) 1
  interior_nonempty' := by
    rw [IsOpen.interior_eq]
    · exact ⟨0, by simp⟩
    · simpa only [Metric.closedBall, dist_zero_right] using
        IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero

noncomputable instance instMeasureSpace : MeasureSpace ℚ_[p] :=
  ⟨addHaarMeasure unitBall_positiveCompact⟩

instance instIsAddHaarMeasure : IsAddHaarMeasure (volume : Measure ℚ_[p]) :=
  isAddHaarMeasure_addHaarMeasure _

lemma volume_closedBall_one : volume {x : ℚ_[p] | ‖x‖ ≤ 1} = 1 := addHaarMeasure_self

end Padic

namespace PadicInt

instance instMeasurableSpace : MeasurableSpace ℤ_[p] := Subtype.instMeasurableSpace
instance instBorelSpace : BorelSpace ℤ_[p] := Subtype.borelSpace _

lemma isMeasurableEmbedding_coe : MeasurableEmbedding ((↑) : ℤ_[p] → ℚ_[p]) := by
  convert isOpenEmbedding_coe.measurableEmbedding

lemma isMeasurableEmbedding_coeRingHom : MeasurableEmbedding (Coe.ringHom (p := p)) :=
  (coe_coeRingHom (p := p)) ▸ isMeasurableEmbedding_coe

noncomputable instance instMeasureSpace : MeasureSpace ℤ_[p] := ⟨addHaarMeasure ⊤⟩

instance instIsAddHaarMeasure : IsAddHaarMeasure (volume : Measure ℤ_[p]) :=
  isAddHaarMeasure_addHaarMeasure _

@[simp] lemma volume_univ : volume (Set.univ : Set ℤ_[p]) = 1 := addHaarMeasure_self

instance instIsFiniteMeasure : IsFiniteMeasure (volume : Measure ℤ_[p]) where
  measure_univ_lt_top := by simp

instance isCompact_subring : IsCompact (subring p).carrier := by
  simpa [Metric.closedBall] using isCompact_closedBall (0 : ℚ_[p]) 1

instance compactSpace_subring : CompactSpace (subring p) :=
  isCompact_iff_compactSpace.mp isCompact_subring

-- https://github.com/ImperialCollegeLondon/FLT/issues/278
@[simp] lemma volume_coe (s : Set ℤ_[p]) : volume ((↑) '' s : Set ℚ_[p]) = volume s := by
  rw [← (coe_coeRingHom (p := p)), ← isMeasurableEmbedding_coeRingHom.comap_apply]
  have := IsAddLeftInvariant.comap volume (f := Coe.ringHom.toAddMonoidHom)
    (by apply isMeasurableEmbedding_coeRingHom (p := p))
  have := IsFiniteMeasureOnCompacts.comap' volume
    (by simpa using continuous_iff_le_induced.mpr fun U a ↦ a)
    (isMeasurableEmbedding_coeRingHom (p := p))
  rw [isAddLeftInvariant_eq_smul (comap Coe.ringHom volume) (volume : Measure ℤ_[p])]
  suffices (comap (Coe.ringHom (p := p)) volume).addHaarScalarFactor volume = 1 by
    simp [-coe_coeRingHom, this]
  
  -- #check AddMonoidHom.measurePreserving
  /- let fcoe : ℤ_[p] →ₜ+ (subring p)  := {
    toFun x := ⟨Coe.ringHom x, by simp⟩
    map_zero' := by simp
    map_add' _ _ := by norm_cast
    continuous_toFun := by simpa using continuous_id
  }
  #check AddMonoidHom.measurePreserving
  (μ := volume.restrict _) (ν := volume) fcoe.continuous_toFun -/
  sorry

end PadicInt
