/-
Copyright (c) 2024 Yaël Dillies, David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, David Loeffler
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.NumberTheory.Padics.ProperSpace
public import FLT.Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Measurability and measures on the p-adics

This file endows `ℤ_[p]` and `ℚ_[p]` with their Borel sigma-algebra and their Haar measure that
makes `ℤ_[p]` (or the copy of `ℤ_[p]` inside `ℚ_[p]`) have norm `1`.
-/

@[expose] public section

open MeasureTheory Measure TopologicalSpace Topology

variable {p : ℕ} [Fact p.Prime]

namespace Padic

noncomputable instance instMeasurableSpace : MeasurableSpace ℚ_[p] := borel _
instance instBorelSpace : BorelSpace ℚ_[p] := ⟨rfl⟩

-- Should we more generally make a map from `CompactOpens` to `PositiveCompacts`?
/-- The unit ball as a compact set with nonempty interior. -/
def unitBall_positiveCompact : PositiveCompacts ℚ_[p] where
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

noncomputable instance instMeasurableSpace : MeasurableSpace ℤ_[p] := Subtype.instMeasurableSpace
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

lemma volume_coe_univ :
    volume ((↑) '' (Set.univ : Set ℤ_[p]) : Set ℚ_[p]) = volume (Set.univ : Set ℤ_[p]) := by
  simp only [volume_univ, ← Padic.volume_closedBall_one (p := p)]
  -- ❌️ at reducible transparency,
  --   ℤ_[p]
  -- and
  --   { x : ℚ_[p] // Membership.mem (γ := Set ℚ_[p]) (fun x ↦ Real.le✝ ‖x‖ 1) x }
  -- are not defeq, but they are at default transparency.
  erw [Subtype.coe_image_univ]
  rfl

set_option backward.isDefEq.respectTransparency false in
-- https://github.com/ImperialCollegeLondon/FLT/issues/278
@[simp] lemma volume_coe (s : Set ℤ_[p]) : volume ((↑) '' s : Set ℚ_[p]) = volume s := by
  have h := volume_coe_univ (p := p)
  rw [← (coe_coeRingHom (p := p)), ← isMeasurableEmbedding_coeRingHom.comap_apply] at h ⊢
  have := IsAddLeftInvariant.comap volume
    (f := Coe.ringHom.toAddMonoidHom)
    (isMeasurableEmbedding_coeRingHom (p := p))
  have := IsFiniteMeasureOnCompacts.comap' volume
    (continuous_iff_le_induced.mpr fun _ h ↦ h)
    (isMeasurableEmbedding_coeRingHom (p := p))
  rw [isAddLeftInvariant_eq_smul (comap Coe.ringHom volume) (volume : Measure ℤ_[p])] at h ⊢
  suffices (comap (Coe.ringHom (p := p)) volume).addHaarScalarFactor volume = 1 by
    simp [-coe_coeRingHom, this]
  simpa only [smul_apply, volume_univ, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_eq_one]
    using h

end PadicInt
