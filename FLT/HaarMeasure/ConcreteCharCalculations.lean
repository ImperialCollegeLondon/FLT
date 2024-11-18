import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.Analysis.Normed.Group.Ultra
import FLT.HaarMeasure.DistribHaarChar
import FLT.Mathlib.Analysis.Complex.Basic
import FLT.Mathlib.Data.Complex.Basic
import FLT.Mathlib.LinearAlgebra.Determinant
import FLT.Mathlib.MeasureTheory.Group.Action
import FLT.Mathlib.NumberTheory.Padics.PadicIntegers
import FLT.Mathlib.NumberTheory.Padics.MeasurableSpacePadics
import FLT.Mathlib.RingTheory.Norm.Defs

open Real Complex Padic MeasureTheory Measure NNReal Set TopologicalSpace
open scoped Pointwise ENNReal Localization

lemma distribHaarChar_complex (z : ℂˣ) : distribHaarChar ℂ z = ‖(z : ℂ)‖₊ ^ (-2 : ℤ) := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (s := Icc 0 1 ×ℂ Icc 0 1) (μ := volume)
    (measure_pos_of_nonempty_interior _ <| by simp [interior_reProdIm]).ne'
    (isCompact_Icc.reProdIm isCompact_Icc).measure_ne_top ?_
  have key : ((LinearMap.mul ℂ ℂ z).restrictScalars ℝ).det = ‖z.val‖₊ ^ 2 := by
    refine Complex.ofReal_injective ?_
    rw [LinearMap.det_restrictScalars]
    simp [Algebra.norm_complex_apply, normSq_eq_norm_sq, zpow_ofNat]
  have := addHaar_preimage_linearMap (E := ℂ) volume
    (f := (LinearMap.mul ℂ ℂ z).restrictScalars ℝ)
  simp [key] at this
  convert this _ using 2
  · symm
    exact Set.preimage_smul z _
  · simp [← Real.ennnorm_eq_ofReal_abs, ← Complex.norm_eq_abs, zpow_ofNat]

lemma distribHaarChar_real (x : ℝˣ) : distribHaarChar ℝ x = ‖(x : ℝ)‖₊⁻¹ := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (s := Icc 0 1) (μ := volume)
    (measure_pos_of_nonempty_interior _ <| by simp).ne' isCompact_Icc.measure_ne_top ?_
  rw [Units.smul_def, Measure.addHaar_smul]
  simp [Real.ennnorm_eq_ofReal_abs, abs_inv, ENNReal.ofReal_inv_of_pos]

variable {p : ℕ} [Fact p.Prime]

private lemma distribHaarChar_padic_integral (x : nonZeroDivisors ℤ_[p]) :
  distribHaarChar ℚ_[p] (x : ℚ_[p]ˣ) = ‖(x : ℚ_[p])‖₊⁻¹ := by
  let K : AddSubgroup ℚ_[p] :=
    (IsUltrametricDist.closedBall_openAddSubgroup _ (zero_lt_one)).toAddSubgroup
  -- have : K = ℤ_[p] := rfl
  -- TODO: See `FLT.Mathlib.Analysis.Normed.Group.Ultra`. This would make `K = ℤ_[p]` definitionally
  refine distribHaarChar_eq_of_measure_smul_eq_mul (s := K) (μ := volume) (G := ℚ_[p]ˣ)
    (by simp [K, IsUltrametricDist.closedBall_openAddSubgroup, Metric.closedBall, Padic.volume_closedBall (p := p)])
    (by simp [K, IsUltrametricDist.closedBall_openAddSubgroup, Metric.closedBall, Padic.volume_closedBall (p := p)])
    ?_
  rw [Units.smul_def]
  simp
  let H := (x : ℚ_[p])⁻¹ • K
  rw [← ENNReal.mul_eq_mul_left (a := H.relindex K) (by sorry) (by sorry)]
  let h : (H.addSubgroupOf K).FiniteIndex := sorry
  change _ * volume (H : Set ℚ_[p]) = _
  rw [index_mul_addHaar_addSubgroup_eq_addHaar_addSubgroup (μ := volume) (K := K)]
  -- volume (K) = 1 via this line
  -- simp [K, IsUltrametricDist.closedBall_openAddSubgroup, Metric.closedBall, Padic.volume_closedBall]
  sorry
  sorry
  · exact measurableSet_closedBall.const_smul (x⁻¹ : ℚ_[p]ˣ)
  · exact measurableSet_closedBall

lemma distribHaarChar_padic (x : ℚ_[p]ˣ) : distribHaarChar ℚ_[p] x = ‖(x : ℚ_[p])‖₊⁻¹ := by
  let g : ℚ_[p]ˣ →* ℝ≥0 := {
    toFun := fun x => ‖(x : ℚ_[p])‖₊⁻¹
    map_one' := by simp
    map_mul' := by simp [mul_comm]
  }
  revert x
  suffices distribHaarChar ℚ_[p] = g by simp [this, g]
  refine MonoidHom.eq_of_eqOn_dense (PadicInt.closure_nonZeroDiviorsZp_eq_unitsQp (p := p)) ?_
  simp
  ext x
  simp [g]
  rw [distribHaarChar_padic_integral]
  rfl
