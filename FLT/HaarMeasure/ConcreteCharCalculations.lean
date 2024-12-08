import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import FLT.Mathlib.Analysis.Complex.Basic
import FLT.Mathlib.Data.Complex.Basic
import FLT.Mathlib.LinearAlgebra.Determinant
import FLT.Mathlib.MeasureTheory.Group.Action
import FLT.Mathlib.NumberTheory.Padics.MeasurableSpacePadics
import FLT.Mathlib.RingTheory.Norm.Defs
import FLT.HaarMeasure.DistribHaarChar

open Real Complex Padic MeasureTheory Measure NNReal Set  IsUltrametricDist Metric
open scoped Pointwise ENNReal Localization

lemma distribHaarChar_complex (z : ℂˣ) : distribHaarChar ℂ z = ‖(z : ℂ)‖₊ ^ 2 := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (s := Icc 0 1 ×ℂ Icc 0 1) (μ := volume)
    (measure_pos_of_nonempty_interior _ <| by simp [interior_reProdIm]).ne'
    (isCompact_Icc.reProdIm isCompact_Icc).measure_ne_top ?_
  have key : ((LinearMap.mul ℂ ℂ z⁻¹).restrictScalars ℝ).det = ‖z.val‖₊ ^ (-2 : ℤ) := by
    refine Complex.ofReal_injective ?_
    rw [LinearMap.det_restrictScalars]
    simp [Algebra.norm_complex_apply, normSq_eq_norm_sq, zpow_ofNat]
  have := addHaar_preimage_linearMap (E := ℂ) volume
    (f := (LinearMap.mul ℂ ℂ z⁻¹).restrictScalars ℝ)
  simp [key] at this
  convert this _ _ using 2
  · symm
    simpa [LinearMap.mul, LinearMap.mk₂, LinearMap.mk₂', LinearMap.mk₂'ₛₗ, Units.smul_def]
      using Set.preimage_smul_inv z (Icc 0 1 ×ℂ Icc 0 1)
  · simp [ofReal_norm_eq_coe_nnnorm, ← Complex.norm_eq_abs, ENNReal.ofReal_pow, zpow_ofNat]
  · simp [zpow_ofNat]

lemma distribHaarChar_real (x : ℝˣ) : distribHaarChar ℝ x = ‖(x : ℝ)‖₊ := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (s := Icc 0 1) (μ := volume)
    (measure_pos_of_nonempty_interior _ <| by simp).ne' isCompact_Icc.measure_ne_top ?_
  rw [Units.smul_def, Measure.addHaar_smul]
  simp [Real.ennnorm_eq_ofReal_abs, abs_inv, ENNReal.ofReal_inv_of_pos]

variable {p : ℕ} [Fact p.Prime]

private lemma finiteIndex_smul (x : nonZeroDivisors ℤ_[p]) :
    ((closedBall_openAddSubgroup ℚ_[p] zero_lt_one).addSubgroupOf
      ((x : ℚ_[p]) • (closedBall_openAddSubgroup _ zero_lt_one).toAddSubgroup)).FiniteIndex := sorry

private lemma relindex_smul (x : nonZeroDivisors ℤ_[p]) :
    (closedBall_openAddSubgroup ℚ_[p] zero_lt_one).toAddSubgroup.relindex
      ((x : ℚ_[p]) • (closedBall_openAddSubgroup _ zero_lt_one).toAddSubgroup) = ‖(x : ℚ_[p])‖₊ :=
  sorry

private lemma distribHaarChar_padic_integral (x : nonZeroDivisors ℤ_[p]) :
    distribHaarChar ℚ_[p] (x : ℚ_[p]ˣ) = ‖(x : ℚ_[p])‖₊ := by
  let Z : AddSubgroup ℚ_[p] := (closedBall_openAddSubgroup _ zero_lt_one).toAddSubgroup
  -- have : K = ℤ_[p] := rfl
  -- TODO: See `FLT.Mathlib.Analysis.Normed.Group.Ultra`. This would make `Z = ℤ_[p]` definitionally
  refine distribHaarChar_eq_of_measure_smul_eq_mul (s := Z) (μ := volume) (G := ℚ_[p]ˣ)
    (by simp [Z, closedBall_openAddSubgroup, Metric.closedBall, Padic.volume_closedBall])
    (by simp [Z, closedBall_openAddSubgroup, Metric.closedBall, Padic.volume_closedBall]) ?_
  let H := (x : ℚ_[p]) • Z
  rw [Units.smul_def]
  change volume (H : Set ℚ_[p]) = _
  have : (Z.addSubgroupOf H).FiniteIndex := finiteIndex_smul _
  rw [← index_mul_addHaar_addSubgroup_eq_addHaar_addSubgroup (μ := volume) (H := Z)]
  · congr 1
    exact mod_cast relindex_smul x
  · sorry
  · exact measurableSet_closedBall
  · exact measurableSet_closedBall.const_smul (x : ℚ_[p]ˣ)

lemma distribHaarChar_padic (x : ℚ_[p]ˣ) : distribHaarChar ℚ_[p] x = ‖(x : ℚ_[p])‖₊ := by
  let g : ℚ_[p]ˣ →* ℝ≥0 := {
    toFun := fun x => ‖(x : ℚ_[p])‖₊
    map_one' := by simp
    map_mul' := by simp
  }
  revert x
  suffices distribHaarChar ℚ_[p] = g by simp [this, g]
  refine MonoidHom.eq_of_eqOn_dense (PadicInt.closure_nonZeroDivisorsZp_eq_unitsQp (p := p)) ?_
  simp
  ext x
  simp [g]
  rw [distribHaarChar_padic_integral]
  rfl
