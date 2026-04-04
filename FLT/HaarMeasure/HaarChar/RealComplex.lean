/-
Copyright (c) 2024 Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Javier López-Contreras
-/
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import FLT.HaarMeasure.HaarChar.Ring

/-!
# The distributive Haar characters of `ℝ` and `ℂ`

This file computes `ringHaarChar` for `ℝ` and `ℂ`.

This lets us know what `volume (x • s)` is in terms of `‖x‖` and `volume s`, when `x` is a
nonzero real/complex number and `s` is a set of reals/complex numbers.

## Main declarations

* `ringHaarChar_real`: `ringHaarChar` is the usual norm on `ℝ`.
* `ringHaarChar_complex`: `ringHaarChar` is the usual norm on `ℂ` squared.
* `Real.volume_real_smul`: `volume (x • s) = ‖x‖₊ * volume s` for all `x : ℝ` and `s : Set ℝ`.
* `Complex.volume_complex_smul`: `volume (z • s) = ‖z‖₊ ^ 2 * volume s` for all `z : ℂ` and
  `s : Set ℂ`.
-/

open Real Complex MeasureTheory Measure Set
open scoped Pointwise

lemma Real.volume_real_smul (x : ℝ) (s : Set ℝ) : volume (x • s) = ‖x‖₊ * volume s := by
  simp [← enorm_eq_ofReal_abs, enorm_eq_nnnorm]

/-- The distributive Haar character of the action of `ℝˣ` on `ℝ` is the usual norm.

This means that `volume (x • s) = ‖x‖ * volume s` for all `x : ℝ` and `s : Set ℝ`.
See `Real.volume_real_smul`. -/
lemma MeasureTheory.ringHaarChar_real (x : ℝˣ) : ringHaarChar x = ‖(x : ℝ)‖₊ :=
  -- We compute that `volume (x • [0, 1]) = ‖x‖₊ * volume [0, 1]`.
  ringHaarChar_eq_of_measure_smul_eq_mul (s := Icc 0 1) (μ := volume)
    (measure_pos_of_nonempty_interior _ <| by simp).ne' isCompact_Icc.measure_ne_top
      (Real.volume_real_smul ..)

set_option backward.isDefEq.respectTransparency false in
/-- The distributive Haar character of the action of `ℂˣ` on `ℂ` is the usual norm squared.

This means that `volume (z • s) = ‖z‖ ^ 2 * volume s` for all `z : ℂ` and `s : Set ℂ`.
See `Complex.volume_complex_smul`. -/
lemma MeasureTheory.ringHaarChar_complex (z : ℂˣ) : ringHaarChar z = ‖(z : ℂ)‖₊ ^ 2 := by
  -- We compute that `volume (x • ([0, 1] × [0, 1])) = ‖x‖₊ ^ 2 * volume ([0, 1] × [0, 1])`.
  refine ringHaarChar_eq_of_measure_smul_eq_mul (s := Icc 0 1 ×ℂ Icc 0 1) (μ := volume)
    (measure_pos_of_nonempty_interior _ <| by simp [interior_reProdIm]).ne'
    (isCompact_Icc.reProdIm isCompact_Icc).measure_ne_top ?_
  -- The determinant of left multiplication by `z⁻¹` as a `ℝ`-linear map is `‖z‖₊ ^ (-2)`.
  have key : ((LinearMap.mul ℂ ℂ z⁻¹).restrictScalars ℝ).det = ‖z.val‖₊ ^ (-2 : ℤ) := by
    refine Complex.ofReal_injective ?_
    rw [LinearMap.det_restrictScalars]
    simp [Algebra.norm_complex_apply, normSq_eq_norm_sq, zpow_ofNat]
  -- Massaging, we find the result.
  convert addHaar_preimage_linearMap (E := ℂ) volume
    (f := (LinearMap.mul ℂ ℂ z⁻¹).restrictScalars ℝ) _ _ using 2
  · simpa [LinearMap.mul, LinearMap.mk₂, LinearMap.mk₂', LinearMap.mk₂'ₛₗ, Units.smul_def, eq_comm]
      using preimage_smul_inv z (Icc 0 1 ×ℂ Icc 0 1)
  · simp [key, ENNReal.ofReal_pow, zpow_ofNat]; rfl
  · simp [key, zpow_ofNat]

set_option backward.isDefEq.respectTransparency false in
lemma Complex.volume_complex_smul (z : ℂ) (s : Set ℂ) : volume (z • s) = ‖z‖₊ ^ 2 * volume s := by
  obtain rfl | hz := eq_or_ne z 0
  · simp [(finite_zero.subset s.zero_smul_set_subset).measure_zero]
  · lift z to ℂˣ using hz.isUnit
    rw [← ENNReal.coe_pow, ← ringHaarChar_complex, ← Units.smul_def, ringHaarChar_mul_volume]
