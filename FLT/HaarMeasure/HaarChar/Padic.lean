/-
Copyright (c) 2024 Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Javier López-Contreras
-/
import FLT.Mathlib.MeasureTheory.Group.Action
import FLT.HaarMeasure.MeasurableSpacePadics
import FLT.HaarMeasure.HaarChar.Ring

/-!
# The distributive Haar characters of the p-adics

This file computes `ringHaarChar` for `ℤ_[p]` and `ℚ_[p]`.

This lets us know what `volume (x • s)` is in terms of `‖x‖` and `volume s`, when `x` is a
p-adic/p-adic integer and `s` is a set of p-adics/p-adic integers.

## Main declarations

* `ringHaarChar_padic`: `ringHaarChar` is the usual p-adic norm on `ℚ_[p]ˣ`.
* `ringHaarChar_padicInt`: `ringHaarChar` is constantly `1` on `ℤ_[p]ˣ`.
* `Padic.volume_padic_smul`: `volume (x • s) = ‖x‖₊ * volume s` for all `x : ℚ_[p]` and
  `s : Set ℚ_[p]`.
* `PadicInt.volume_padicInt_smul`: `volume (x • s) = ‖x‖₊ * volume s` for all `x : ℤ_[p]` and
  `s : Set ℤ_[p]`.
-/

open Padic MeasureTheory Measure Metric Set
open scoped Pointwise ENNReal NNReal nonZeroDivisors

variable {p : ℕ} [Fact p.Prime]

private lemma MeasureTheory.ringHaarChar_padic_padicInt (x : ℤ_[p]⁰) :
    ringHaarChar (x : ℚ_[p]ˣ) = ‖(x : ℚ_[p])‖₊ := by
  -- Let `K` be the copy of `ℤ_[p]` inside `ℚ_[p]` and `H` be `xK`.
  let K : AddSubgroup ℚ_[p] := (1 : Submodule ℤ_[p] ℚ_[p]).toAddSubgroup
  let H := (x : ℚ_[p]) • K
  -- We compute that `volume H = ‖x‖₊ * volume K`.
  refine ringHaarChar_eq_of_measure_smul_eq_mul (s := K) (μ := volume) (R := ℚ_[p])
    (by simp [K, Padic.submodule_one_eq_closedBall, closedBall, Padic.volume_closedBall_one])
    (by simp [K, Padic.submodule_one_eq_closedBall, closedBall, Padic.volume_closedBall_one]) ?_
  change volume (H : Set ℚ_[p]) = ‖(x : ℚ_[p])‖₊ * volume (K : Set ℚ_[p])
  -- This is true because `H` is a `‖x‖₊⁻¹`-index subgroup of `K`.
  have hHK : H ≤ K := by
    simpa [H, K, -Submodule.smul_le_self_of_tower]
      using (1 : Submodule ℤ_[p] ℚ_[p]).smul_le_self_of_tower (x : ℤ_[p])
  have x_nonzero: x.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.1 x.property
  have : H.IsFiniteRelIndex K :=
    PadicInt.smul_submodule_one_isFiniteRelIndex (p := p) x_nonzero
  have H_relindex_Z : (H.relindex K : ℝ≥0∞) = ‖(x : ℚ_[p])‖₊⁻¹ :=
    congr(ENNReal.ofNNReal $(PadicInt.smul_submodule_one_relindex (p := p)))
  rw [← index_mul_addHaar_addSubgroup_eq_addHaar_addSubgroup hHK, H_relindex_Z, ENNReal.coe_inv,
    ENNReal.mul_inv_cancel_left]
  · simp
  · simp
  · simp
  · simpa [H, K, Padic.submodule_one_eq_closedBall]
      using measurableSet_closedBall.const_smul (x : ℚ_[p]ˣ)
  · simpa [K, Padic.submodule_one_eq_closedBall] using measurableSet_closedBall

/-- The distributive Haar character of the action of `ℚ_[p]ˣ` on `ℚ_[p]` is the usual p-adic norm.

This means that `volume (x • s) = ‖x‖ * volume s` for all `x : ℚ_[p]` and `s : Set ℚ_[p]`.
See `Padic.volume_padic_smul` -/
@[simp]
lemma MeasureTheory.ringHaarChar_padic (x : ℚ_[p]ˣ) : ringHaarChar x = ‖(x : ℚ_[p])‖₊ := by
  -- Write the RHS as the application of a monoid hom `g`.
  let g : ℚ_[p]ˣ →* ℝ≥0 := {
    toFun := fun x => ‖(x : ℚ_[p])‖₊
    map_one' := by simp
    map_mul' := by simp
  }
  change ringHaarChar.toMulHom x = _
  revert x
  suffices ringHaarChar (R := ℚ_[p]) = g by simp [this, g]
  -- By density of `ℤ_[p]⁰` inside `ℚ_[p]ˣ`, it's enough to check that `ringHaarChar ℚ_[p]` and
  -- `g` agree on `ℤ_[p]⁰`.
  refine MonoidHom.eq_of_eqOn_dense (PadicInt.closure_nonZeroDivisors_padicInt (p := p)) ?_
  -- But this is what we proved in `ringHaarChar_padic_padicInt`.
  simp only [eqOn_range, g]
  ext x
  simp only [MonoidHom.coe_coe, Function.comp_apply, MonoidHom.coe_mk,
    OneHom.coe_mk, Units.val_mk0, coe_nnnorm, PadicInt.padic_norm_e_of_padicInt,
    ringHaarChar_padic_padicInt]

@[simp]
lemma Padic.volume_padic_smul (x : ℚ_[p]) (s : Set ℚ_[p]) : volume (x • s) = ‖x‖₊ * volume s := by
  obtain rfl | hx := eq_or_ne x 0
  · simp [(finite_zero.subset s.zero_smul_set_subset).measure_zero]
  · lift x to ℚ_[p]ˣ using hx.isUnit
    rw [← ringHaarChar_padic, ← Units.smul_def, ringHaarChar_mul_volume]

@[simp] lemma Padic.volume_padicInt_smul (x : ℤ_[p]) (s : Set ℚ_[p]) :
    volume (x • s) = ‖x‖₊ * volume s := by simpa [-volume_padic_smul] using volume_padic_smul x s

@[simp] lemma PadicInt.volume_padicInt_smul (x : ℤ_[p]) (s : Set ℤ_[p]) :
    volume (x • s) = ‖x‖₊ * volume s := by
  simpa [-volume_padicInt_smul, ← image_coe_smul_set] using Padic.volume_padicInt_smul x ((↑) '' s)

/-- The distributive Haar character of the action of `ℤ_[p]ˣ` on `ℤ_[p]` is the constant `1`.

This means that `volume (x • s) = ‖x‖ * volume s` for all `x : ℤ_[p]` and `s : Set ℤ_[p]`.
See `PadicInt.volume_padicInt_smul` -/
@[simp]
lemma MeasureTheory.ringHaarChar_padicInt (x : ℤ_[p]ˣ) : ringHaarChar x = 1 :=
  -- We compute `ringHaarChar ℤ_[p]` by lifting everything to `ℚ_[p]`.
  ringHaarChar_eq_of_measure_smul_eq_mul (s := univ) (μ := volume) (by simp) (measure_ne_top _ _)
    (by simp)
