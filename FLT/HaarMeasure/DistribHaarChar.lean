/-
Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras
-/
import FLT.Mathlib.Data.ENNReal.Inv
import FLT.ForMathlib.DomMulActMeasure

/-!
# The distributive character of Haar measures

Given a group `G` acting on an measurable additive commutative group `A`, and an element `g : G`,
one can pull back the Haar measure `μ` of `A` along the map `(g • ·) : A → A` to get another Haar
measure `μ'` on `A`. By unicity of Haar measures, there exists some nonnegative real number `r` such
that `μ' = r • μ`. We can thus define a map `distribHaarChar : G → ℝ≥0` sending `g` to its
associated real number `r`. Furthermore, this number doesn't depend on the Haar measure `μ` we
started with, and `distribHaarChar` is a group homomorphism.

## See also

[Zulip](https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/canonical.20norm.20coming.20from.20Haar.20measure/near/480050592)
-/

open scoped NNReal Pointwise ENNReal

namespace MeasureTheory.Measure

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
  [MeasurableSpace A]
  [MeasurableSpace G] -- not needed actually
  [MeasurableSMul G A] -- only need `MeasurableConstSMul` but we don't have this class.
variable {μ ν : Measure A} {g : G}

variable [TopologicalSpace A] [BorelSpace A] [TopologicalAddGroup A] [LocallyCompactSpace A]
  [ContinuousConstSMul G A] [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]

variable (μ A) in
@[simps (config := .lemmasOnly)]
noncomputable def distribHaarChar : G →* ℝ≥0 where
  toFun g := addHaarScalarFactor (addHaar (G := A)) (DomMulAct.mk g • addHaar)
  map_one' := by simp
  map_mul' g g' := by
    simp
    rw [addHaarScalarFactor_eq_mul _ (DomMulAct.mk g • addHaar (G := A))]
    congr 1
    simp_rw [mul_smul]
    exact addHaarScalarFactor_smul_congr ..

variable (μ) in
lemma addHaarScalarFactor_smul_eq_distribHaarChar (g : G) :
    addHaarScalarFactor μ (DomMulAct.mk g • μ) = distribHaarChar A g :=
  addHaarScalarFactor_smul_congr ..

variable (μ) in
lemma addHaarScalarFactor_smul_inv_eq_distribHaarChar (g : G) :
    addHaarScalarFactor ((DomMulAct.mk g)⁻¹ • μ) μ = distribHaarChar A g := by
  rw [← addHaarScalarFactor_dma_smul _ _ (DomMulAct.mk g)]
  simp_rw [← mul_smul, mul_inv_cancel, one_smul]
  exact addHaarScalarFactor_smul_eq_distribHaarChar ..

variable (μ) in
lemma addHaarScalarFactor_smul_eq_distribHaarChar_inv (g : G) :
    addHaarScalarFactor (DomMulAct.mk g • μ) μ = (distribHaarChar A g)⁻¹ := by
  rw [← map_inv, ← addHaarScalarFactor_smul_inv_eq_distribHaarChar μ, DomMulAct.mk_inv, inv_inv]

lemma distribHaarChar_pos : 0 < distribHaarChar A g :=
  pos_iff_ne_zero.mpr ((Group.isUnit g).map (distribHaarChar A)).ne_zero

variable [IsFiniteMeasureOnCompacts μ] [Regular μ] {s : Set A}

variable (μ) in
lemma distribHaarChar_mul (g : G) (s : Set A) : distribHaarChar A g * μ s = μ (g⁻¹ • s) := by
  have : (DomMulAct.mk g⁻¹ • μ) s = μ (g⁻¹ • s) := by simp [dma_smul_apply]
  rw [eq_comm, ← nnreal_smul_coe_apply, ← inv_smul_eq_iff₀ distribHaarChar_pos.ne', ← map_inv,
    ← addHaarScalarFactor_smul_eq_distribHaarChar μ,
    ← this, ← smul_apply, ← isAddLeftInvariant_eq_smul_of_regular μ (DomMulAct.mk g⁻¹ • μ)]

lemma distribHaarChar_eq_div (hs₀ : μ s ≠ 0) (hs : μ s ≠ ∞) (g : G) :
    distribHaarChar A g = μ (g⁻¹ • s) / μ s := by
  rw [← distribHaarChar_mul, ENNReal.mul_div_cancel_right hs₀ hs]
