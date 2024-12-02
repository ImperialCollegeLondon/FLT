/-
Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras
-/
import Mathlib.MeasureTheory.Measure.Haar.Unique

open scoped NNReal Pointwise ENNReal

namespace MeasureTheory.Measure

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
  [MeasurableSpace A]
  [MeasurableSpace G] -- not needed actually
  [MeasurableSMul G A] -- We only need `MeasurableConstSMul` but we don't have this class.
variable {μ ν : Measure A} {g : G}

noncomputable
instance : DistribMulAction Gᵈᵐᵃ (Measure A) where
  smul g μ := μ.map ((DomMulAct.mk.symm g)⁻¹ • ·)
  one_smul μ := show μ.map _ = _ by simp
  mul_smul g g' μ := by
    show μ.map _ = ((μ.map _).map _)
    rw [map_map]
    · simp [Function.comp_def, mul_smul]
    · exact measurable_const_smul ..
    · exact measurable_const_smul ..
  smul_zero g := by
    show (0 : Measure A).map _ = 0
    simp
  smul_add g μ ν := by
    show (μ + ν).map _ = μ.map _ + ν.map _
    rw [Measure.map_add]
    exact measurable_const_smul ..

lemma dma_smul_apply (μ : Measure A) (g : Gᵈᵐᵃ) (s : Set A) :
    (g • μ) s = μ ((DomMulAct.mk.symm g) • s) := by
  refine ((MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)).map_apply _).trans ?_
  congr 1
  exact Set.preimage_smul_inv (DomMulAct.mk.symm g) s

lemma integral_dma_smul {α} [NormedAddCommGroup α] [NormedSpace ℝ α] (g : Gᵈᵐᵃ) (f : A → α) :
    ∫ x, f x ∂g • μ = ∫ x, f ((DomMulAct.mk.symm g)⁻¹ • x) ∂μ :=
  integral_map_equiv (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) f

variable [TopologicalSpace A] [BorelSpace A] [TopologicalAddGroup A] [LocallyCompactSpace A]
  [ContinuousConstSMul G A] [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]

instance : SMulCommClass ℝ≥0 Gᵈᵐᵃ (Measure A) where
  smul_comm r g μ := show r • μ.map _ = (r • μ).map _ by simp

instance : SMulCommClass Gᵈᵐᵃ ℝ≥0 (Measure A) := .symm ..

instance (g : Gᵈᵐᵃ) [Regular μ] : Regular (g • μ) :=
  Regular.map (μ := μ) (Homeomorph.smul ((DomMulAct.mk.symm g : G)⁻¹))

instance (g : Gᵈᵐᵃ) : (g • μ).IsAddHaarMeasure :=
  (DistribMulAction.toAddEquiv _ (DomMulAct.mk.symm g⁻¹)).isAddHaarMeasure_map _
    (continuous_const_smul _) (continuous_const_smul _)

variable (μ ν) in
lemma addHaarScalarFactor_dma_smul (g : Gᵈᵐᵃ) :
    addHaarScalarFactor (g • μ) (g • ν) = addHaarScalarFactor μ ν := by
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_zero⟩ :
    ∃ f : C(A, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 0 ≠ 0 := exists_continuous_nonneg_pos 0
  have int_f_ne_zero : ∫ x, f x ∂g • ν ≠ 0 :=
    (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_zero).ne'
  apply NNReal.coe_injective
  rw [addHaarScalarFactor_eq_integral_div (g • μ) (g • ν) f_cont f_comp int_f_ne_zero,
    integral_dma_smul, integral_dma_smul]
  refine (addHaarScalarFactor_eq_integral_div _ _ (by fun_prop) ?_ ?_).symm
  · exact f_comp.comp_isClosedEmbedding (Homeomorph.smul _).isClosedEmbedding
  · rw [← integral_dma_smul]
    exact (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_zero).ne'

variable (μ) in
lemma addHaarScalarFactor_smul_congr (g : Gᵈᵐᵃ) :
    addHaarScalarFactor μ (g • μ) = addHaarScalarFactor ν (g • ν) := by
  rw [addHaarScalarFactor_eq_mul _ (g • ν), addHaarScalarFactor_dma_smul,
    mul_comm, ← addHaarScalarFactor_eq_mul]
