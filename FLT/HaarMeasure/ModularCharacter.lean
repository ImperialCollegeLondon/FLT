import FLT.Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory Measure
open scoped NNReal

variable {G A : Type*} [Group G] [AddCommGroup A] [DistribMulAction G A]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
  [TopologicalAddGroup A]
  [MeasurableSpace G] -- not needed actually
  [LocallyCompactSpace A] [ContinuousConstSMul G A] [MeasurableSMul G A]
variable (μ ν : Measure A) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]

noncomputable
instance : DistribMulAction Gᵈᵐᵃ (Measure A) where
  smul g μ := μ.map ((DomMulAct.mk.symm g : G)⁻¹ • ·)
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

instance : SMulCommClass ℝ≥0 Gᵈᵐᵃ (Measure A) where
  smul_comm r g μ := by
    show r • μ.map _ = (r • μ).map _
    simp

instance : SMulCommClass Gᵈᵐᵃ ℝ≥0 (Measure A) := .symm ..

instance (g : Gᵈᵐᵃ) : (g • μ).IsAddHaarMeasure :=
  (DistribMulAction.toAddEquiv _ ((DomMulAct.mk.symm g : G)⁻¹)).isAddHaarMeasure_map _
    (continuous_const_smul _) (continuous_const_smul _)

lemma addHaarScalarFactor_dma_smul (g : Gᵈᵐᵃ) :
    addHaarScalarFactor (g • μ) (g • ν) = addHaarScalarFactor μ ν := by
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_one⟩ :
    ∃ f : C(A, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 0 ≠ 0 := exists_continuous_nonneg_pos 0
  have int_g_ne_zero : ∫ x, f x ∂g • ν ≠ 0 :=
    ne_of_gt (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_one)
  apply NNReal.coe_injective
  refine (addHaarScalarFactor_eq_integral_div (g • μ) (g • ν) f_cont f_comp int_g_ne_zero).trans ?_
  conv =>
    enter [1, 1]
    tactic => exact integral_map_equiv (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) f
  conv =>
    enter [1, 2]
    tactic => exact integral_map_equiv (MeasurableEquiv.smul ((DomMulAct.mk.symm g : G)⁻¹)) f
  simp only [MeasurableEquiv.smul_apply]
  refine (addHaarScalarFactor_eq_integral_div _ _ ?_ ?_ ?_).symm
  fun_prop
  · apply f_comp.comp_isClosedEmbedding
    exact (Homeomorph.smul (DomMulAct.mk.symm g : G)⁻¹).isClosedEmbedding
  · erw [← integral_map_equiv (MeasurableEquiv.smul (DomMulAct.mk.symm g : G)⁻¹) f]
    show ∫ x, f x ∂g • ν ≠ 0
    exact ne_of_gt (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_one)

lemma addHaarScalarFactor_smul_congr (g : Gᵈᵐᵃ) :
    addHaarScalarFactor μ (g • μ) = addHaarScalarFactor ν (g • ν) := by
  rw [addHaarScalarFactor_eq_mul _ (g • ν), addHaarScalarFactor_dma_smul,
    mul_comm, ← addHaarScalarFactor_eq_mul]

variable (A) in
noncomputable def modularHaarChar : G →* ℝ≥0 where
  toFun g := addHaarScalarFactor (addHaar (G := A)) (DomMulAct.mk g • addHaar)
  map_one' := by simp
  map_mul' g g' := by
    simp
    rw [addHaarScalarFactor_eq_mul _ (DomMulAct.mk g • addHaar (G := A))]
    congr 1
    simp_rw [mul_smul]
    exact addHaarScalarFactor_smul_congr ..

lemma addHaarScalarFactor_smul_eq_modularHaarChar (g : G) :
  addHaarScalarFactor μ (DomMulAct.mk g • μ) = modularHaarChar A g :=
  addHaarScalarFactor_smul_congr ..
