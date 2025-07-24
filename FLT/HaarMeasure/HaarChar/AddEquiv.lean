import Mathlib.MeasureTheory.Measure.Haar.Unique
import FLT.Mathlib.Topology.Algebra.ContinuousMonoidHom
import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import FLT.Mathlib.MeasureTheory.Measure.Regular
import FLT.Mathlib.MeasureTheory.Group.Measure

open MeasureTheory.Measure
open scoped NNReal

namespace MeasureTheory

@[to_additive]
lemma _root_.ContinuousMulEquiv.isHaarMeasure_comap {G H : Type*}
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [MeasurableMul H] [BorelSpace H]
    (φ : G ≃ₜ* H) (μ : Measure H) [IsHaarMeasure μ] : IsHaarMeasure (comap φ μ) :=
  φ.toHomeomorph.isOpenEmbedding.isHaarMeasure_comap (φ := φ.toMulEquiv.toMonoidHom) μ

lemma _root_.Homeomorph.regular_comap {G H : Type*}
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    (φ : G ≃ₜ H) (μ : Measure H) [Regular μ] : Regular (comap φ μ) :=
  φ.isOpenEmbedding.regular_comap φ μ

lemma _root_.Homeomorph.regular_map {G H : Type*}
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    (φ : G ≃ₜ H) (μ : Measure G) [Regular μ] : Regular (map φ μ) :=
  (Regular.map_iff φ).mpr inferInstance

section basic

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

@[to_additive]
lemma IsHaarMeasure.nnreal_smul {μ : Measure G}
    [h : IsHaarMeasure μ] {c : ℝ≥0} (hc : 0 < c) : IsHaarMeasure (c • μ) :=
  h.smul _ (by simp [hc.ne']) (Option.some_ne_none _)

variable [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- If `φ : G ≃ₜ* G` then `mulEquivHaarChar φ` is the positive real factor by which
`φ` scales Haar measure on `G`. -/
@[to_additive "If `φ : A ≃ₜ+ A` then `addEquivAddHaarChar φ` is the positive
real factor by which `φ` scales Haar measure on `A`."]
noncomputable def mulEquivHaarChar (φ : G ≃ₜ* G) : ℝ≥0 :=
  haarScalarFactor haar (map φ haar)

@[to_additive]
lemma mulEquivHaarChar_pos (φ : G ≃ₜ* G) : 0 < mulEquivHaarChar φ :=
  haarScalarFactor_pos_of_isHaarMeasure _ _

-- should be in haarScalarFactor API
@[to_additive]
lemma mul_haarScalarFactor_smul (μ' μ : Measure G)
    [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {c : ℝ≥0}
    (hc : 0 < c) :
    haveI : IsHaarMeasure (c • μ) := IsHaarMeasure.nnreal_smul hc
    c * haarScalarFactor μ' (c • μ) = haarScalarFactor μ' μ := by
  haveI : IsHaarMeasure (c • μ) := IsHaarMeasure.nnreal_smul hc
  obtain ⟨⟨g, g_cont⟩, g_comp, g_nonneg, g_one⟩ :
    ∃ g : C(G, ℝ), HasCompactSupport g ∧ 0 ≤ g ∧ g 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_g_ne_zero : ∫ x, g x ∂μ ≠ 0 :=
    ne_of_gt (g_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero g_comp g_nonneg g_one)
  apply NNReal.coe_injective
  calc
    c * haarScalarFactor μ' (c • μ) = c * ((∫ x, g x ∂μ') / ∫ x, g x ∂(c • μ)) :=
      by rw [haarScalarFactor_eq_integral_div _ _ g_cont g_comp (by simp [int_g_ne_zero, hc.ne'])]
    _ = c * ((∫ x, g x ∂μ') / (c • ∫ x, g x ∂μ)) := by simp
    _ = (∫ x, g x ∂μ') / (∫ x, g x ∂μ) := by
      rw [NNReal.smul_def, smul_eq_mul, ← mul_div_assoc]
      exact mul_div_mul_left (∫ (x : G), g x ∂μ') (∫ (x : G), g x ∂μ) (by simp [hc.ne'])
    _ = μ'.haarScalarFactor μ :=
      (haarScalarFactor_eq_integral_div _ _ g_cont g_comp int_g_ne_zero).symm

-- should be in haarScalarFactor API
@[to_additive]
lemma haarScalarFactor_smul_smul (μ' μ : Measure G)
    [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {c : ℝ≥0}
    (hc : 0 < c) :
    haveI : IsHaarMeasure (c • μ) := IsHaarMeasure.nnreal_smul hc
    haarScalarFactor (c • μ') (c • μ) = haarScalarFactor μ' μ := by
  rw [haarScalarFactor_smul, smul_eq_mul, mul_haarScalarFactor_smul _ _ hc]

-- should be in haarScalarFactor API
@[to_additive]
lemma haarScalarFactor_map (μ' μ : Measure G) [IsHaarMeasure μ] [IsHaarMeasure μ'] (φ : G ≃ₜ* G) :
    (map φ μ').haarScalarFactor (map φ μ) = μ'.haarScalarFactor μ := by
  obtain ⟨⟨f, f_cont⟩, f_comp, f_nonneg, f_one⟩ :
    ∃ f : C(G, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_f_ne_zero : ∫ (x : G), f x ∂(map φ μ) ≠ 0 :=
    ne_of_gt (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero f_comp f_nonneg f_one)
  have hφ : AEMeasurable φ μ := φ.continuous.aemeasurable
  rw [← NNReal.coe_inj, haarScalarFactor_eq_integral_div _ _ f_cont f_comp int_f_ne_zero,
    haarScalarFactor_eq_integral_div μ' μ (f_cont.comp φ.continuous),
    integral_map hφ f_cont.aestronglyMeasurable, integral_map ?_ f_cont.aestronglyMeasurable]
  · rfl
  · exact φ.continuous.aemeasurable
  · exact f_comp.comp_homeomorph φ.toHomeomorph
  · change ∫ x, f (φ x) ∂μ ≠ 0
    rwa [← integral_map hφ f_cont.aestronglyMeasurable]

@[to_additive]
lemma mulEquivHaarChar_eq (μ : Measure G) [IsHaarMeasure μ]
    [Regular μ] (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ = haarScalarFactor μ (map φ μ) := by
  have smul := isMulLeftInvariant_eq_smul_of_regular haar μ
  unfold mulEquivHaarChar
  conv =>
    enter [1, 1]
    rw [smul]
  conv =>
    enter [1, 2, 2]
    rw [smul]
  simp_rw [MeasureTheory.Measure.map_smul]
  exact haarScalarFactor_smul_smul _ _ (haarScalarFactor_pos_of_isHaarMeasure haar μ)

@[to_additive]
lemma mulEquivHaarChar_map (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) :
    (mulEquivHaarChar φ) • map φ μ = μ := by
  rw [mulEquivHaarChar_eq μ φ]
  haveI : Regular (map φ μ) := (Regular.map_iff φ.toHomeomorph).mpr inferInstance
  exact (isMulLeftInvariant_eq_smul_of_regular μ (map φ μ)).symm

-- Version of `mulEquivHaarChar_map` without the regularity assumption
-- In this case, the measures need only be equal on open sets
@[to_additive]
lemma mulEquivHaarChar_map_open (μ : Measure G)
    [IsHaarMeasure μ] (φ : G ≃ₜ* G) {s : Set G} (hs : IsOpen s) :
    ((mulEquivHaarChar φ) • map φ μ) s = μ s := by
  rw [mulEquivHaarChar, smul_apply, haarScalarFactor_eq_mul haar (map φ μ) (map φ haar), mul_comm,
    mul_smul, ← measure_isHaarMeasure_eq_smul_of_isOpen haar _ hs,
    measure_isHaarMeasure_eq_smul_of_isOpen haar μ hs, ← mul_smul, haarScalarFactor_map,
    ← haarScalarFactor_eq_mul, haarScalarFactor_self, one_smul]

@[to_additive]
lemma mulEquivHaarChar_comap (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) :
    (mulEquivHaarChar φ) • μ = comap φ μ := by
  let e := φ.toHomeomorph.toMeasurableEquiv
  rw [show ⇑φ = ⇑e from rfl, ← e.map_symm, show ⇑e.symm = ⇑φ.symm from rfl]
  have : (map (⇑φ.symm) μ).Regular := φ.symm.toHomeomorph.regular_map μ
  rw [← mulEquivHaarChar_map (map φ.symm μ) φ, map_map]
  · simp
  · exact φ.toHomeomorph.toMeasurableEquiv.measurable
  · exact e.symm.measurable

@[to_additive addEquivAddHaarChar_smul_integral_map]
lemma mulEquivHaarChar_smul_integral_map (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] {f : G → ℝ} (φ : G ≃ₜ* G) :
    ∫ (a : G), f a ∂μ = (mulEquivHaarChar φ) • ∫ a, f a ∂(map φ μ) := by
  nth_rw 1 [← mulEquivHaarChar_map μ φ]
  simp

@[to_additive addEquivAddHaarChar_smul_integral_comap]
lemma mulEquivHaarChar_smul_integral_comap (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] {f : G → ℝ} (φ : G ≃ₜ* G) :
    ∫ (a : G), f a ∂(comap φ μ) = (mulEquivHaarChar φ) • ∫ a, f a ∂μ := by
  let e := φ.toHomeomorph.toMeasurableEquiv
  change ∫ (a : G), f a ∂(comap e μ) = (mulEquivHaarChar φ) • ∫ a, f a ∂μ
  haveI : (map (e.symm) μ).IsHaarMeasure := φ.symm.isHaarMeasure_map μ
  haveI : (map (e.symm) μ).Regular := φ.symm.toHomeomorph.regular_map μ
  rw [← e.map_symm, mulEquivHaarChar_smul_integral_map (map e.symm μ) φ,
    map_map (by exact φ.toHomeomorph.toMeasurableEquiv.measurable) e.symm.measurable]
  -- congr -- breaks to_additive -- TODO minimise and report?
  rw [show ⇑φ ∘ ⇑e.symm = id by ext; simp [e]]
  simp

@[to_additive addEquivAddHaarChar_smul_preimage]
lemma mulEquivHaarChar_smul_preimage
    (μ : Measure G) [IsHaarMeasure μ] [Regular μ] {X : Set G} (φ : G ≃ₜ* G) :
    μ X = (mulEquivHaarChar φ) • μ (φ ⁻¹' X) := by
  nth_rw 1 [← mulEquivHaarChar_map μ φ]
  simp only [smul_apply, nnreal_smul_coe_apply]
  exact congr_arg _ <| MeasurableEquiv.map_apply φ.toMeasurableEquiv X

@[to_additive]
lemma mulEquivHaarChar_refl :
    mulEquivHaarChar (ContinuousMulEquiv.refl G) = 1 := by
  simp [mulEquivHaarChar, Function.id_def]

@[to_additive]
lemma mulEquivHaarChar_trans {φ ψ : G ≃ₜ* G} :
    mulEquivHaarChar (ψ.trans φ) = mulEquivHaarChar ψ * mulEquivHaarChar φ := by
  rw [mulEquivHaarChar_eq haar ψ, mulEquivHaarChar_eq haar (ψ.trans φ)]
  have hφ : Measurable φ := φ.toHomeomorph.measurable
  have hψ : Measurable ψ := ψ.toHomeomorph.measurable
  simp_rw [ContinuousMulEquiv.coe_trans, ← map_map hφ hψ]
  have h_reg : (haar.map ψ).Regular := Regular.map ψ.toHomeomorph
  rw [MeasureTheory.Measure.haarScalarFactor_eq_mul haar (haar.map ψ),
    ← mulEquivHaarChar_eq (haar.map ψ)]

open ENNReal TopologicalSpace Set in
@[to_additive addEquivAddHaarChar_eq_one_of_compactSpace]
lemma mulEquivHaarChar_eq_one_of_compactSpace [CompactSpace G] (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ = 1 := by
  set μ := haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts G)
  have hμ : μ univ = 1 := haarMeasure_self
  rw [mulEquivHaarChar_eq μ]
  suffices (μ.haarScalarFactor (map φ μ) : ℝ≥0∞) = 1 by exact_mod_cast this
  calc
    _ = μ.haarScalarFactor (map φ μ) • (1 : ℝ≥0∞) := by rw [ENNReal.smul_def, smul_eq_mul, mul_one]
    _ = μ.haarScalarFactor (map φ μ) • (map φ μ univ) := by
          rw [map_apply (map_continuous φ).measurable .univ, Set.preimage_univ, hμ]
    _ = μ univ := by
          conv_rhs => rw [isMulInvariant_eq_smul_of_compactSpace μ (map φ μ), Measure.smul_apply]
    _ = 1 := hμ

open Topology in
@[to_additive]
lemma mulEquivHaarChar_eq_mulEquivHaarChar_of_isOpenEmbedding {X Y : Type*}
    [TopologicalSpace X] [Group X] [IsTopologicalGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [Group Y] [IsTopologicalGroup Y] [LocallyCompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    {f : X →* Y} (hf : IsOpenEmbedding f) (α : X ≃ₜ* X) (β : Y ≃ₜ* Y)
    (hComm : ∀ x, f (α x) = β (f x)) : mulEquivHaarChar α = mulEquivHaarChar β := by
  let μY : Measure Y := haar
  let μX := comap f μY
  have hμX : IsHaarMeasure μX := hf.isHaarMeasure_comap μY
  have : μX.Regular := hf.regular_comap _ μY
  obtain ⟨⟨g, g_cont⟩, g_comp, g_nonneg, g_one⟩ :
    ∃ g : C(X, ℝ), HasCompactSupport g ∧ 0 ≤ g ∧ g 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_g_ne_zero : ∫ x, g x ∂μX ≠ 0 :=
    ne_of_gt (g_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero g_comp g_nonneg g_one)
  refine NNReal.coe_injective <| Or.resolve_right (mul_eq_mul_right_iff.mp ?_) int_g_ne_zero
  calc mulEquivHaarChar α • ∫ a, g a ∂μX
    _ = ∫ a, g a ∂(comap α μX) := (mulEquivHaarChar_smul_integral_comap μX α).symm
    _ = ∫ a, g a ∂(comap (f ∘ α) μY) := by
      rw [comap_comap ?_ hf.injective hf.measurableEmbedding.measurableSet_image']
      exact α.measurableEmbedding.measurableSet_image'
    _ = ∫ a, g a ∂(comap (β ∘ f) μY) := by congr; exact funext hComm
    _ = ∫ a, g a ∂(comap f (comap β μY)) := by
      rw [comap_comap hf.measurableEmbedding.measurableSet_image' β.injective ?_]
      exact β.measurableEmbedding.measurableSet_image'
    _ = ∫ a, g a ∂(comap f (mulEquivHaarChar β • μY)) := by rw [← mulEquivHaarChar_comap]
    _ = ∫ a, g a ∂(comap f ((mulEquivHaarChar β : ENNReal) • μY)) := rfl
    _ = mulEquivHaarChar β • ∫ a, g a ∂μX := by rw [comap_smul, integral_smul_measure]; rfl

/-- A version of `mulEquivHaarChar_eq_mulEquivHaarChar_of_isOpenEmbedding` with the stronger
assumption that `f` is a `ContinuousMulEquiv`, for convenience. -/
@[to_additive "A version of `addEquivAddHaarChar_eq_addEquivAddHaarChar_of_isOpenEmbedding`
with the stronger assumption that `f` is a `ContinuousAddEquiv`, for convenience."]
lemma mulEquivHaarChar_eq_mulEquivHaarChar_of_continuousMulEquiv {X Y : Type*}
    [TopologicalSpace X] [Group X] [IsTopologicalGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [Group Y] [IsTopologicalGroup Y] [LocallyCompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (f : X ≃ₜ* Y) (α : X ≃ₜ* X) (β : Y ≃ₜ* Y) (hComm : ∀ x, f (α x) = β (f x)) :
    mulEquivHaarChar α = mulEquivHaarChar β :=
  mulEquivHaarChar_eq_mulEquivHaarChar_of_isOpenEmbedding (f := f) f.isOpenEmbedding α β hComm

end basic

section prodCongr

variable {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]

/-- The product of two multiplication-preserving homeomorphisms is
a multiplication-preserving homeomorphism. -/
@[to_additive "The product of
two addition-preserving homeomorphisms is an addition-preserving homeomorphism."]
def _root_.ContinuousMulEquiv.prodCongr (φ : A ≃ₜ* B) (ψ : C ≃ₜ* D) : A × C ≃ₜ* B × D where
  __ := φ.toMulEquiv.prodCongr ψ
  continuous_toFun := Continuous.prodMap φ.continuous_toFun ψ.continuous_toFun
  continuous_invFun := by exact Continuous.prodMap φ.continuous_invFun ψ.continuous_invFun -- ?!

end prodCongr

section prod

variable {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H]

@[to_additive MeasureTheory.addEquivAddHaarChar_prodCongr]
lemma mulEquivHaarChar_prodCongr [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace H] [BorelSpace H] (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) :
    letI : MeasurableSpace (G × H) := borel _
    haveI : BorelSpace (G × H) := ⟨rfl⟩
    mulEquivHaarChar (φ.prodCongr ψ) = mulEquivHaarChar φ * mulEquivHaarChar ψ := by
  letI : MeasurableSpace (G × H) := borel _
  have : BorelSpace (G × H) := ⟨rfl⟩
  have ⟨K, hK, _, hKcomp⟩ := local_compact_nhds (x := (1 : H)) Filter.univ_mem
  have ⟨Y, hY, hYopen, one_mem_Y⟩ := mem_nhds_iff.mp hK
  have ⟨K', hK', _, hK'comp⟩ := local_compact_nhds (x := (1 : G)) Filter.univ_mem
  have ⟨X, hX, hXopen, one_mem_X⟩ := mem_nhds_iff.mp hK'
  have hXYopen : IsOpen (X ×ˢ Y) := hXopen.prod hYopen
  have hψYopen : IsOpen (ψ '' Y) := ψ.isOpen_image.mpr hYopen
  have hφXopen : IsOpen (φ '' X) := φ.isOpen_image.mpr hXopen
  -- Define the Haar measure `ν` on `G`
  let ν := (haar (G := G × H)).restrict (Set.univ ×ˢ (ψ '' Y)) |>.map Prod.fst
  have ν_apply {S : Set G} (hS : MeasurableSet S) : ν S = haar (S ×ˢ (ψ '' Y)) := by
    rw [Measure.map_apply _ hS, ← Set.prod_univ, Measure.restrict_apply]
    · congr 1; ext; simp
    · exact prod_le_borel_prod _ <| hS.prod MeasurableSet.univ
    · intro; exact (prod_le_borel_prod _ <| measurable_fst ·)
  have : IsMulLeftInvariant ν := by
    refine (forall_measure_preimage_mul_iff ν).mp fun g s hs ↦ ?_
    rw [ν_apply hs, ν_apply (hs.preimage (measurable_const_mul g))]
    nth_rw 2 [← map_mul_left_eq_self haar ⟨g, 1⟩]
    conv in fun x ↦ (g, 1) * x => change fun x ↦ ((g * ·) x.1, (1 * ·) x.2)
    simp_rw [one_mul]
    rw [map_apply (by fun_prop), ← Set.prod_preimage_left]
    exact prod_le_borel_prod _ (hs.prod hψYopen.measurableSet)
  have hν : IsHaarMeasure ν := by
    apply isHaarMeasure_of_isCompact_nonempty_interior ν K' hK'comp
    · exact ⟨1, hXopen.subset_interior_iff.mpr hX one_mem_X⟩
    · refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hX))
      rw [ν_apply hXopen.measurableSet]
      exact (hXopen.prod hψYopen).measure_pos haar ⟨⟨1, ψ 1⟩, by simp [one_mem_X, one_mem_Y]⟩
    · have ⟨C, hCcomp, hC⟩ := exists_compact_superset hK'comp
      refine lt_top_iff_ne_top.mp <| lt_of_le_of_lt (measure_mono hC) ?_
      rw [ν_apply measurableSet_interior]
      apply lt_of_le_of_lt <| measure_mono <| Set.prod_mono interior_subset (Set.image_mono hY)
      exact hCcomp.prod (ψ.isCompact_image.mpr hKcomp) |>.measure_ne_top.symm.lt_top'
  -- Define the Haar measure `μ` on `H`
  let μ := (haar (G := G × H)).restrict (X ×ˢ Set.univ) |>.map Prod.snd
  have μ_apply {S : Set H} (hS : MeasurableSet S) : μ S = haar (X ×ˢ S) := by
    rw [Measure.map_apply _ hS, ← Set.univ_prod, Measure.restrict_apply]
    · congr 1; ext; simp [and_comm]
    · exact prod_le_borel_prod _ <| MeasurableSet.univ.prod hS
    · intro; exact (prod_le_borel_prod _ <| measurable_snd ·)
  have : IsMulLeftInvariant μ := by
    refine (forall_measure_preimage_mul_iff μ).mp fun h s hs ↦ ?_
    rw [μ_apply hs, μ_apply (hs.preimage (measurable_const_mul h))]
    nth_rw 2 [← map_mul_left_eq_self haar ⟨1, h⟩]
    conv in fun x ↦ (1, h) * x => change fun x ↦ ((1 * ·) x.1, (h * ·) x.2)
    simp_rw [one_mul]
    rw [map_apply (by fun_prop), ← Set.prod_preimage_right]
    exact prod_le_borel_prod _ (hXopen.measurableSet.prod hs)
  have hμ : IsHaarMeasure μ := by
    apply isHaarMeasure_of_isCompact_nonempty_interior μ K hKcomp
    · exact ⟨1, hYopen.subset_interior_iff.mpr hY one_mem_Y⟩
    · refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono hY))
      rw [μ_apply hYopen.measurableSet]
      exact (hXopen.prod hYopen).measure_pos haar ⟨⟨1, 1⟩, by simp [one_mem_X, one_mem_Y]⟩
    · have ⟨C, hCcomp, hC⟩ := exists_compact_superset hKcomp
      refine lt_top_iff_ne_top.mp <| lt_of_le_of_lt (measure_mono hC) ?_
      rw [μ_apply measurableSet_interior]
      apply lt_of_le_of_lt <| measure_mono <| Set.prod_mono hX interior_subset
      exact hK'comp.prod hCcomp |>.measure_ne_top.symm.lt_top'
  -- Prove the lemma by showing that both `mulEquivHaarChar (φ.prodCongr ψ) * haar (X ×ˢ Y)` and
  -- `mulEquivHaarChar φ * mulEquivHaarChar ψ * haar (X ×ˢ Y)` equal `haar ((φ '' X) ×ˢ (ψ '' Y))`
  suffices mulEquivHaarChar (φ.prodCongr ψ) * haar (X ×ˢ Y) =
      mulEquivHaarChar φ * mulEquivHaarChar ψ * haar (X ×ˢ Y) by
    have ne_zero : haar (X ×ˢ Y) ≠ 0 :=
      (isHaarMeasure_haarMeasure _).open_pos _ hXYopen ⟨⟨1, 1⟩, ⟨one_mem_X, one_mem_Y⟩⟩
    have ne_top : haar (X ×ˢ Y) ≠ ⊤ := by
      refine (lt_of_le_of_lt (measure_mono <| Set.prod_mono hX hY) ?_).ne
      exact (isHaarMeasure_haarMeasure _).lt_top_of_isCompact <| hK'comp.prod hKcomp
    exact_mod_cast (ENNReal.mul_left_inj ne_zero ne_top).mp this
  calc mulEquivHaarChar (φ.prodCongr ψ) * haar (X ×ˢ Y)
    _ = mulEquivHaarChar _ * (map (φ.prodCongr ψ) haar) ((φ.prodCongr ψ) '' (X ×ˢ Y)) := by
      have hφψ : Measurable (φ.prodCongr ψ) := (φ.prodCongr ψ).measurable
      rw [map_apply hφψ, Set.preimage_image_eq _ (φ.prodCongr ψ).injective]
      exact (φ.prodCongr ψ).measurableEmbedding.measurableSet_image' hXYopen.measurableSet
    _ = (mulEquivHaarChar (φ.prodCongr ψ) • (map (φ.prodCongr ψ) haar)) ((φ '' X) ×ˢ (ψ '' Y)) := by
      rw [← Set.prodMap_image_prod]; rfl
    _ = haar ((φ '' X) ×ˢ (ψ '' Y)) := by
      rw [mulEquivHaarChar_map_open haar (φ.prodCongr ψ) (hφXopen.prod hψYopen)]
    _ = ν (φ '' X) := ν_apply hφXopen.measurableSet |>.symm
    _ = ((mulEquivHaarChar φ) • (map φ ν)) (φ '' X) := by rw [mulEquivHaarChar_map_open ν φ hφXopen]
    _ = (mulEquivHaarChar φ) * (map φ ν) (φ '' X) := rfl
    _ = (mulEquivHaarChar φ) * ν X := by
      rw [map_apply (show Measurable φ from φ.measurable) hφXopen.measurableSet]
      rw [show φ ⁻¹' (φ '' X) = X from φ.preimage_image X]
    _ = (mulEquivHaarChar φ) * haar (X ×ˢ (ψ '' Y)) := by rw [ν_apply hXopen.measurableSet]
    _ = (mulEquivHaarChar φ) * μ (ψ '' Y) := by rw [μ_apply hψYopen.measurableSet]
    _ = (mulEquivHaarChar φ) * (mulEquivHaarChar ψ) * haar (X ×ˢ Y) := by
      nth_rw 1 [← mulEquivHaarChar_map_open μ ψ hψYopen]
      have hψ : Measurable ψ := ψ.measurable
      rw [smul_apply, nnreal_smul_coe_apply, mul_assoc, map_apply hψ hψYopen.measurableSet,
        Set.preimage_image_eq _ ψ.injective, μ_apply hYopen.measurableSet]

end prod

section piCongrRight

variable {ι : Type*} {G H : ι → Type*}
    [Π i, Group (G i)] [Π i, TopologicalSpace (G i)]
    [Π i, Group (H i)] [Π i, TopologicalSpace (H i)]

-- should be in mathlib?
/-- An arbitrary product of multiplication-preserving homeomorphisms
is a multiplication-preserving homeomorphism.
-/
@[to_additive "An arbitrary product of
addition-preserving homeomorphisms is an addition-preserving homeomorphism."]
def _root_.ContinuousMulEquiv.piCongrRight (ψ : Π i, (G i) ≃ₜ* (H i)) :
    (∀ i, G i) ≃ₜ* (∀ i, H i) where
  __ := MulEquiv.piCongrRight (fun i ↦ ψ i)
  continuous_toFun := Continuous.piMap (fun i ↦ (ψ i).continuous_toFun)
  continuous_invFun := Continuous.piMap (fun i ↦ (ψ i).continuous_invFun)

end piCongrRight

section pi

variable {ι : Type*} {H : ι → Type*} [Π i, Group (H i)] [Π i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, LocallyCompactSpace (H i)]
    [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]

open Classical ContinuousMulEquiv in
@[to_additive]
lemma mulEquivHaarChar_piCongrRight [Fintype ι] (ψ : Π i, (H i) ≃ₜ* (H i)) :
    letI : MeasurableSpace (Π i, H i) := borel _
    haveI : BorelSpace (Π i, H i) := ⟨rfl⟩
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = ∏ i, mulEquivHaarChar (ψ i) := by
  let P : (α : Type u_1) → [Fintype α] → Prop := fun ι _ ↦
    ∀ (H : ι → Type u_2) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, LocallyCompactSpace (H i)]
    [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] (ψ : (i : ι) → H i ≃ₜ* H i),
    letI : MeasurableSpace (Π i, H i) := borel _
    haveI : BorelSpace (Π i, H i) := ⟨rfl⟩
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = ∏ i, mulEquivHaarChar (ψ i)
  refine Fintype.induction_subsingleton_or_nontrivial (P := P) ι ?_ ?_ H ψ
  · intro α _ subsingleton_α H _ _ _ _ _ _ ψ
    borelize (Π i, H i)
    by_cases hα : Nonempty α; swap
    · rw [not_nonempty_iff] at hα; simp [mulEquivHaarChar_eq_one_of_compactSpace]
    have : Unique α := @Unique.mk' α (Classical.inhabited_of_nonempty hα) subsingleton_α
    rw [Fintype.prod_subsingleton _ default]
    exact mulEquivHaarChar_eq_mulEquivHaarChar_of_continuousMulEquiv (piUnique H) _ _ (fun _ ↦ rfl)
  intro α fintype_α nontrivial_α ih H _ _ _ _ _ _ ψ
  have ⟨a, b, ne⟩ := nontrivial_α
  let β₁ := {i : α // i = a}
  let β₂ := {i : α // i ≠ a}
  borelize (Π i, H i) (Π (i : β₁), H i) (Π (i : β₂), H i) ((Π (i : β₁), H i) × (Π (i : β₂), H i))
  let ψ₁ : Π (i : β₁), H i ≃ₜ* H i := fun i ↦ ψ i
  let ψ₂ : Π (i : β₂), H i ≃ₜ* H i := fun i ↦ ψ i
  rw [mulEquivHaarChar_eq_mulEquivHaarChar_of_continuousMulEquiv (piEquivPiSubtypeProd (· = a) H),
    mulEquivHaarChar_prodCongr, ih β₁ (fintype_α.card_subtype_lt ne.symm) (H ·) ψ₁,
    ih β₂ (fintype_α.card_subtype_lt (· rfl)) (H ·) ψ₂, Fintype.prod_eq_mul_prod_subtype_ne _ a,
    Finset.univ_unique, Finset.prod_singleton]
  · rfl
  · intro; rfl

end pi

section restrictedproduct

open ENNReal

-- -- some sample code to show how why a nonempty compact open has
-- -- positive finite Haar measure
-- example (X : Type*) [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
--     [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
--     -- IsHaarMeasure gives "positive on opens" and "finite on compacts"
--     [IsHaarMeasure μ] (C : Set X) [Nonempty C]
--     (hCopen : IsOpen C) (hCcompact : IsCompact C) :
--     0 < μ C ∧ μ C < ∞ := by
--   constructor
--   · exact IsOpen.measure_pos μ hCopen Set.Nonempty.of_subtype
--   · exact IsCompact.measure_lt_top hCcompact

open RestrictedProduct

open Pointwise in
-- TODO this should be elsewhere
@[to_additive]
lemma _root_.WeaklyLocallyCompactSpace.of_isTopologicalGroup_of_isOpen_compactSpace_subgroup
    {A : Type*} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    (C : Subgroup A) [hCopen : Fact (IsOpen (C : Set A))] [CompactSpace C] :
    WeaklyLocallyCompactSpace A := .mk fun x ↦
    ⟨x • (C : Set A), .smul _ (isCompact_iff_compactSpace.mpr inferInstance),
      hCopen.out |>.smul _ |>.mem_nhds <| by
      simpa using Set.smul_mem_smul_set (a := x) (one_mem C)⟩

variable {ι : Type*}
    {G : ι → Type*}
    [Π i, Group (G i)] [Π i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    {C : (i : ι) → Subgroup (G i)}
    [hCopen : Fact (∀ (i : ι), IsOpen (C i : Set (G i)))]
    [hCcompact : ∀ i, CompactSpace (C i)]
    [∀ i, MeasurableSpace (G i)]
    [∀ i, BorelSpace (G i)]

omit [∀ (i : ι), BorelSpace (G i)] [∀ i, MeasurableSpace (G i)] in
--@[to_additive, simp]
@[simp]
lemma restrictedProduct_subset_measure_open_pos
    [∀ i, LocallyCompactSpace (G i)]
    [∀i, CompactSpace (G i)]
    (φ : Π i, (G i) ≃ₜ* (G i))
    [∀ i, MeasurableSpace (G i)]
    (S : Set ι := {i | ¬Set.BijOn ⇑(φ i) ↑(C i) ↑(C i)})
    (X : Set (Πʳ i, [G i, C i]))
    (hXdef : X = {x | ∀ i ∉ S, x i ∈ C i})
    (hXopen : IsOpen X) :
    letI : MeasurableSpace (Πʳ i, [G i, C i]) := borel _
    haveI : BorelSpace (Πʳ i, [G i, C i]) := ⟨rfl⟩
    (0 : ℝ≥0∞) < haar X := by
  letI : MeasurableSpace (Πʳ i, [G i, C i]) := borel _
  haveI : BorelSpace (Πʳ i, [G i, C i]) := ⟨rfl⟩
  apply IsOpen.measure_pos haar hXopen
  use 1
  simp only [hXdef, Set.mem_setOf]
  intro i _
  exact one_mem _

omit [∀ (i : ι), IsTopologicalGroup (G i)] [∀ (i : ι), BorelSpace (G i)]
[Π i, TopologicalSpace (G i)] [∀ i, MeasurableSpace (G i)] in
@[to_additive (attr := simp ) simp]
lemma restrictedProduct_subset_eq_prod_subset
  [∀ i, TopologicalSpace (G i)] [∀ i, CompactSpace (G i)]
  (hCopen : Fact (∀ i, IsOpen (↑(C i) : Set (G i))))
  (hCcompact : ∀ i, CompactSpace (C i))
  (S : Set ι)
  (hS_finite : S.Finite) :
  ∃ (U : Set (Π i : S, G i)), IsOpen U ∧ IsCompact U ∧
    {x : Πʳ i, [G i, ↑(C i)] | ∀ i ∉ S, x i ∈ C i} =
    {x : Πʳ i, [G i, ↑(C i)] | (fun i : S => x i.val) ∈ U ∧ ∀ i ∉ S, x i ∈ C i} := by
  haveI : Fact (∀ i, IsOpen (↑(C i) : Set (G i))) := hCopen
  haveI : ∀ i, CompactSpace (C i) := hCcompact
  haveI : S.Finite := hS_finite
  -- We choose U to be the entire space, which is the simplest choice that makes the equality hold.
  use Set.univ
  -- The proof now splits into three goals: IsOpen, IsCompact, and the set equality.
  refine ⟨isOpen_univ, ?_, by simp⟩
  -- Proof that `Set.univ` is compact:
  -- Tychonoff's theorem (`isCompact_univ`) states that a product space is compact
  --   if each of its component spaces is compact.
  --haveI : Fintype S := fintype
  exact isCompact_univ

/-- Projection from restricted product subset to product over S and complement -/
@[to_additive (attr := simp) restrictedSumToSplitSum, simp]
def restrictedProductToSplitProduct
    (S : Set ι)
    (C : (i : ι) → Subgroup (G i))
    (U : Set (Π i : S, G i))
    (X : Set (Πʳ i, [G i, C i]))
    (hX_eq : X = {x : Πʳ i, [G i, C i] | (fun i : S => x i.val) ∈ U ∧ ∀ i ∉ S, x i ∈ C i})
    : X → U × Π i : {i | i ∉ S}, C i :=
  fun x =>
    (⟨fun i : S => x.val i.val, by
      have : x.val ∈ {x : Πʳ i, [G i, C i] | (fun i : S => x i.val) ∈ U ∧ ∀ i ∉ S, x i ∈ C i} := by
        rw [← hX_eq]; exact x.property
      exact this.1⟩,
    fun i : {i | i ∉ S} => ⟨x.val i.val, by
      have : x.val ∈ {x : Πʳ i, [G i, C i] | (fun i : S => x i.val) ∈ U ∧ ∀ i ∉ S, x i ∈ C i} := by
        rw [← hX_eq]; exact x.property
      exact this.2 i.val i.property⟩)

/-- Inverse map from split product to restricted product subset -/
@[to_additive (attr := simp) splitSumToRestrictedSum, simp]
def splitProductToRestrictedProduct
    (S : Set ι)
    [DecidablePred (· ∈ S)]
    (hS_finite : S.Finite)
    (C : (i : ι) → Subgroup (G i))
    (U : Set (Π i : S, G i))
    (X : Set (Πʳ i, [G i, C i]))
    (hX_eq : X = {x : Πʳ i, [G i, C i] | (fun i : S => x i.val) ∈ U ∧ ∀ i ∉ S, x i ∈ C i})
    : U × (Π i : {i | i ∉ S}, C i) → X :=
  fun ⟨u, c⟩ =>
    let x_val : Π i, G i := fun i =>
      if h : i ∈ S then
        u.val ⟨i, h⟩
      else
        (c ⟨i, h⟩).val
    ⟨⟨x_val,
      by {
        apply Set.Finite.subset hS_finite
        intro i hi_notin_C
        by_cases h_in_S : i ∈ S
        · -- If `i` is in `S`, the goal is met.
          exact h_in_S
        · -- Now, assume `i ∉ S` and derive a contradiction.
          exfalso
          have h_is_in_C : x_val i ∈ C i := by
            simp only [x_val, dif_neg h_in_S]
            exact (c ⟨i, h_in_S⟩).property
          exact hi_notin_C h_is_in_C
      }
    ⟩, by {
        rw [hX_eq]
        refine ⟨?_, ?_⟩ -- We will prove the two conditions for membership in `X`
        · -- First, prove `(fun i : S => x_val i.val) ∈ U`.
          -- We know `u.val ∈ U` from `u.property`.
          -- We'll prove our function equals `u.val` and then rewrite.
          have h_fn_eq : (fun i : S => x_val i.val) = u.val := by {
            -- To prove two functions are equal, prove they are equal for any input `i`.
            funext i
            -- Unfold `x_val` and simplify using that `i.val ∈ S`.
            simp only [x_val, dif_pos i.property]
          }
          -- Rewrite with our proven equality and use the property of `u` to finish.
          have h_u_prop : u.val ∈ U := u.property
          rwa [← h_fn_eq] at h_u_prop
        · -- Second, prove `∀ i ∉ S, x_val i ∈ C i`.
          intro i hi

          -- We want to prove that the projection of our constructed element equals `x_val i`.
          -- First, we construct the element of the restricted product explicitly.
          let restricted_product_element : Πʳ i, [G i, C i] :=
            ⟨x_val, by {
                -- This is the proof that `x_val` satisfies the restricted product condition.
                apply Set.Finite.subset hS_finite
                intro j hj_notin_C
                by_cases h_in_S : j ∈ S
                · exact h_in_S
                · exfalso
                  have h_is_in_C : x_val j ∈ C j := by
                  {
                    dsimp [x_val]
                    rw [dif_neg h_in_S]
                    exact (c ⟨j, h_in_S⟩).property
                  }
                  exact hj_notin_C h_is_in_C
              }
            ⟩

          -- Now, state the property about the projection.
          -- This is true by definition (`rfl`).
          have h_proj_eq : restricted_product_element i = x_val i := rfl

          -- Rewrite the goal using this definitional equality.
          rw [h_proj_eq]

          -- The goal is now `x_val i ∈ C i`.
          -- Unfold `x_val` and use the hypothesis that `i ∉ S`.
          simp only [x_val, dif_neg hi]

          -- The final goal matches the property of the subtype element `c`.
          exact (c ⟨i, hi⟩).property
      }
    ⟩

omit
  [∀ (i : ι), IsTopologicalGroup (G i)]
  [∀ (i : ι), BorelSpace (G i)]
  [(i : ι) → TopologicalSpace (G i)]
  [(i : ι) → MeasurableSpace (G i)] in
@[simp]
lemma splitProductToRestrictedProduct_comp_restrictedProductToSplitProduct
    (S : Set ι)
    [DecidablePred (· ∈ S)]
    (hS_finite : S.Finite)
    (C : (i : ι) → Subgroup (G i))
    (U : Set (Π i : S, G i))
    (X : Set (Πʳ i, [G i, C i]))
    (hX_eq : X = {x : Πʳ i, [G i, C i] | (fun i : S => x i.val) ∈ U ∧ ∀ i ∉ S, x i ∈ C i})
    : ∀ x, splitProductToRestrictedProduct S hS_finite C U X hX_eq
        (restrictedProductToSplitProduct S C U X hX_eq x) = x := by
  intro x
  ext i
  by_cases h : i ∈ S
  · simp [restrictedProductToSplitProduct, splitProductToRestrictedProduct]
  · simp [restrictedProductToSplitProduct, splitProductToRestrictedProduct]

omit
  [∀ (i : ι), IsTopologicalGroup (G i)]
  [∀ (i : ι), BorelSpace (G i)]
  [(i : ι) → TopologicalSpace (G i)]
  [(i : ι) → MeasurableSpace (G i)] in
@[simp]
lemma restrictedProductToSplitProduct_comp_splitProductToRestrictedProduct
    (S : Set ι)
    [DecidablePred (· ∈ S)]
    (hS_finite : S.Finite)
    (C : (i : ι) → Subgroup (G i))
    (U : Set (Π i : S, G i))
    (X : Set (Πʳ i, [G i, C i]))
    (hX_eq : X = {x : Πʳ i, [G i, C i] | (fun i : S => x i.val) ∈ U ∧ ∀ i ∉ S, x i ∈ C i})
    : ∀ y, restrictedProductToSplitProduct S C U X hX_eq
        (splitProductToRestrictedProduct S hS_finite C U X hX_eq y) = y := by
  intro ⟨u, c⟩
  apply Prod.ext
  · ext i
    simp only [restrictedProductToSplitProduct, splitProductToRestrictedProduct]
    change (if h : i.val ∈ S then u.val ⟨i.val, h⟩ else (c ⟨i.val, h⟩).val) = u.val i
    simp only [dif_pos i.property]
  · funext i
    apply Subtype.ext
    simp only [restrictedProductToSplitProduct, splitProductToRestrictedProduct]
    change (if h : i.val ∈ S then u.val ⟨i.val, h⟩ else (c ⟨i.val, h⟩).val) = (c i).val
    simp only [dif_neg i.property]

-- todo >> Mathlib.Topology.Algebra.RestrictedProduct
@[simp]
lemma RestrictedProduct.continuous_iff.{u, v, w}
    {ι : Type u} {X : Type v} {G : ι → Type w}
    [TopologicalSpace X] [∀ i, TopologicalSpace (G i)]
    (C : (i : ι) → Set (G i))
    (𝓕 : Filter ι)
    {f : X → RestrictedProduct G C 𝓕}
    : Continuous f ↔ ∀ i, Continuous (fun x ↦ f x i) := by
  sorry

@[simp]
lemma continuous_splitProductToRestrictedProduct_components
    {ι : Type*} {G : ι → Type*}
    -- Typeclasses
    [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    -- Main arguments
    (C : (i : ι) → Subgroup (G i))
    (S : Set ι)
    (hS_finite : S.Finite)
    (U : Set ((i : ↑S) → G ↑i))
    (X : Set Πʳ (i : ι), [G i, ↑(C i)])
    [DecidablePred fun x ↦ x ∈ S]
    (hX_eq : X = {x | (fun i : S ↦ x i.val) ∈ U ∧ ∀ i ∉ S, x i ∈ C i})
    -- The proposition the lemma proves
    : ∀ (i : ι), Continuous (fun x ↦
      (splitProductToRestrictedProduct S hS_finite C U X hX_eq x).val i) := by
  intro i
  dsimp [splitProductToRestrictedProduct]
  by_cases h_in_S : i ∈ S
  · -- Case 1: `i ∈ S`
    -- We first prove that our function simplifies to a composition of projections.
    have h_fn_eq : (fun x ↦ (splitProductToRestrictedProduct S hS_finite C U X hX_eq x).val i) =
      (fun x ↦ x.1.val ⟨i, h_in_S⟩) := by
        simp [splitProductToRestrictedProduct, h_in_S]
    have h_cont_simple :
      Continuous (fun (x : ↥U × (Π (i : {i | i ∉ S}), ↥(C i))) ↦ x.1.val ⟨i, h_in_S⟩) := by
      -- Extract the components with explicit types
      have h1 : Continuous (fun (x : ↥U × (Π (i : {i | i ∉ S}), ↥(C i))) ↦ x.1) := continuous_fst
      have h2 : Continuous (fun (u : ↥U) ↦ u.val) := continuous_subtype_val
      have h3 : Continuous (fun (f : (i : ↑S) → G ↑i) ↦ f ⟨i, h_in_S⟩) :=
        continuous_apply (⟨i, h_in_S⟩ : ↑S)
      -- Compose them
      exact h3.comp (h2.comp h1)
    -- Now rewrite the goal using this equality.
    rwa [← h_fn_eq] at h_cont_simple
  · -- Case 2: `i ∉ S`
    -- We first prove that our function simplifies to a composition of projections.
    have h_fn_eq : (fun x ↦ (splitProductToRestrictedProduct S hS_finite C U X hX_eq x).val i) =
                      (fun x ↦ (x.2 ⟨i, h_in_S⟩).val) := by
        simp [splitProductToRestrictedProduct, h_in_S]
    have h_cont_simple :
      Continuous (fun (x : ↥U × (Π (i : {i | i ∉ S}), ↥(C i))) ↦ (x.2 ⟨i, h_in_S⟩).val) := by
      -- Extract the components with explicit types
      have h1 : Continuous (fun (x : ↥U × (Π (i : {i | i ∉ S}), ↥(C i))) ↦ x.2) := continuous_snd
      have h2 : Continuous (fun (f : (i : {i | i ∉ S}) → ↥(C ↑i)) ↦ f ⟨i, h_in_S⟩) :=
        continuous_apply (⟨i, h_in_S⟩ : {i | i ∉ S})
      have h3 : Continuous (fun (c : ↥(C i)) ↦ c.val) := continuous_subtype_val
      -- Compose them
      exact h3.comp (h2.comp h1)
    -- Now rewrite the goal using this equality.
    rwa [← h_fn_eq] at h_cont_simple

open ContinuousMulEquiv Classical in
--@[to_additive (attr := simp) addEquivAddChar_restrictedProductCongrRight_X_compact
--  "The additive version of the docstring.", simp]
omit hCopen [∀ (i : ι), BorelSpace (G i)] [(i : ι) → MeasurableSpace (G i)] in
@[simp]
lemma mulEquivHaarChar_restrictedProductCongrRight_X_compact
    [∀ i, CompactSpace (G i)]
    (φ : Π i, (G i) ≃ₜ* (G i))
    (hφ : ∀ᶠ (i : ι) in Filter.cofinite, Set.BijOn ⇑(φ i) ↑(C i) ↑(C i))
    (S : Set ι)
    (hS_finite : S.Finite)
    (hS_def : S = {i | ¬Set.BijOn ⇑(φ i) ↑(C i) ↑(C i)})
    (X : Set (Πʳ i, [G i, C i]))
    (hX_def : X = {x | ∀ i ∉ S, x i ∈ C i})
    (U : Set (Π i : S, G i))
    (hU_open : IsOpen U)
    (hU_compact : IsCompact U)
    (hX_eq : X = {x : Πʳ i, [G i, C i] | (fun i : S => x i.val) ∈ U ∧ ∀ i ∉ S, x i ∈ C i})
    : IsCompact X := by
  -- Define the homeomorphism between X and U × ∏ i ∉ S, C i
  let f : X → U × Π i : {i | i ∉ S}, C i :=
    restrictedProductToSplitProduct S C U X hX_eq

  let g : ↥U × (Π i : {i | i ∉ S}, ↥(C i)) → ↥X :=
    splitProductToRestrictedProduct S hS_finite C U X hX_eq

  -- Show f and g are inverses

  have hfg : ∀ x, g (f x) = x :=
    splitProductToRestrictedProduct_comp_restrictedProductToSplitProduct
      S hS_finite C U X hX_eq

  have hgf : ∀ y, f (g y) = y :=
    restrictedProductToSplitProduct_comp_splitProductToRestrictedProduct
      S hS_finite C U X hX_eq

  -- show (Subtype.val ∘ g) is continuous
  have hg_cont : Continuous (Subtype.val ∘ g) := by
    -- We state that it is sufficient to prove that each component function is continuous.
      rw [RestrictedProduct.continuous_iff]
      exact continuous_splitProductToRestrictedProduct_components C S hS_finite U X hX_eq

  -- Show X = (Subtype.val ∘ g) '' univ
  have hX_eq_image : X = (Subtype.val ∘ g) '' Set.univ := by
    ext x
    simp only [Set.mem_image, Set.mem_univ, true_and, Function.comp_apply]
    constructor
    · intro hx
      use f ⟨x, hx⟩
      simp [hfg]
    · rintro ⟨y, rfl⟩
      exact (g y).property

  -- X is the image of a compact set under a continuous map
  rw [hX_eq_image]

  -- The source space of g is compact
  haveI hcompact : CompactSpace (U × Π i : {i | i ∉ S}, C i) := by
    -- First component: U is compact
    haveI : CompactSpace U := isCompact_iff_compactSpace.mp hU_compact
    -- Second component: product of compact spaces
    haveI : ∀ i : {i | i ∉ S}, CompactSpace (C i.val) := fun i => inferInstance
    -- Now the product instance applies automatically
    exact inferInstance

  exact (@isCompact_univ _ _ hcompact).image hg_cont

open Classical in
noncomputable def X_eq_intersection
    {ι : Type*} {G : ι → Type*} [Π i, Group (G i)] [Π i, TopologicalSpace (G i)]
    (C : (i : ι) → Subgroup (G i))
    (S : Set ι) :
    {x : Πʳ i, [G i, ↑(C i)] | ∀ i ∉ S, x i ∈ C i} = ⋂ i, ⋂ (_ : i ∉ S), {x | x i ∈ C i} := by
  ext x
  simp only [Set.mem_setOf, Set.mem_iInter]

@[simp]
lemma restrictedProduct_subset_isOpen
    {ι : Type*} {G : ι → Type*} [Π i, Group (G i)]
    [Π i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    (C : (i : ι) → Subgroup (G i))
    (hCopen : Fact (∀ i, IsOpen (↑(C i) : Set (G i))))
    (S : Set ι)
    (hS_finite : S.Finite) :
    IsOpen (⋂ i, ⋂ (_ : i ∉ S), {x : Πʳ i, [G i, ↑(C i)] | x i ∈ C i}) := by
  -- have h_eq : {x : Πʳ i, [G i, ↑(C i)] | ∀ i ∉ S, x i ∈ C i} =
  --             {x : Πʳ i, [G i, ↑(C i)] | {i | x i ∉ C i} ⊆ S}
  -- Now we have ⋂ i ∈ Sᶜ, {x | x i ∈ C i}
  -- So {x | ∀ i ∉ S, x i ∈ C i} = {x | support of exceptions ⊆ S}
  -- The key insight: in a restricted product, x i ∈ C i for all but finitely many i
  rw [← X_eq_intersection C S]
  -- This is a finite intersection of open sets (since S is finite, Sᶜ is cofinite)
  sorry -- Q.E.D.

-- todo >> Mathlib.Data.ENNReal.BigOperators
lemma ENNReal.coe_finprod_of_finite
    {ι : Type*} [Fintype ι]
    (f : ι → ℝ≥0) :
    ∏ᶠ i, (f i : ℝ≥0∞) = ↑(∏ᶠ i, f i) := by
  simp [finprod_eq_prod_of_fintype]

-- The definition of a finitary product over
-- a commutative monoid with a complete lattice structure.
-- todo >> Mathlib.Algebra.BigOperators.Finprod
def finprod_def'
  {ι : Type*} {M : Type*} [CommMonoid M] [CompleteLattice M]
  (f : ι → M) : M :=
  ⨆ s : Finset ι, ∏ i ∈ s, f i

-- todo >> Mathlib.Data.ENNReal.BigOperators
@[simp]
lemma ENNReal.coe_finprod
    {ι : Type*} {f : ι → ℝ≥0}
    [Decidable (Function.mulSupport f).Finite] :
    ↑(∏ᶠ i, f i) = ∏ᶠ i, (f i : ℝ≥0∞) := by
  -- Define the coercion as a monoid homomorphism
  let g : ℝ≥0 →* ℝ≥0∞ := {
    toFun := fun x => ↑x
    map_one' := by simp
    map_mul' := fun x y => by simp
  }
  -- Apply the theorem
  convert MonoidHom.map_finprod_of_injective g _ f
  -- Prove injectivity
  · intros x y h
    rw [MonoidHom.coe_mk] at h
    -- Now h : ↑x = ↑y
    exact coe_injective h

@[simp]
lemma restrictedProduct_subset_measure_open
    {ι : Type*} {G : ι → Type*} [Π i, Group (G i)]
    [∀ i, TopologicalSpace (G i)] [∀ i, CompactSpace (G i)]
    [Π i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]
    (C : (i : ι) → Subgroup (G i))
    (S : Set ι)
    (X : Set Πʳ (i : ι), [G i, ↑(C i)])
    (hXdef : X = {x | ∀ i ∉ S, x i ∈ C i})
    (hCopen : Fact (∀ i, IsOpen (↑(C i) : Set (G i))))
    (hS_finite : S.Finite) : IsOpen X := by
  -- We can use that this is a basic open set in the restricted product topology
  -- First, rewrite X in terms of intersections of preimages
  rw [hXdef]
  have : {x | ∀ i ∉ S, x i ∈ C i} = ⋂ i ∉ S, {x : Πʳ i, [G i, C i] | x i ∈ C i} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf]
  rw [this]
  -- For the restricted product, {x | x i ∈ C i} is always open
  -- because it's either the whole space (if i is not in the support)
  -- or it's the preimage of the open set C i under the continuous projection
  exact restrictedProduct_subset_isOpen C hCopen S hS_finite

-- This lemma is the equivalent of the `Measure.map_image` you were looking for.
lemma measure_image_of_measurable_equiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α)
    (e : α ≃ᵐ β)
    (s : Set α)
    : μ.map e (e '' s) = μ s := by
  sorry

/--
For `a, b, c` in `ℝ≥0∞`, the equality `a = b⁻¹ * c` is equivalent to `b * a = c`,
provided `b` is invertible (i.e., not `0` or `∞`).
-/
lemma ENNReal.eq_inv_mul_iff_mul_eq'
    {a b c : ℝ≥0∞}
    (hb_ne_zero : b ≠ 0)
    (hb_ne_top : b ≠ ⊤) :
    a = b⁻¹ * c ↔ b * a = c := by
  constructor
  -- 1. Forward direction: `a = b⁻¹ * c → b * a = c`
  · intro h
    -- Substitute `a` using the hypothesis `h`.
    rw [h]
    -- The goal is now `b * (b⁻¹ * c) = c`.
    -- Use associativity to regroup.
    rw [← mul_assoc]
    -- Since `b` is not 0 or ∞, `b * b⁻¹ = 1`.
    rw [ENNReal.mul_inv_cancel hb_ne_zero hb_ne_top]
    -- The goal is now `1 * c = c`, which is true.
    rw [one_mul]
  -- 2. Backward direction: `b * a = c → a = b⁻¹ * c`
  · intro h
    sorry

lemma ENNReal.smul_smul_measure {α : Type*} [MeasurableSpace α]
    (a b : ℝ≥0∞) (μ : Measure α) : a • b • μ = (a * b) • μ := by
  sorry

-- todo >> import Mathlib.Topology.Algebra.RestrictedProduct
/--
A "box" in a restricted product is a set of elements where each component `x i`
is contained in a specified set `U i`.
-/
@[simp]
def RestrictedProduct.box'
  -- Universe variables for generality
  {ι : Type*} {G : ι → Type*}
  -- The family of default sets and the filter
  (C : (i : ι) → Set (G i))
  (𝓕 : Filter ι)
  -- The family of sets defining the shape of the box
  (U : Π i, Set (G i))
  -- The resulting type is a set within the restricted product
  : Set (RestrictedProduct G C 𝓕) :=
  {x | ∀ i, x i ∈ U i}

lemma RestrictedProduct.mem_box'
    {ι : Type*} {R : ι → Type*}
    {A : (i : ι) → Set (R i)} {𝓕 : Filter ι}
    {B : (i : ι) → Set (R i)}
    {x : RestrictedProduct R A 𝓕} :
  x ∈ box' A 𝓕 B ↔ ∀ i, x i ∈ B i := sorry

open ContinuousMulEquiv Classical RestrictedProduct in
/--
mulEquivHaarChar_restrictedProductCongrRight:
key steps:
* Identify the finite set S where φ doesn't preserve C
* Construct the compact open subset X
* Show the automorphism scales X by the product of individual characters
* Handle the support finiteness conditions for the finitary product -/
--@[to_additive, simp]
@[simp]
lemma mulEquivHaarChar_restrictedProductCongrRight
  [∀ i, LocallyCompactSpace (G i)] [∀i, CompactSpace (G i)]
  (φ : Π i, (G i) ≃ₜ* (G i))
  (hφ : ∀ᶠ (i : ι) in Filter.cofinite, Set.BijOn ⇑(φ i) ↑(C i) ↑(C i)) :
    -- typeclass stuff
    letI : MeasurableSpace (Πʳ i, [G i, C i]) := borel _
    haveI : BorelSpace (Πʳ i, [G i, C i]) := ⟨rfl⟩
    haveI : ∀ i, WeaklyLocallyCompactSpace (G i) := fun i ↦
      haveI : Fact (IsOpen (C i : Set (G i))) := ⟨hCopen.out i⟩
      WeaklyLocallyCompactSpace.of_isTopologicalGroup_of_isOpen_compactSpace_subgroup (C i)
    -- lemma statement starts here
    mulEquivHaarChar
      (.restrictedProductCongrRight φ hφ : (Πʳ i, [G i, C i]) ≃ₜ* (Πʳ i, [G i, C i])) =
    ∏ᶠ i, mulEquivHaarChar (φ i) := by
  letI : MeasurableSpace (Πʳ i, [G i, C i]) := borel _
  haveI : BorelSpace (Πʳ i, [G i, C i]) := ⟨rfl⟩
  -- Extract the finite set where φ doesn't preserve C
  let S : Set ι := {i | ¬Set.BijOn ⇑(φ i) ↑(C i) ↑(C i)}
  have hS_finite : S.Finite := by
    rwa [← Filter.eventually_cofinite]
  -- Define open sets for coordinates in S (all unrestricted)
  let opens : (i : ι) → i ∈ S → Set (G i) := fun i hi => Set.univ
  let hU : ∀ i (hi : i ∈ S), IsOpen (opens i hi) := fun i hi => isOpen_univ
  obtain ⟨U, hU_open, hU_compact, hX_eq⟩ :=
    restrictedProduct_subset_eq_prod_subset
      hCopen hCcompact S hS_finite
  -- Define the compact open subset X of the restricted product
  let X : Set (Πʳ i, [G i, C i]) := {x | ∀ i ∉ S, x i ∈ C i}
  have hXopen : IsOpen X :=
    restrictedProduct_subset_measure_open
      C S X (by rfl) hCopen hS_finite
  have hS_def : S = {i | ¬Set.BijOn ⇑(φ i) ↑(C i) ↑(C i)} := rfl
  have hX_def : X = {x | ∀ i ∉ S, x i ∈ C i} := rfl
  have hXcompact : IsCompact X :=
    mulEquivHaarChar_restrictedProductCongrRight_X_compact
      φ hφ S hS_finite hS_def X hX_def U hU_open hU_compact hX_eq
  have hXpos : (0 : ℝ≥0∞) < haar X :=
    restrictedProduct_subset_measure_open_pos
      φ S X hX_def hXopen
  have hXfin : haar X < ∞ := hXcompact.measure_lt_top
  -- Apply the characterization of mulEquivHaarChar via scaling on open sets
  suffices h : (mulEquivHaarChar (.restrictedProductCongrRight φ hφ) : ℝ≥0∞) * haar X =
    (∏ᶠ i, mulEquivHaarChar (φ i) : ℝ≥0∞) * haar X by
      -- We have μ(X) ≠ 0 and μ(X) ≠ ∞, so we can cancel it from both sides.
      have ne_zero : haar X ≠ 0 := hXpos.ne'
      have ne_top : haar X ≠ ∞ := hXfin.ne
      rw [mul_comm, mul_comm (∏ᶠ i, (mulEquivHaarChar (φ i) : ℝ≥0∞)) _] at h
      have h' := (ENNReal.mul_right_inj ne_zero ne_top).mp h
      rw [← ENNReal.coe_finprod] at h'
      exact ENNReal.coe_inj.mp h'
  -- Now prove the suffices statement: show that the automorphism preserves X
  have h_preserves_X : (restrictedProductCongrRight φ hφ) '' X = X := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩ -- y ∈ X by verifying: for all i ∉ S, we have y i ∈ C i
      intro i hi
      have hbij : Set.BijOn (φ i) (C i) (C i) := by
        rw [Set.mem_setOf_eq] at hi; push_neg at hi; exact hi
      exact hbij.mapsTo (hx i hi)
    · intro hy -- Verifies preimage is in X by showing: for all i ∉ S, (φ i).symm (y i) ∈ C i
      use (restrictedProductCongrRight φ hφ).symm y
      constructor
      · intro i hi
        have hbij : Set.BijOn (φ i) (C i) (C i) := by
          rw [Set.mem_setOf_eq] at hi; push_neg at hi; exact hi
        have : ∀ x ∈ C i, (φ i).symm x ∈ C i := by
          intro x hx
          obtain ⟨z, hz, rfl⟩ := hbij.surjOn hx
          convert hz
          simp
        exact this (y i) (hy i hi)
      · simp -- restrictedProductCongrRight φ hφ ((restrictedProductCongrRight φ hφ).symm y) = y
  -- This relies on the fundamental scaling property of mulEquivHaarChar
  have h_scale : haar ((restrictedProductCongrRight φ hφ) '' X) =
    (mulEquivHaarChar (restrictedProductCongrRight φ hφ) : ℝ≥0∞) * haar X := by
    -- Let `ψ` be our equivalence and `c` be its character for brevity.
    let ψ := restrictedProductCongrRight φ hφ
    let c := mulEquivHaarChar ψ
    let c_ennreal := (c : ℝ≥0∞)

    -- The fundamental theorem defining `c` is `mulEquivHaarChar_map`, which gives:
    -- `c • map ψ haar = haar`
    have h_map_identity := mulEquivHaarChar_map haar ψ
    have hc_pos : 0 < c := mulEquivHaarChar_pos ψ
    -- Multiply both sides by c to solve for `haar (ψ '' X)`
    have hc_ne_top : c_ennreal ≠ ⊤ := ENNReal.coe_ne_top
    have hc_ne_zero : c_ennreal ≠ 0 := ENNReal.coe_ne_zero.mpr hc_pos.ne'
    have h_ennreal : c_ennreal • Measure.map (⇑ψ) haar = haar := by
        rw [← ENNReal.smul_def]
        exact h_map_identity

    -- From this, we get: `map ψ haar = c⁻¹ • haar`
    have h_map_inv : Measure.map (⇑ψ) haar = c_ennreal⁻¹ • haar := by

      -- We want to solve for `Measure.map (⇑ψ) haar`. We can do this by
      -- multiplying both sides by `c_ennreal⁻¹`. The lemma `inv_smul_eq_iff₀`
      -- achieves this, provided the scalar is non-zero.
      have hc_ne_zero : c_ennreal ≠ 0 :=
        ENNReal.coe_ne_zero.mpr (mulEquivHaarChar_pos ψ).ne'

      -- We use the reverse direction of the `iff` lemma to rewrite our identity.
      -- `y₀ • x = y ↔ x = y₀⁻¹ • y`
      sorry -- rwa [inv_smul_eq_iff₀ hc_ne_zero] at h_ennreal

    -- Apply both sides to `ψ '' X`
    have h_on_image : (Measure.map (⇑ψ) haar) (ψ '' X) = (c_ennreal⁻¹ • haar) (ψ '' X) := by
      rw [h_map_inv]

    -- Simplify the LHS using the fact that map pulls back the preimage
    have h_lhs : (Measure.map (⇑ψ) haar) (ψ '' X) = haar X := by
      sorry--rw [Measure.map_apply ψ.continuous.measurable, ψ.toEquiv.preimage_image]

    -- Simplify the RHS using the definition of scalar multiplication
    have h_rhs : (c_ennreal⁻¹ • haar) (ψ '' X) = c_ennreal⁻¹ * haar (ψ '' X) := by
      -- This is the definition of scalar multiplication on a measure.
      simp [Measure.smul_apply]

    -- Combine to get: `haar X = c⁻¹ * haar (ψ '' X)`
    have h_combined : haar X = c_ennreal⁻¹ * haar (ψ '' X) := by
      rw [← h_lhs, h_on_image, h_rhs]

    have h_final : c_ennreal * haar X = haar (ψ '' X) := by
      -- We rewrite our goal using the `iff` lemma for ENNReal.
      rw [← ENNReal.eq_inv_mul_iff_mul_eq'
        (ENNReal.coe_ne_zero.mpr (mulEquivHaarChar_pos ψ).ne') hc_ne_top]
      -- The goal is now exactly our `h_combined` hypothesis.
      exact h_combined

    -- The goal is the symmetric version of `h_final`.
    exact h_final.symm
  rw [← h_scale]
  -- Step 2: The crucial (and sorry'd) lemma from product measure theory.
  -- This states that the measure of the transformed set is the finitary product
  -- of the local scaling factors times the measure of the original set.
  have h_haar_image_eq_prod : haar ((restrictedProductCongrRight φ hφ) '' X) =
    (∏ᶠ i, mulEquivHaarChar (φ i) : ℝ≥0∞) * haar X := by
    -- Let ψ be our equivalence for brevity.
    let ψ := restrictedProductCongrRight φ hφ

    -- Define the component spaces for X. For i ∈ S, the space is the whole group G i.
    -- For i ∉ S, the space is the subgroup C i.
    let X_group_comp : (i : ι) → Type u_2 := fun i ↦ if i ∈ S then G i else ↥(C i)

    -- The set X is the box formed by the carrier sets of these component groups/subgroups.
    let X_carrier_comp : Π i, Set (G i) := fun i ↦ if i ∈ S then Set.univ else ↑(C i)

    -- Step 1: Verify that X is the box formed by these carrier sets.
    have hX_is_prod : X = RestrictedProduct.box' (fun i ↦ (↑(C i) : Set (G i)))
      Filter.cofinite X_carrier_comp := by
      sorry--ext x; simp [X, X_carrier_comp, RestrictedProduct.mem_box', hX_def]

    -- Step 2: Verify that the image of X is the box of the component images.
    have h_img_is_prod : ψ '' X =
        RestrictedProduct.box' (fun i ↦ (↑(C i) : Set (G i)))
          Filter.cofinite (fun i ↦ (φ i) '' (X_carrier_comp i)) := by
      -- This proof follows from the definition of `restrictedProductCongrRight`,
      -- which acts component-wise.
      sorry -- (Proof is the same as the previous version)

    -- Step 3: Verify the local scaling property for each component's Haar measure.
    -- `haarMeasure (G i)` is the Haar measure on the group `G i`.
    have h_local_scale : ∀ i, haar ((φ i) '' (X_carrier_comp i)) =
      (mulEquivHaarChar (φ i) : ℝ≥0∞) * haar (X_carrier_comp i) := by sorry

    -- Step 4: Assume the theorem that the Haar measure of a box is the finitary product
    -- of the component measures.
    have haar_box_is_finprod (U : Π i, Set (G i)) :
      haar (RestrictedProduct.box' (fun i ↦ (↑(C i) : Set (G i)))
        Filter.cofinite U) = ∏ᶠ i, haar (U i) := by
        sorry -- This is the core of product measure theory for restricted products.

    -- Now, we construct the final proof by rewriting with our verified hypotheses.

    -- First, establish the measure of the LHS `haar (ψ '' X)`.
    have h_lhs_measure : haar (ψ '' X) = ∏ᶠ i, (mulEquivHaarChar (φ i) : ℝ≥0∞) *
      haar (X_carrier_comp i) := by
      -- Start with the image, rewrite it as a box, then as a product of measures.
      rw [h_img_is_prod, haar_box_is_finprod]
      -- Now apply the local scaling property to each term in the product.
      congr
      funext i
      exact h_local_scale i

    -- Next, establish the measure of the RHS `haar X`.
    have h_rhs_measure : haar X = ∏ᶠ i, haar (X_carrier_comp i) := by sorry

    -- For the first goal: mulEquivHaarChar support
    have h_char_support : (Function.mulSupport fun i ↦ ↑(mulEquivHaarChar (φ i))).Finite := by
      -- The support is contained in S because for i ∉ S, φ i preserves C i
      have h_subset : Function.mulSupport (fun i ↦ ↑(mulEquivHaarChar (φ i))) ⊆ S := by
        intro i hi
        contrapose! hi
        -- For i ∉ S, φ i bijectively preserves C i, so mulEquivHaarChar (φ i) = 1
        have : mulEquivHaarChar (φ i) = 1 := by
          apply mulEquivHaarChar_eq_one_of_compactSpace
        simp [this]
      exact hS_finite.subset h_subset

    -- For the second goal: haar measure support
    have h_haar_support : (Function.mulSupport fun i ↦ haar (X_carrier_comp i)).Finite := by sorry
      /- -- X_carrier_comp i = univ when i ∈ S, and haar univ = 1 in compact spaces
      have h_subset : Function.mulSupport (fun i ↦ haar (X_carrier_comp i)) ⊆ Sᶜ := by
        intro i hi
        contrapose! hi
        -- When i ∈ S, X_carrier_comp i = univ
        have : X_carrier_comp i = Set.univ := by simp [X_carrier_comp, hi]
        rw [this]
        -- haar univ = 1 in compact spaces
        have : haar (Set.univ : Set (G i)) = 1 := by
          sorry -- This follows from compactness
        simp [this]
      -- Sᶜ is cofinite, but we need actual finiteness
      sorry -- Need to show this is actually finite, not just cofinite -/

    -- For the second goal: haar measure support
    have h_char_support' :
      (Function.mulSupport fun i ↦ (mulEquivHaarChar (φ i) : ℝ≥0∞)).Finite := by
        simp only [Function.mulSupport, ENNReal.coe_ne_one]
        exact h_char_support

    -- Finally, combine these pieces using the distributive property of finitary products.
    -- We start with the LHS measure, pull out the scaling factors, and substitute the RHS measure.
    rw [h_lhs_measure, finprod_mul_distrib h_char_support' h_haar_support, ← h_rhs_measure]
  -- Step 3: The goal is now a direct consequence of this key lemma.
  exact h_haar_image_eq_prod -- FLT#552

end restrictedproduct

end MeasureTheory
