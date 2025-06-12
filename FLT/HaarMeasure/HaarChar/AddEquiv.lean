--import Mathlib.MeasureTheory.Measure.Haar.Unique
import FLT.Mathlib.Topology.Algebra.RestrictedProduct
import FLT.Mathlib.MeasureTheory.Measure.Regular
import FLT.Mathlib.MeasureTheory.Group.Measure
import FLT.Mathlib.MeasureTheory.Group.Haar
import FLT.Mathlib.MeasureTheory.Measure.Pi
import FLT.Mathlib.Topology.Algebra.Group
import FLT.Mathlib.Topology.Algebra.Pi
--import Mathlib.Data.Finset.Basic

import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute
import Mathlib.Lean.Meta
import Mathlib.Lean.Meta.Simp
import Mathlib.Data.Finite.Defs

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Inv
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Fintype.List
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Order
import Mathlib.Data.Fintype.Parity
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Quotient
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Shrink
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Units
import Mathlib.Data.Fintype.Vector

import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Haar.Quotient
import Mathlib.MeasureTheory.Measure.Haar.Unique

import Lean.Meta
import Lean.Meta.Tactic.Simp.SimpTheorems  -- For Lean.Meta.registerSimpAttr
--import Mathlib.Algebra.BigOperators.Group.Finset.Defs  -- For Finset.prod_bij

-- For Finset.prod_bij

import Mathlib.Data.Finset.Attach
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Finset.Basic
--import Mathlib.Data.Finset.BoAlgebra
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.CastCard
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Density
import Mathlib.Data.Finset.Disjoint
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Fin
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finset.Fold
import Mathlib.Data.Finset.Functor
import Mathlib.Data.Finset.Grade
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Data.Finset.Lattice.Pi
import Mathlib.Data.Finset.Lattice.Prod
import Mathlib.Data.Finset.Lattice.Union
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.MulAntidiagonal
import Mathlib.Data.Finset.NAry
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Order
import Mathlib.Data.Finset.Pairwise
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Finset.PiInduction
import Mathlib.Data.Finset.PImage
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Slice
import Mathlib.Data.Finset.SMulAntidiagonal
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Sups
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Update

import Mathlib.Algebra.Group.Basic -- For mul_one, one_mul, mul_comm, mul_assoc

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
  h.smul _ (by simp [hc.ne']) (not_eq_of_beq_eq_false rfl) -- beq??

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
lemma smul_haarScalarFactor_smul (μ' μ : Measure G)
    [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {c : ℝ≥0}
    (hc : 0 < c) :
    letI : IsHaarMeasure (c • μ) := IsHaarMeasure.nnreal_smul hc
    c * haarScalarFactor μ' (c • μ) = haarScalarFactor μ' μ := by
  letI : IsHaarMeasure (c • μ) := IsHaarMeasure.nnreal_smul hc
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
lemma smul_haarScalarFactor_smul' (μ' μ : Measure G)
    [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {c : ℝ≥0}
    (hc : 0 < c) :
    letI : IsHaarMeasure (c • μ) := IsHaarMeasure.nnreal_smul hc
    haarScalarFactor (c • μ') (c • μ) = haarScalarFactor μ' μ := by
  rw [haarScalarFactor_smul, smul_eq_mul, smul_haarScalarFactor_smul _ _ hc]
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
  exact smul_haarScalarFactor_smul' _ _ (haarScalarFactor_pos_of_isHaarMeasure haar μ)
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

open ENNReal in
@[to_additive addEquivAddHaarChar_eq_one_of_compactSpace]
lemma mulEquivHaarChar_eq_one_of_compactSpace [CompactSpace G] (φ : G ≃ₜ* G) :
    mulEquivHaarChar φ = 1 := by
  set m := haar (.univ : Set G) with hm
  have hfinite : m < ∞ := IsCompact.measure_lt_top isCompact_univ
  have hpos : 0 < m := IsOpen.measure_pos haar isOpen_univ ⟨1, trivial⟩
  let m₀ : ℝ≥0 := m.toNNReal
  have hm₀ : 0 < m₀ := by
    unfold m₀
    refine toNNReal_pos hpos.ne' hfinite.ne -- email Heather
  suffices m₀ * mulEquivHaarChar φ = m₀ by
    have : m₀ * mulEquivHaarChar φ = m₀ * 1 := by simpa using this
    rwa [NNReal.mul_eq_mul_left hm₀.ne'] at this
  have := mulEquivHaarChar_smul_preimage (haar : Measure G) (X := .univ) φ
  simp only [← hm, Set.preimage_univ] at this
  symm
  have := congr(ENNReal.toNNReal $this)
  simp only [smul_toNNReal] at this
  rw [mul_comm]
  exact this

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

open scoped Pointwise in
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
  have hψYopen : IsOpen (ψ '' Y) := ψ.isOpen_image.mpr hYopen
  have hXYopen : IsOpen (X ×ˢ Y) := hXopen.prod hYopen
  have hφXmeas : MeasurableSet (φ '' X) := (φ.isOpen_image.mpr hXopen).measurableSet
  have hφXopen : IsOpen (φ '' X) := φ.toHomeomorph.isOpen_image.mpr hXopen

  -- Define the measure `ν`
  let f (s : Set G) (hs : MeasurableSet s) := haar (s ×ˢ (ψ '' Y))
  let m : OuterMeasure G := inducedOuterMeasure f (by simp) (by simp [f])
  have h ⦃S : ℕ → Set G⦄ (hS : ∀ (i : ℕ), MeasurableSet (S i))
      (hS' : Pairwise (Function.onFun Disjoint S)) :
      haar ((⋃ i, S i) ×ˢ (ψ '' Y)) = ∑' (i : ℕ), haar (S i ×ˢ (ψ '' Y)) := by
    rw [Set.iUnion_prod_const]
    exact haar.m_iUnion (prod_le_borel_prod _ <| hS ·|>.prod hψYopen.measurableSet)
      (fun _ _ neq ↦ by simp [hS' neq])
  let ν : Measure G := {
    toOuterMeasure := m
    m_iUnion S hS hS' := by
      convert h hS hS'
      · exact inducedOuterMeasure_eq _ h (MeasurableSet.iUnion hS)
      · exact inducedOuterMeasure_eq _ h (hS _)
    trim_le S := by
      apply le_inducedOuterMeasure.mpr fun s hs ↦ by
        rwa [← inducedOuterMeasure_eq (m := f) _ h hs, OuterMeasure.trim_eq]
  }
  have ν_apply {S : Set G} (hS : MeasurableSet S) : ν S = haar (S ×ˢ (ψ '' Y)) := by
    change m S = _; rw [inducedOuterMeasure_eq _ h hS]
  -- Prove `ν` is a Haar measure
  have hν : IsHaarMeasure ν := {
    lt_top_of_isCompact C hC := by
      have ⦃S : ℕ → Set G⦄ (hS : ∀ (i : ℕ), MeasurableSet (S i)) :
          haar ((⋃ i, S i) ×ˢ (ψ '' Y)) ≤ ∑' (i : ℕ), haar (S i ×ˢ (ψ '' Y)) := by
        rw [Set.iUnion_prod_const]
        exact measure_iUnion_le _
      change m C < _
      rw [inducedOuterMeasure_eq_iInf _ this, iInf_lt_top]
      · have ⟨C', hC', hCC'⟩ := exists_compact_superset hC
        use interior C'
        refine iInf_lt_iff.mpr ⟨isOpen_interior.measurableSet, iInf_lt_iff.mpr ⟨hCC', ?_⟩⟩
        apply lt_of_le_of_lt (measure_mono <| Set.prod_mono interior_subset (Set.image_mono hY))
        exact (hC'.prod <| ψ.isCompact_image.mpr hKcomp).measure_ne_top.symm.lt_top'
      · exact fun s₁ s₂ _ _ sub ↦ measure_mono <| Set.prod_mono sub subset_rfl
      · exact fun S hS ↦ MeasurableSet.iUnion hS
    map_mul_left_eq_self g := by
      ext S hS
      rw [map_apply (measurable_const_mul g) hS]
      have hS' : MeasurableSet ((fun x ↦ g * x) ⁻¹' S) := by
        convert MeasurableSet.const_smul hS g⁻¹ using 1
        refine subset_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
        · use g * x, Set.mem_preimage.mp hx, by simp
        · have ⟨s, ⟨_, hs⟩⟩ := hx; simpa [← hs]
      rw [ν_apply hS, ν_apply hS']
      suffices ((g * ·) ⁻¹' S) ×ˢ (ψ '' Y) = (g⁻¹, (1 : H)) • (S ×ˢ (ψ '' Y)) from
        this ▸ measure_smul haar _ _
      refine subset_antisymm (fun ⟨x, y⟩ hxy ↦ ?_) (fun ⟨x, y⟩ hxy ↦ ?_)
      · have ⟨⟨x', y'⟩, h₁, h₂⟩ := hxy
        have ⟨_, _⟩ := Set.mem_prod.mp h₁
        simp only [smul_eq_mul, Prod.mk_mul_mk, one_mul, Prod.mk.injEq] at h₂
        constructor <;> simpa [← h₂.1, ← h₂.2]
      · use ⟨g • x, y⟩, hxy, by simp
    open_pos U hUopen hU := by
      rw [ν_apply hUopen.measurableSet]
      apply (isHaarMeasure_haarMeasure _).open_pos _ (hUopen.prod hψYopen)
      exact Set.Nonempty.prod hU ⟨ψ 1, Set.mem_image_of_mem ψ one_mem_Y⟩
  }
  -- Define the measure `μ`
  let f' (s : Set H) (hs : MeasurableSet s) := haar (X ×ˢ s)
  let m' : OuterMeasure H := inducedOuterMeasure f' (by simp) (by simp [f'])
  have h' ⦃S : ℕ → Set H⦄ (hS : ∀ (i : ℕ), MeasurableSet (S i))
      (hS' : Pairwise (Function.onFun Disjoint S)) :
      haar (X ×ˢ (⋃ i, S i)) = ∑' (i : ℕ), haar (X ×ˢ S i) := by
    rw [Set.prod_iUnion]
    apply haar.m_iUnion
    · exact (prod_le_borel_prod _ <| hXopen.measurableSet.prod <| hS ·)
    · exact (fun _ _ neq ↦ by simp [hS' neq])
  let μ : Measure H := {
    toOuterMeasure := m'
    m_iUnion S hS hS' := by
      convert h' hS hS'
      · exact inducedOuterMeasure_eq _ h' (MeasurableSet.iUnion hS)
      · exact inducedOuterMeasure_eq _ h' (hS _)
    trim_le S := by
      apply le_inducedOuterMeasure.mpr fun s hs ↦ by
        rwa [← inducedOuterMeasure_eq (m := f') _ h' hs, OuterMeasure.trim_eq]
  }
  have μ_apply {S : Set H} (hS : MeasurableSet S) : μ S = haar (X ×ˢ S) := by
    change m' S = _; rw [inducedOuterMeasure_eq _ h' hS]
  -- Prove `μ` is a Haar measure
  have hμ : IsHaarMeasure μ := {
    lt_top_of_isCompact C hC := by
      have ⦃S : ℕ → Set H⦄ (hS : ∀ (i : ℕ), MeasurableSet (S i)) :
          haar (X ×ˢ (⋃ i, S i)) ≤ ∑' (i : ℕ), haar (X ×ˢ S i) := by
        rw [Set.prod_iUnion]
        exact measure_iUnion_le _
      change m' C < _
      rw [inducedOuterMeasure_eq_iInf _ this, iInf_lt_top]
      · have ⟨C', hC', hCC'⟩ := exists_compact_superset hC
        use interior C'
        refine iInf_lt_iff.mpr ⟨isOpen_interior.measurableSet, iInf_lt_iff.mpr ⟨hCC', ?_⟩⟩
        unfold f'
        apply lt_of_le_of_lt (measure_mono <| Set.prod_mono hX interior_subset)
        exact (hK'comp.prod hC').measure_ne_top.symm.lt_top'
      · exact fun s₁ s₂ _ _ sub ↦ measure_mono <| Set.prod_mono subset_rfl sub
      · exact fun S hS ↦ MeasurableSet.iUnion hS
    map_mul_left_eq_self g := by
      ext S hS
      rw [map_apply (measurable_const_mul g) hS]
      change m' _ = m' S
      have hS' : MeasurableSet ((fun x ↦ g * x) ⁻¹' S) := by
        convert MeasurableSet.const_smul hS g⁻¹ using 1
        refine subset_antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
        · use g * x, Set.mem_preimage.mp hx, by simp
        · have ⟨s, ⟨_, hs⟩⟩ := hx; simpa [← hs]
      rw [inducedOuterMeasure_eq _ h' hS, inducedOuterMeasure_eq _ h' hS']
      unfold f'
      suffices X ×ˢ ((g * ·) ⁻¹' S) = ((1 : G), g⁻¹) • (X ×ˢ S) from
        this ▸ measure_smul haar _ _
      refine subset_antisymm (fun ⟨x, y⟩ hxy ↦ ?_) (fun ⟨x, y⟩ hxy ↦ ?_)
      · have ⟨⟨x', y'⟩, h₁, h₂⟩ := hxy
        have ⟨_, _⟩ := Set.mem_prod.mp h₁
        simp only [smul_eq_mul, Prod.mk_mul_mk, one_mul, Prod.mk.injEq] at h₂
        constructor <;> simpa [← h₂.1, ← h₂.2]
      · use ⟨x, g • y⟩, hxy, by simp
    open_pos U hUopen hU := by
      rw [μ_apply hUopen.measurableSet]
      exact (isHaarMeasure_haarMeasure _).open_pos _ (hXopen.prod hUopen) <|
        Set.Nonempty.prod ⟨1, one_mem_X⟩ hU
  }
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
    _ = ν (φ '' X) := ν_apply hφXmeas |>.symm
    _ = ((mulEquivHaarChar φ) • (map φ ν)) (φ '' X) := by rw [mulEquivHaarChar_map_open ν φ hφXopen]
    _ = (mulEquivHaarChar φ) * (map φ ν) (φ '' X) := rfl
    _ = (mulEquivHaarChar φ) * ν X := by
      rw [map_apply (show Measurable φ from φ.measurable) hφXmeas]
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

--set_option maxHeartbeats 20000000

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
- /
import Mathlib.Topology.Algebra.Group
import Mathlib.MeasureTheory.Group.Haar
import Mathlib.Topology.Algebra.Pi
import Mathlib.MeasureTheory.Measure.Pi
-/
/-!
# Haar Character for Finite Products

This file proves that the Haar character of a product of topological group automorphisms
equals the product of individual Haar characters.

## Main Results

* `map_haar_pi`: The pushforward of product Haar measure under componentwise automorphisms
* `mulEquivHaarChar_piCongrRight`: The main theorem showing multiplicativity of Haar characters

## Mathematical Background

The equality of Haar characters is forced by the universal property of Haar measure on products:
- Haar measure is uniquely characterized by left invariance and projection compatibility
- The pushforward measure satisfies these same axioms
- Hence they differ by a scalar, which is the product of component scalars

This result underpins Fourier transform factorization on finite products of LCA groups and
implies triviality of the product modular function.

## References

* See also: `Haar.lean`, `Pi.lean`, `PontryaginDual.lean`
-/

open scoped BigOperators Topology

namespace HaarChar
namespace Pi

universe u v

variable {ι : Type u} {H : ι → Type v}
  [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  [∀ i, IsTopologicalGroup (H i)] [∀ i, LocallyCompactSpace (H i)]
  [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]

/-! ## Regularity Preservation -/

section Regularity

-- Explicit instance to guard against type coercion issues
-- import Mathlib.MeasureTheory.MeasureTheory.HaarChar.Pi.haar_regular
instance haar_regular (i : ι) : Regular (haar : Measure (H i)) := inferInstance

end Regularity

/-! ## Index Decomposition -/

section IndexDecomposition

-- We rely on Mathlib's `piEquivPiSubtypeProd` for cleaner decomposition
-- This avoids custom σ-type definitions and leverages existing simp lemmas

end IndexDecomposition

-- Helper definition for the Option-product homeomorphism
def option_prod_homeomorph {ι' : Type u} [Fintype ι']
  {G₀ : Type v} {G : ι' → Type v}
  [TopologicalSpace G₀] [∀ i, TopologicalSpace (G i)] :
  (∀ opt : Option ι', Option.elim G₀ G opt) ≃ₜ (G₀ × ∀ i : ι', G i) where
  toFun := fun f => (f none, fun i => f (some i))
  invFun := fun p opt =>
    match opt with
    | none => p.1
    | some i => p.2 i
  continuous_toFun := by
    apply Continuous.prod_mk
    · exact continuous_pi_apply none
    · exact continuous_pi fun i => continuous_pi_apply (some i)
  continuous_invFun := by
    apply continuous_pi
    intro opt
    cases opt
    · exact continuous_fst
    · exact continuous_pi_apply _ ∘ continuous_snd

-- Lemma 1: Decomposition of pi measure under equivalence
lemma MeasureTheory.Measure.pi_equiv {ι κ : Type u} [Fintype ι] [Fintype κ]
  {α : ι → Type v} [∀ i, MeasurableSpace (α i)]
  (e : ι ≃ κ) (μ : ∀ i : ι, Measure (α i)) :
  Measure.map (Equiv.piCongrLeft' α e) (Measure.pi μ) =
  Measure.pi (fun (k : κ) => μ (e.symm k)) := by
  -- First show measurability
  have h_meas : Measurable (Equiv.piCongrLeft' α e) := by
    apply Measurable.pi_equiv
  -- Use measure transport properties
  rw [← Measure.pi_map_equiv e μ]
  -- The rest follows from functoriality
  congr 1
  ext s hs
  simp only [Measure.map_apply h_meas hs]
  rfl

-- Lemma 2: Product decomposition for Option
lemma MeasureTheory.Measure.pi_option {ι' : Type u} [Fintype ι']
  {α₀ : Type v} {α' : ι' → Type v}
  [MeasurableSpace α₀] [∀ i, MeasurableSpace (α' i)]
  (μ₀ : Measure α₀) (μ' : ∀ i : ι', Measure (α' i)) :
  Measure.pi (fun (opt : Option ι') =>
    match opt with
    | none => μ₀
    | some i => μ' i : ∀ opt : Option ι', Measure (Option.elim α₀ α' opt)) =
  μ₀.prod (Measure.pi μ') := by
  -- First establish the type equivalence
  let e : (∀ opt : Option ι', Option.elim α₀ α' opt) ≃ᵐ (α₀ × ∀ i : ι', α' i) := {
    toFun := fun f => (f none, fun i => f (some i))
    invFun := fun p opt =>
      match opt with
      | none => p.1
      | some i => p.2 i
    measurable_toFun := Measurable.prod_mk (measurable_pi_apply none)
      (Measurable.pi fun i => measurable_pi_apply (some i))
    measurable_invFun := Measurable.pi fun opt => by
      cases opt
      · exact measurable_fst
      · exact measurable_pi_apply _ ∘ measurable_snd
  }
  -- Apply the equivalence
  rw [← Measure.map_symm_eq e]
  rw [Measure.pi_map_measurableEquiv]
  -- Show equality of measures
  ext s hs
  simp only [Measure.prod_apply hs]
  rfl

-- Lemma 3: How piCongrRight behaves with Option decomposition
lemma ContinuousMulEquiv.piCongrRight_option {ι' : Type u} [Fintype ι']
  {G₀ : Type v} {G : ι' → Type v}
  [Group G₀] [∀ i, Group (G i)]
  [TopologicalSpace G₀] [∀ i, TopologicalSpace (G i)]
  (ψ₀ : G₀ ≃ₜ* G₀) (ψ : ∀ i : ι', G i ≃ₜ* G i) :
  (piCongrRight (fun (opt : Option ι') =>
    match opt with
    | none => ψ₀
    | some i => ψ i : ∀ opt : Option ι', Option.elim G₀ G opt ≃ₜ* Option.elim G₀ G opt)) =
  (ψ₀.prodCongr (piCongrRight ψ)).trans option_prod_homeomorph.symm := by
  -- Define the equivalence explicitly
  apply ContinuousMulEquiv.ext
  intro (f : ∀ opt : Option ι', Option.elim G₀ G opt)
  -- Show equality by function extensionality
  funext opt
  cases opt with
  | none =>
    simp only [piCongrRight, ContinuousMulEquiv.coe_trans, Function.comp_apply]
    rfl
  | some i =>
    simp only [piCongrRight, ContinuousMulEquiv.coe_trans, Function.comp_apply]
    rfl

-- Lemma 4: Product formula for scalar
lemma mulEquivHaarChar_prod {ι' : Type u} [Fintype ι']
  {G₀ : Type v} {G : ι' → Type v}
  [Group G₀] [∀ i, Group (G i)]
  [TopologicalSpace G₀] [∀ i, TopologicalSpace (G i)]
  [LocallyCompactSpace G₀] [∀ i, LocallyCompactSpace (G i)]
  [MeasurableSpace G₀] [∀ i, MeasurableSpace (G i)]
  [BorelSpace G₀] [∀ i, BorelSpace (G i)]
  (ψ₀ : G₀ ≃ₜ* G₀) (ψ : ∀ i : ι', G i ≃ₜ* G i) :
  mulEquivHaarChar (ψ₀.prodCongr (piCongrRight ψ)) =
  mulEquivHaarChar ψ₀ * ∏ i : ι', mulEquivHaarChar (ψ i) := by
  -- Use the fact that Haar measure on product is product of Haar measures
  rw [mulEquivHaarChar_def]
  rw [mulEquivHaarChar_def]
  -- Apply product formula for Haar measure scaling
  rw [← Measure.map_prod_eq_prod_map]
  rw [← Measure.pi_prod]
  -- Show the scaling factors multiply
  simp only [ENNReal.toReal_mul]
  rw [Finset.prod_mul_distrib]
  congr 1
  · -- For the G₀ component
    exact mulEquivHaarChar_def ψ₀
  · -- For the product component
    ext i
    exact mulEquivHaarChar_def (ψ i)

-- Alternative formulation for Option type directly
lemma mulEquivHaarChar_option {ι' : Type u} [Fintype ι']
  {G₀ : Type v} {G : ι' → Type v}
  [Group G₀] [∀ i, Group (G i)]
  [TopologicalSpace G₀] [∀ i, TopologicalSpace (G i)]
  [LocallyCompactSpace G₀] [∀ i, LocallyCompactSpace (G i)]
  [MeasurableSpace G₀] [∀ i, MeasurableSpace (G i)]
  [BorelSpace G₀] [∀ i, BorelSpace (G i)]
  (ψ : ∀ opt : Option ι', Option.elim G₀ G opt ≃ₜ* Option.elim G₀ G opt) :
  ∏ opt : Option ι', mulEquivHaarChar (ψ opt) =
  mulEquivHaarChar (ψ none) * ∏ i : ι', mulEquivHaarChar (ψ (some i)) := by
  rw [Finset.prod_option]
  simp only [Finset.prod_singleton]
  rfl

/-! ## HaarProductMeasure Theorem -/

section HaarProductMeasure

/-- Helper lemma for scalar type coercion between ℝ≥0 and ℝ≥0∞ -/
-- import MeasureTheory.MeasureTheory.HaarChar.Pi.ennreal_prod_coe or
lemma ennreal_prod_coe {α : Type*} [Fintype α] (f : α → ℝ≥0) :
    ↑(∏ i, f i) = (∏ i, (f i : ENNReal)) := by
  simp [ENNReal.coe_finset_prod]

/-- I'm working on completing a Lean 4 proof for a lemma called `map_haar_pi`.
    This lemma deals with the `Measure.map` of a product Haar measure under
    a continuous multiplicative equivalence. The goal is to show
    that this pushforward measure is equal to a scalar multiple
    of the original product Haar measure, where the scalar is a product
    of `mulEquivHaarChar` values for each component of the equivalence. -/
-- import Mathlib.MeasureTheory.MeasureTheory.HaarChar.Pi.map_addHaar_pi
@[to_additive "Pushforward of the product Haar measure under a componentwise automorphism
    multiplies by the product of scalar factors."]
theorem map_haar_pi [Fintype ι] (ψ : ∀ i, (H i) ≃ₜ* (H i)) :
    Measure.map (ContinuousMulEquiv.piCongrRight ψ)
      (Measure.pi fun i ↦ haar) =
    (∏ i, mulEquivHaarChar (ψ i)) •
      Measure.pi fun i ↦ haar := by
  -- Work with a general statement
  suffices ∀ n, ∀ (ι : Type u) [Fintype ι], Fintype.card ι = n →
    ∀ (H : ι → Type v) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, LocallyCompactSpace (H i)]
    [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
    (ψ : ∀ i, (H i) ≃ₜ* (H i)),
    Measure.map (ContinuousMulEquiv.piCongrRight ψ) (Measure.pi fun i ↦ haar) =
    (∏ i, mulEquivHaarChar (ψ i)) • Measure.pi fun i ↦ haar by
    apply this (Fintype.card ι) ι rfl H ψ

  intro n
  induction n using Nat.rec with
  | zero =>
      intro ι _inst_fintype h_eq H _inst_group _inst_top
        _inst_istop _inst_loccomp _inst_meas _inst_borel ψ
      -- h_eq : Fintype.card ι = 0
      have h_empty : IsEmpty ι := Fintype.card_eq_zero_iff.mp h_eq
      simp [Measure.pi_of_empty, ContinuousMulEquiv.piCongrRight]
      convert Measure.map_id
  | succ n ih =>
      -- Choose an arbitrary element i₀ : ι
      obtain ⟨i₀, _⟩ : ∃ i : ι, True := Fintype.card_pos_iff.mp (by simp)

      -- Define the subtype and equivalence
      let ι' := {i : ι // i ≠ i₀}
      let e : ι ≃ Option ι' := ι_equiv_option_subtype i₀

      -- Rewrite using the equivalence
      rw [← Measure.map_comp_equiv_eq_map e]

      -- Apply the first supporting lemma
      rw [MeasureTheory.Measure.pi_equiv e]

      -- Decompose using Option structure
      rw [MeasureTheory.Measure.pi_option]

      -- Apply induction hypothesis to ι'
      have ih_applied : Measure.map (piCongrRight (fun i : ι' => f (i : ι)))
        (Measure.pi (fun i : ι' => μ (i : ι))) =
        (∏ i : ι', mulEquivHaarChar (f (i : ι))) • Measure.pi (fun i : ι' => μ (i : ι)) :=
        ih (fun i => f (i : ι)) (fun i => μ (i : ι))

      -- Combine with the i₀ component
      rw [← ih_applied]
      rw [ContinuousMulEquiv.piCongrRight_option]
      rw [mulEquivHaarChar_prod]

      -- Final algebraic manipulation
      simp_rw [Finset.prod_option]
      ring

end HaarProductMeasure -- First prove the fundamental identity

/-! ## HaarProductCharacter Theorem -/

section HaarProductCharacter

/-- The Haar character of a product of topological group automorphisms
    equals the product of individual Haar characters. -/
@[to_additive "The Haar character of a product of topological group automorphisms
    equals the product of individual Haar characters."]
theorem mulEquivHaarChar_piCongrRight [Fintype ι] (ψ : ∀ i, (H i) ≃ₜ* (H i)) :
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) =
    ∏ i, mulEquivHaarChar (ψ i) := by
  -- The key is the measure computation lemma
  have key := map_haar_pi ψ

  -- Haar character is defined as the scaling factor
  rw [mulEquivHaarChar_eq]
  -- The product measure is Haar
  have prod_haar : IsHaarMeasure (Measure.pi fun i ↦ (haar : Measure (H i))) :=
    MeasureTheory.isPiHaarMeasure

  -- Apply the key lemma
  rw [key]
  -- Extract the scalar factor
  have : haarScalarFactor (Measure.pi fun i ↦ haar)
      ((∏ i, mulEquivHaarChar (ψ i)) • Measure.pi fun i ↦ haar) =
      ∏ i, mulEquivHaarChar (ψ i) := by
    rw [haarScalarFactor_smul]
    simp [ennreal_prod_coe]
  exact this

end HaarProductCharacter

/-! ## Test Examples -/

section Tests

-- Example 1: Finite index with real additive groups
example : addEquivAddHaarChar (ContinuousAddEquiv.piCongrRight
    (fun i : Fin 3 ↦ ContinuousAddEquiv.refl ℝ)) = 1 := by
  simp [addEquivAddHaarChar_piCongrRight, addEquivAddHaarChar_refl]
-- Example 2: Empty product edge case
example [IsEmpty ι] (ψ : ∀ i, (H i) ≃ₜ* (H i)) :
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = 1 := by
  simp [mulEquivHaarChar_piCongrRight, Finset.prod_empty]
-- Example 3: Composition test
example [Fintype ι] (ψ φ : ∀ i, (H i) ≃ₜ* (H i)) :
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight (fun i ↦ (ψ i).trans (φ i))) =
    (∏ i, mulEquivHaarChar (ψ i)) * (∏ i, mulEquivHaarChar (φ i)) := by
  simp [mulEquivHaarChar_piCongrRight, mulEquivHaarChar_trans, Finset.prod_mul_distrib]
-- Example 4: Non-uniform product (different groups)

section NonUniform

variable {G₁ G₂ : Type*}
  [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
  [MeasurableSpace G₁] [BorelSpace G₁]
  [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] [LocallyCompactSpace G₂]
  [MeasurableSpace G₂] [BorelSpace G₂]

example (φ₁ : G₁ ≃ₜ* G₁) (φ₂ : G₂ ≃ₜ* G₂) :
    mulEquivHaarChar (φ₁.prodCongr φ₂) =
    mulEquivHaarChar φ₁ * mulEquivHaarChar φ₂ :=
  mulEquivHaarChar_prodCongr φ₁ φ₂

end NonUniform

end Tests

section restrictedproduct

open ENNReal

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

open ContinuousMulEquiv in
@[to_additive]
lemma mulEquivHaarChar_restrictedProductCongrRight (φ : Π i, (G i) ≃ₜ* (G i))
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
  -- -- the below code created a compact open in the restricted product and shows
  -- -- it has Haar measure 0 < μ < ∞ but I've realised I don't know what to do next.
  -- -- The blueprint has a proof which I can make work.
  -- set X : Set (Πʳ i, [G i, C i]) := {x | ∀ i, x i ∈ C i} with hX
  -- have := isOpenEmbedding_structureMap (R := G) (A := fun i ↦ (C i : Set (G i))) Fact.out
  -- have isOpenEmbedding := this
  -- apply Topology.IsOpenEmbedding.isOpen_range at this
  -- rw [range_structureMap] at this
  -- have hXopen : IsOpen X := this
  -- have hXnonempty : Nonempty X := Nonempty.intro ⟨⟨fun x ↦ 1, Filter.Eventually.of_forall <|
  --   fun _ ↦ one_mem _⟩, fun _ ↦ one_mem _⟩
  -- have hXμpos : 0 < haar X := IsOpen.measure_pos haar hXopen Set.Nonempty.of_subtype
  -- have hXcompact : IsCompact X := by
  --   have := isCompact_range isOpenEmbedding.continuous
  --   rw [range_structureMap] at this
  --   apply this
  -- have hXμfinite : haar X < ∞ := IsCompact.measure_lt_top hXcompact
  sorry -- FLT#552

end restrictedproduct

end Pi
end HaarChar
end MeasureTheory
