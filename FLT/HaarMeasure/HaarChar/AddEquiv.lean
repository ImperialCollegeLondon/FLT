--import Mathlib.MeasureTheory.Measure.Haar.Unique
import FLT.Mathlib.Topology.Algebra.RestrictedProduct
import FLT.Mathlib.MeasureTheory.Measure.Regular
import FLT.Mathlib.MeasureTheory.Group.Measure
import FLT.Mathlib.MeasureTheory.Group.Haar
import FLT.Mathlib.MeasureTheory.Measure.Pi
import FLT.Mathlib.Topology.Algebra.Group
import FLT.Mathlib.Topology.Algebra.Pi
--import Mathlib.Data.Finset.Basic

import Mathlib.Topology.Basic

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Logic.Equiv.Basic

import Mathlib.Logic.Nonempty

import Mathlib.Data.Set.Image
--import Mathlib.Data.Set.NAry

import Mathlib.Init

import Lean.Meta.Tactic.Simp.Attr
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute
import Mathlib.Lean.Meta
import Mathlib.Lean.Meta.Simp

import Mathlib.Data.Finite.Defs

import Mathlib.Combinatorics.Enumerative.Composition

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

import Mathlib.Logic.Equiv.Defs -- For Equiv

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Basic

--import Mathlib.MeasureTheory.Measure.MeasurableEquiv
import Mathlib.Data.Prod.TProd

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

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Constructions
import Mathlib.Order.Filter.Basic

import Mathlib.Data.Set.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Separation.Regular

import Mathlib.Topology.Defs.Filter

import Mathlib.Topology.Sets.Compacts

import Init.Prelude

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

library_note "Uniqueness of Haar measure"
/-- Any two Haar measures on a locally compact group are proportional. This is
a fundamental result in the theory of Haar measures. -/

-- Haar measures on locally compact groups are regular
@[to_additive IsAddHaarMeasure.regular]
lemma IsHaarMeasure.regular [BorelSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G]
    (μ : Measure G) [IsHaarMeasure μ] : Regular μ := by
  -- The default Haar measure is regular
  have haar_reg : Regular (haar : Measure G) := haar_regular G

  -- Any Haar measure is a scalar multiple of the default Haar measure
  obtain ⟨c, hc⟩ := exists_isHaarMeasure_eq_smul_isHaarMeasure μ haar

  -- Rewrite μ as a scalar multiple of haar
  rw [hc]

  -- Scalar multiples of regular measures are regular
  exact Regular.smul haar_reg c

@[to_additive exists_pos_smul_eq_of_isAddHaarMeasure]
lemma exists_pos_smul_eq_of_isHaarMeasure
    [BorelSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G]
    (μ ν : Measure G) [IsHaarMeasure μ] [IsHaarMeasure ν] :
  ∃ (c : ℝ≥0ˣ), μ = c • ν := by
  -- Now you need to apply the lemma explicitly
  haveI : Regular μ := IsHaarMeasure.regular μ
  haveI : Regular ν := IsHaarMeasure.regular ν
  let c := haarScalarFactor μ ν
  have hc_pos : 0 < c := haarScalarFactor_pos_of_isHaarMeasure μ ν
  refine ⟨⟨c, (c)⁻¹, ?_, ?_⟩, ?_⟩
  · simp [hc_pos.ne']
  · simp [hc_pos.ne']
  · exact isMulLeftInvariant_eq_smul_of_regular μ ν

@[to_additive]
theorem IsHaarMeasure.exists_unique_smul_eq
    [BorelSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G]
    (μ ν : Measure G) [IsHaarMeasure μ] [IsHaarMeasure ν] :
  ∃ (c : ℝ≥0ˣ), μ = c • ν := by
  exact exists_pos_smul_eq_of_isHaarMeasure μ ν

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

-- First, let's recall what piCongrLeft' does
-- It reindexes a dependent function using an equivalence

-- Proof that piCongrLeft' is measurable
lemma measurable_piCongrLeft' {ι κ : Type*} [Fintype ι] [Fintype κ]
  {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  (e : ι ≃ κ) :
  Measurable (Equiv.piCongrLeft' α e) := by
  -- piCongrLeft' : (∀ i : ι, α i) → (∀ k : κ, α (e.symm k))
  -- We need to show this is measurable

  -- It suffices to show that each component function is measurable
  apply measurable_pi_iff.mpr
  intro k

  -- The k-th component of piCongrLeft' extracts the (e.symm k)-th component
  -- This is just a projection, which is measurable
  convert measurable_pi_apply (e.symm k)

-- If you need the inverse direction as well:
lemma measurable_piCongrLeft'_symm {ι κ : Type*} [Fintype ι] [Fintype κ]
  {α : ι → Type*} [∀ i, MeasurableSpace (α i)]
  (e : ι ≃ κ) :
  Measurable (Equiv.piCongrLeft' α e).symm := by
  -- The inverse of piCongrLeft' takes g : (k : κ) → α (e.symm k)
  -- and returns f : (i : ι) → α i where f i = g (e i)
  -- but with the type cast handled

  -- We'll show this is measurable by showing it's measurable in each component
  rw [measurable_pi_iff]
  intro i

  -- For the i-th component, we need to show measurability of
  -- g ↦ ((Equiv.piCongrLeft' α e).symm g) i

  -- By the definition of piCongrLeft', this equals g (e i) with appropriate casting
  show Measurable (fun g => ((Equiv.piCongrLeft' α e).symm g) i)

  sorry

-- General lemma for handling type transports with equivalences
lemma equiv_transport_set {ι : Type u} {α : ι → Type v}
  (e : ι ≃ ι) (S : ∀ i : ι, Set (α i)) (i : ι) :
  ∀ (i' : ι) (h_eq : e.symm (e i) = i'),
    (h_eq ▸ S (e.symm (e i)) : Set (α i')) = S i' := by
  intro i' h_eq
  -- Induction on the equality to reduce to the reflexive case
  induction h_eq
  -- Now the goal is simplified: the transport disappears
  rfl

-- Version for the specific case we need
lemma equiv_symm_apply_transport_set {ι : Type u} {α : ι → Type v}
  (e : ι ≃ ι) (S : ∀ i : ι, Set (α i)) (i : ι) :
  (Equiv.symm_apply_apply e i ▸ S (e.symm (e i)) : Set (α i)) = S i :=
  equiv_transport_set e S i i (Equiv.symm_apply_apply e i)

-- Assume the context is similar to the original problem
universe uu vv
variable {ιι ιι' : Type uu} {HH : ι → Type vv}

/-
-- Assuming ContinuousMulEquiv is defined elsewhere, we use a simplified version for this example
 -/
abbrev ContinuousMulEquiv (GG HH : Type*)
[TopologicalSpace GG] [Group GG] [TopologicalSpace HH] [Group HH] := GG ≃* HH

-- Corrected helper lemma
private lemma transport_in_equiv_apply_combo {ιι ιι' : Type*} {HH : ιι → Type*}
    -- Assumptions from the main definition
    [(i : ιι) → TopologicalSpace (HH i)] [(i : ιι) → Group (HH i)]
    -- The equivalence between the two index types
    (e : ιι ≃ ιι')
    -- The rest of the arguments
    (ψ : (i : ιι) → ContinuousMulEquiv (HH i) (HH i))
    (f : (i : ιι) → HH i)
    (i : ιι)
    (j : ιι)
    (h_eq : e.symm (e i) = j) :
    (ψ j).symm (h_eq ▸ (ψ (e.symm (e i)) (f (e.symm (e i))))) = f j := by
  -- The proof remains the same: induction on the equality is the key.
  induction h_eq
  -- After induction, the goal simplifies to `(ψ i).symm (ψ i (f i)) = f i`.
  -- `simp` can solve this automatically using `MulEquiv.symm_apply_apply`.
  simp

-- Lemma 1: Decomposition of pi measure under equivalence
@[simp]
lemma pi_equiv {ι : Type u} [Fintype ι]
  {α : ι → Type v} [∀ i, MeasurableSpace (α i)]
  (e : ι ≃ ι) (μ : ∀ i : ι, Measure (α i)) :
  Measure.map (Equiv.piCongrLeft' α e) (Measure.pi μ) =
  Measure.pi (fun i => μ (e.symm i)) := by
  -- Now piCongrLeft' : (∀ i : ι, α i) ≃ (∀ i : ι, α (e.symm i))
  -- This avoids the separate type κ

  have h_meas : Measurable (Equiv.piCongrLeft' α e) :=
    measurable_piCongrLeft' e

  -- Key lemma: preimage of rectangles
  have rectangle_preimage : ∀ (S : ∀ i : ι, Set (α (e.symm i))),
    (Equiv.piCongrLeft' α e)⁻¹' (Set.pi Set.univ S) =
    Set.pi Set.univ (fun i => S (e i)) := by
    intro S
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    simp [Equiv.piCongrLeft']
    -- Now both sides have the same type naturally

  -- Show equality on rectangles (which generate the σ-algebra)
  suffices ∀ (S : ∀ i : ι, Set (α (e.symm i))), (∀ i, MeasurableSet (S i)) →
    (Measure.map (Equiv.piCongrLeft' α e) (Measure.pi μ)) (Set.pi Set.univ S) =
    (Measure.pi (fun i => μ (e.symm i))) (Set.pi Set.univ S) by
    -- This suffices by π-λ theorem since rectangles generate the product σ-algebra
    sorry

  intro S hS

  -- Left side
  rw [Measure.map_apply h_meas (MeasurableSet.pi (fun _ => Set.univ) (fun _ => hS _))]
  rw [rectangle_preimage S]
  rw [Measure.pi_pi μ _]

  -- Right side
  rw [Measure.pi_pi (fun i => μ (e.symm i)) _]

  -- Show the products are equal
  -- ∏ i : ι, μ i (S (e i)) = ∏ i : ι, μ (e.symm i) (S i)
  rw [← Finset.prod_bij (fun i _ => e i) _ _ _ _]
  · simp only [Finset.mem_univ, forall_true_left]
  · simp only [Finset.mem_univ, true_implies]
    exact Equiv.injective e
  · simp only [Finset.mem_univ, exists_prop, true_and]
    exact Equiv.surjective e
  · simp only [Finset.mem_univ, true_implies]
    intro i
    simp

-- Lemma 2: Product decomposition for Option
@[simp]
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
@[simp]
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
@[simp]
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

-- Lemma: Pi measure decomposes as product
@[simp]
lemma Measure.pi_prod_pi {ι : Type*} [DecidableEq ι] [Fintype ι]
    {H : ι → Type*} [∀ i, MeasurableSpace (H i)]
    (μ : ∀ i, Measure (H i)) (i₀ : ι) :
    Measure.pi μ = Measure.map (equivToMeasurableEquivOfFintype _).symm
      ((μ i₀).prod (Measure.pi fun i' : {i // i ≠ i₀} => μ (i' : ι))) := by
  -- This requires showing the measures agree on measurable rectangles
  sorry

theorem isHaarMeasure_map_mulEquiv {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (ψ : G ≃ₜ* G) (μ : Measure G) [IsHaarMeasure μ] :
    ∃ (c : ℝ≥0ˣ), IsHaarMeasure (μ.map ψ) ∧ μ.map ψ = c • μ := by
  -- 1. First, prove that the pushforward of a Haar measure `μ` by a group
  --    automorphism `ψ` is also a Haar measure.
  have h_is_haar : IsHaarMeasure (Measure.map ψ) := haar_map_is_haar μ ψ
  -- 2. By the uniqueness of Haar measure (up to a scalar), there must exist a
  --    positive constant `c` relating the two Haar measures `μ` and `μ.map ψ`.
  rcases exists_pos_smul_eq_of_isHaarMeasure μ (Measure.map ψ) with ⟨c, hc⟩
  -- 3. Combine the constant `c` and the proofs `h_is_haar` and `hc` to prove the goal.
  exact ⟨c, h_is_haar, hc⟩

--import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

--open MeasureTheory Measure

-- We assume G is an Additive, Commutative, Topological Group
variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/--
For an additive character ψ and an additive Haar measure μ,
pushing forward μ along ψ scales it by the factor mulEquivHaarChar ψ.

The specification of `mulEquivHaarChar`: `μ.map ψ = mulEquivHaarChar ψ • μ` for an
additive Haar measure `μ`.
-/

-- Lemma: Haar measure transformation
@[to_additive (attr := simp)]
lemma mulEquivHaarChar_map {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [MeasurableSpace G]
    [BorelSpace G] (ψ : G ≃ₜ* G) :
    Measure.map ψ haar = mulEquivHaarChar ψ • haar := by
      -- This follows directly from the definition of `mulEquivHaarChar`.
      exact (mulEquivHaarChar_spec ψ).2

-- Alternative formulation for Option type directly
@[simp]
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
  -- The goal is a conjunction, so we prove each part.
  constructor
  -- 1. Prove that the mapped measure is also a Haar measure.
  · -- We rewrite using our equality `h_eq`.
    rw [h_eq]
    -- A non-zero scalar multiple of a Haar measure is a Haar measure.
    apply IsAddHaarMeasure.smul_of_ne_zero
    -- The constant `mulEquivHaarChar` is always positive, hence non-zero.
    exact (mulEquivHaarChar_pos ψ).ne'

  -- 2. Prove the equality itself.
  · exact h_eq

/--
The specification of `mulEquivHaarChar`: `μ.map ψ = mulEquivHaarChar ψ • μ` for an
additive Haar measure `μ`.
-/
@[simp]
theorem mulEquivHaarChar_spec (ψ : AddChar G ℝ) (μ : Measure G) [IsAddHaarMeasure μ] :
    IsAddHaarMeasure (map (⇑ψ) μ) ∧ map (⇑ψ) μ = mulEquivHaarChar (ψμ) := by
  -- First, we establish the equality using the main lemma from mathlib.
  have h_eq : map (⇑ψ) μ = mulEquivHaarChar (ψμ) := by
    exact map_haar_mulEquiv_eq_mulEquivHaarChar_smul ψ μ

  -- The goal is a conjunction, so we prove each part.
  constructor

  -- 1. Prove that the mapped measure is also a Haar measure.
  · -- We rewrite using our equality `h_eq`.
    rw [h_eq]
    -- A non-zero scalar multiple of a Haar measure is a Haar measure.
    apply IsAddHaarMeasure.smul_of_ne_zero
    -- The constant `mulEquivHaarChar` is always positive, hence non-zero.
    exact (mulEquivHaarChar_pos ψ).ne'

  -- 2. Prove the equality itself.
  · exact h_eq

/-- Given an element `i₀ : ι`, construct an equivalence between `ι` and
    `Option {i : ι // i ≠ i₀}`. The element `i₀` maps to `none` and
    other elements map to `some` of themselves. -/
def ι_equiv_option_subtype {ι : Type*} [DecidableEq ι] (i₀ : ι) :
    ι ≃ Option {i : ι // i ≠ i₀} where
  toFun i := if h : i = i₀ then none else some ⟨i, h⟩
  invFun := fun
    | none => i₀
    | some ⟨i, _⟩ => i
  left_inv i := by
    simp only
    split_ifs with h
    · exact (h).symm
    · rfl
  right_inv := fun
    | none => by simp
    | some ⟨i, hi⟩ => by
        simp only
        split_ifs with h
        · exact absurd h hi
        · congr

/--
A custom lemma that provides a compact neighborhood for any point `g`.
This proof avoids calling `LocallyCompactSpace.local_compact_nhds` directly,
working instead from the T3 property of a locally compact Hausdorff space.
-/
theorem exists_compact_mem_nhds_of_locally_compact {G : Type u}
    [TopologicalSpace G] [LocallyCompactSpace G] [T2Space G] (g : G) :
    ∃ (K : Set G), IsCompact K ∧ K ∈ 𝓝 g := by

  -- 2. Use the compact neighborhood basis from LocallyCompactSpace
  obtain ⟨C, hC_nhds, hC_compact⟩ := (compact_basis_nhds g).ex_mem

  -- 3. Get closed neighborhood within C
  obtain ⟨K, hK_nhds, hK_closed, hK_subset⟩ := exists_mem_nhds_isClosed_subset hC_nhds

  -- 4. K is compact as closed subset of compact
  exact ⟨K, hC_compact.of_isClosed_subset hK_closed hK_subset, hK_nhds⟩

open Set Filter in
/-- A non-empty locally compact group has a compact subset with non-empty interior.
If the group is empty, this is not possible, so we require the group to be `Nonempty`. -/
@[to_additive exists_compact_additive_with_nonempty_interior
"A non-empty locally compact additive group has a compact subset with non-empty interior."]
theorem exists_compact_with_nonempty_interior [Nonempty G] [LocallyCompactSpace G] :
    ∃ (K : Set G), IsCompact K ∧ (interior K).Nonempty := by
  -- Let `g` be any element of the group `G`. Since `G` is nonempty, such an element exists.
  let g : G := Classical.arbitrary G
  have h_univ_nhds : univ ∈ 𝓝 g := univ_mem
  -- Since `G` is a locally compact space, `g` has a compact neighborhood `K`.
  obtain ⟨K, hK_compact, hK_nhds⟩ := exists_compact_mem_nhds_of_locally_compact g -- h_univ_nhds
  -- A neighborhood of `g` by definition contains an open set `U` that also contains `g`.
  obtain ⟨U, hUK, hU_open, hgU⟩ := mem_nhds_iff.mp hK_nhds
  -- We propose this compact set `K` as our candidate.
  refine ⟨K, hK_compact, ?_⟩
  -- We now need to show that the interior of `K` is non-empty.
  -- The open set `U` is a subset of `K`, so it is also a subset of the interior of `K`.
  have hU_sub_int : U ⊆ interior K := hU_open.subset_interior_iff.mpr hUK
  -- The set `U` is non-empty because it contains `g`.
  have hU_nonempty : U.Nonempty := ⟨g, hgU⟩
  -- A set that contains a non-empty set is also non-empty.
  exact hU_nonempty.mono hU_sub_int

@[simp, nolint simpNF, to_additive map_haar_addEquiv_eq_addEquivAddHaarChar_smul ]
theorem exists_unique_smul_of_isHaarMeasure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] [T2Space G]
    (μ ν : Measure G) [IsHaarMeasure μ] [IsHaarMeasure ν] :
    ∃! c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by
    -- ∃! c : `ℝ≥0∞`, c ≠ 0 ∧ c ≠ ∞ ∧ μ = c • ν
  -- Here, we *call* the theorem we just proved to get the set K and its properties.
  obtain ⟨K, hK_compact, hK_interior⟩ := exists_compact_with_nonempty_interior

  -- The rest of the proof proceeds as before...
  have hμK_pos : 0 < μ K := measure_pos_of_isCompact_of_nonempty_interior hK_compact hK_interior
  have hνK_pos : 0 < ν K := measure_pos_of_isCompact_of_nonempty_interior hK_compact hK_interior
  have hμK_finite : μ K < ⊤ := (IsCompact.measure_lt_top hK_compact)
  have hνK_finite : ν K < ⊤ := (IsCompact.measure_lt_top hK_compact)

  let c : ENNReal := μ K / ν K

  refine exists_unique.intro c ?_ ?_

  case existence =>
    constructor
    · exact ⟨(ENNReal.div_pos_iff.mpr (Or.inl ⟨hμK_pos, hνK_finite⟩)).ne.symm,
             ENNReal.div_lt_top_iff.mpr (Or.inl ⟨hμK_finite.ne, hνK_pos⟩)⟩
    · exact measure_eq_div_smul_of_isHaarMeasure μ ν hK_compact hνK_pos hνK_finite

  case uniqueness =>
    intro c' h_c'
    have h_eq : μ K = (c' • ν) K := by rw [h_c'.2]
    rw [smul_apply_of_singleton_ne_zero _ (hK_compact.ne_empty hK_interior)] at h_eq
    have h_def_c : μ K = c * ν K := by
      rw [ENNReal.div_eq_iff_mul_eq (ne_of_gt hνK_pos) hνK_finite.ne]
    rw [h_def_c, mul_eq_mul_right (ne_of_gt hνK_pos) hνK_finite.ne] at h_eq
    exact h_eq.symm

/- TODO: The following lemma is general and should be upstreamed to Mathlib.
   It belongs in `MeasureTheory.Measure.Basic` or similar, not in a file
   specific to Haar measures on products. Distilled here for convenience.

   Proposed location: Mathlib.MeasureTheory.Measure.Basic
   Proposed name: MeasureTheory.Measure.map_comp_measurableEquiv -/

@[to_additive map_haar_addEquiv_eq_addEquivAddHaarChar_smul]
theorem map_haar_mulEquiv_eq_mulEquivHaarChar_smul
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [T2Space G]
    (φ : G ≃ₜ* G) (μ : Measure G) [IsHaarMeasure μ] :
    Measure.map φ μ = mulEquivHaarChar φ • μ := by
  -- By uniqueness of Haar measure, any Haar measure `μ` is a scalar multiple of the
  -- canonical `haarMeasure G`.
  obtain ⟨c, _, hμ⟩ := exists_unique_smul_of_isHaarMeasure μ (haarMeasure G)

  -- We substitute `μ = c • haarMeasure G` on both sides of the goal.
  rw [hμ, hμ, Measure.map_smul]

  -- The definition of `mulEquivHaarChar` states that `map φ (haarMeasure G) = (mulEquivHaarChar φ) • (haarMeasure G)`.
  -- This is captured by the lemma `mulEquivHaarChar_spec`.
  rw [mulEquivHaarChar_spec]

  -- The goal is now to show `c • (mulEquivHaarChar φ • haarMeasure G) = mulEquivHaarChar φ • (c • haarMeasure G)`.
  -- This is true by the commutativity of scalar multiplication.
  rw [smul_comm c]

/-- Composing measure map with equivalence equals map of composed functions -/
lemma map_comp_equiv_eq_map {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (e : α ≃ᵐ β) (f : β → γ) (hf : Measurable f) (μ : Measure α) :
    map (f ∘ e) μ = map f (map e μ) := by
  ext s hs
  rw [map_apply (hf.comp e.measurable) hs]
  rw [map_apply hf, map_apply e.measurable]
  · rfl
  · exact hf hs
  · exact hs

/-- Any equivalence between finite types is a measurable equivalence.

    TODO: This should be added in Mathlib.
    Proposed location: `Mathlib.MeasureTheory.MeasurableSpace.Finite`
    Proposed name: `Fintype.toMeasurableEquiv` or `MeasurableEquiv.ofFintype`

    See also: `measurable_of_finite`, `MeasurableSet.finite`

    Any equivalence between finite types is a measurable equivalence. -/
def equivToMeasurableEquivOfFintype {α β : Type*}
    [Fintype α] [Fintype β]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (e : α ≃ β) : α ≃ᵐ β where
  toEquiv := e
  measurable_toFun := by
    -- Any function from a finite type with measurable singletons is measurable
    apply measurable_of_countable
  measurable_invFun := by
    apply measurable_of_countable

-- We should also add library notes
library_note "Fintype measurable equivalences"
/-- When working with (above) finite types, any equivalence can be upgraded to a measurable
equivalence since all sets are finite and hence measurable. This is used throughout
the theory of Haar measures on finite products. -/

/-- Given homeomorphisms for each component, construct a homeomorphism of pi types
    indexed by `Option ι'` using option elimination. -/
private def optionElimCongrRight {ι' : Type*} {H : Option ι' → Type*}
    [(i : Option ι') → TopologicalSpace (H i)]
    [(i : Option ι') → Group (H i)]
    (ψ_none : H none ≃ₜ* H none)
    (ψ_some : (i' : ι') → H (some i') ≃ₜ* H (some i')) :
    ((i : Option ι') → H i) ≃ₜ* ((i : Option ι') → H i) where
  toFun f i := match i with
    | none => ψ_none (f none)
    | some i' => ψ_some i' (f (some i'))
  invFun f i := match i with
    | none => ψ_none.symm (f none)
    | some i' => (ψ_some i').symm (f (some i'))
  left_inv f := by
    ext i
    cases i <;> simp
  right_inv f := by
    ext i
    cases i <;> simp
  map_mul' := by
    intro f g
    ext i
    cases i
    · exact map_mul ψ_none (f none) (g none)
    · exact map_mul (ψ_some _) (f (some _)) (g (some _))
  continuous_toFun := by
    apply continuous_pi
    intro i
    cases i
    · exact (ψ_none).continuous.comp (continuous_apply _)
    · exact (ψ_some _).continuous.comp (continuous_apply _)
  continuous_invFun := by
    apply continuous_pi
    intro i
    cases i
    · exact (ψ_none).symm.continuous.comp (continuous_apply _)
    · exact (ψ_some _).symm.continuous.comp (continuous_apply _)

open Set Composition -- preimage_id, cast_rfl

@[simp]
lemma continuous_cast {α β : Type u} [inst : TopologicalSpace α] (h : α = β) :
    @Continuous α β inst (h ▸ inst) (cast h) := by
  subst h
  -- Now the goal is @Continuous α α inst inst (cast rfl)
  convert continuous_id

/-- Reindex a pi type homeomorphism using an equivalence of index types -/
private def reindexCongrRight {ι ι' : Type*} (e : ι ≃ ι')
    {H : ι → Type*} [(i : ι) → TopologicalSpace (H i)] [(i : ι) → Group (H i)]
    (ψ : (i : ι) → H i ≃ₜ* H i) :
    ((i : ι) → H i) ≃ₜ* ((i' : ι') → H (e.symm i')) where
  toMulEquiv := {
    toFun := fun f i' => ψ (e.symm i') (f (e.symm i'))
    invFun := fun f i => (ψ i).symm ((Equiv.symm_apply_apply e i) ▸ f (e i))
    left_inv := by
      intro f; ext i
      dsimp

      -- The tactic-based approaches (`simp_rw`, `subst`, `induction` on the main goal) fail
      -- because of a subtle dependency on `i`. We solve this by proving a more general
      -- lemma inside this proof, where the dependency is made explicit.

      -- We state a generalized version of our goal as a helper lemma.
      exact transport_in_equiv_apply_combo e ψ f i i (Equiv.symm_apply_apply e i)
    right_inv := by
      sorry

    map_mul' := by
      intro f g
      ext i'
      -- Need to show: ψ (e.symm i') ((f * g) (e.symm i')) =
      --               ψ (e.symm i') (f (e.symm i')) * ψ (e.symm i') (g (e.symm i'))
      simp only [Pi.mul_apply]
      exact map_mul (ψ (e.symm i')) (f (e.symm i')) (g (e.symm i'))
  }
  continuous_toFun := by
    apply continuous_pi
    intro i'
    exact (ψ (e.symm i')).continuous.comp (continuous_apply _)
  continuous_invFun := by
    apply continuous_pi
    intro i

    refine (ψ i).symm.continuous.comp ?_

    /-
      We need: Continuous (fun f : (i' : ι') → H (e.symm i') =>
        (Equiv.symm_apply_apply e i) ▸ f (e i))
      Note that f : (i' : ι') → H (e.symm i'), so f (e i) : H (e.symm (e i))
    -/

    have aux : ∀ (j : ι) (h : e.symm (e i) = j),
      Continuous (fun f : (i' : ι') → H (e.symm i') => h ▸ f (e i)) := by
      intro j h
      subst h  -- Now the transport disappears
      -- We need: Continuous (fun f : (i' : ι') → H (e.symm i') => f (e i))
      exact continuous_apply (e i)

    exact aux i (Equiv.symm_apply_apply e i)

/-! ## HaarProductMeasure Theorem -/

/-- lemma #1: The cardinality of {i : ι // i ≠ i₀} is one less than the cardinality of ι -/
@[simp]
lemma Fintype.card_subtype_ne {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) :
    Fintype.card {i : ι // i ≠ i₀} = Fintype.card ι - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_of_subsingleton]
  simp

open Lean Meta

-- Create a custom simp attribute for product/sum decompositions
initialize prodDecomposeAttr : SimpExtension ←
  registerSimpAttr `prod_decompose "Lemmas for decomposing products and sums"

/-- lemma #2: Decomposition of a product over ι into i₀ times product over {i : ι // i ≠ i₀} -/
@[to_additive "Decomposition of a sum over ι into i₀ plus sum over {i : ι // i ≠ i₀}"]
lemma prod_decompose_singleton {ι : Type*} [Fintype ι] [DecidableEq ι]
    {β : Type*} [CommMonoid β] (f : ι → β) (i₀ : ι) :
    ∏ i : ι, f i = f i₀ * ∏ i' : {i : ι // i ≠ i₀}, f (i' : ι) := by
  rw [← Finset.prod_subset (s := {i₀}) (t := Finset.univ)]
  · simp only [Finset.prod_singleton]
    congr 1
    apply Finset.prod_bij (fun i hi => ⟨i, by simp at hi; exact hi⟩)
    · intros a b ha hb hab; exact Subtype.coe_injective hab
    · intros b hb; use b.val; simp; exact ⟨b.property, Subtype.coe_eta b⟩
    · intros a ha; rfl
  · intros x hx; simp at hx; exact hx
  · simp

-- Now add the custom attribute after the lemma is defined
attribute [prod_decompose] prod_decompose_singleton

-- The additive version is automatically generated, so we can add the attribute to it
attribute [prod_decompose] sum_decompose_singleton

section HaarProductMeasure

/-- Helper lemma for scalar type coercion between ℝ≥0 and ℝ≥0∞ -/
-- import MeasureTheory.MeasureTheory.HaarChar.Pi.ennreal_prod_coe or
lemma ennreal_prod_coe {α : Type*} [Fintype α] (f : α → ℝ≥0) :
    ↑(∏ i, f i) = (∏ i, (f i : ENNReal)) := by
  simp [ENNReal.coe_finset_prod]

/-- This lemma deals with the `Measure.map` of a product Haar measure under
    a continuous multiplicative equivalence. The goal is to show
    that this pushforward measure is equal to a scalar multiple
    of the original product Haar measure, where the scalar is a product
    of `mulEquivHaarChar` values for each component of the equivalence.

    import Mathlib.MeasureTheory.MeasureTheory.HaarChar.Pi.map_addHaar_pi -/
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
      simp
      convert Measure.map_id
  | succ n ih =>
      intro ι inst h_card H inst_1 inst_2 inst_3 inst_4 inst_5 inst_6 ψ

      haveI : DecidableEq ι := Classical.decEq ι
      have h_pos : 0 < Fintype.card ι := by rw [h_card]; exact Nat.zero_lt_succ n
      have h_nonempty : Nonempty ι := Fintype.card_pos_iff.mp h_pos

      let i₀ : ι := h_nonempty.some
      let ι' : Type _ := { i : ι // i ≠ i₀ }
      let e : ι ≃ Option ι' := ι_equiv_option_subtype i₀
      let ψ' : ∀ i' : ι', H (i' : ι) ≃ₜ* H (i' : ι) := fun i' => ψ (i' : ι)

      -- Use the first lemma here
      have h_card' : Fintype.card ι' = n := by
        rw [Fintype.card_subtype_ne i₀, h_card]
        simp [Nat.succ_sub_one]

      -- Use the second lemma here
      have h_prod_decomp : ∏ i : ι, mulEquivHaarChar (ψ i) =
          mulEquivHaarChar (ψ i₀) * ∏ i' : ι', mulEquivHaarChar (ψ (i' : ι)) :=
        prod_decompose_singleton _ i₀

      have ih_ι' := ih ι' h_card' (fun i' => H (i' : ι))
        (fun i' => ψ (i' : ι))

      -- The transformation `piCongrRight` also decomposes nicely.
      -- T is conjugate to the product of the transformations on the components.
      let T := ContinuousMulEquiv.piCongrRight ψ
      let C := ContinuousMulEquiv.prodCongr (ψ i₀) (ContinuousMulEquiv.piCongrRight ψ')
      have transform_conj : T = (pi_equiv.symm.trans C).trans pi_equiv := by
        ext f i
        dsimp [T, ContinuousMulEquiv.piCongrRight]
        -- Calculate T(f)(i)
        have h_T : T f i = ψ i (f i) := rfl
        -- Calculate (pi_equiv.symm.trans C).trans pi_equiv f i
        dsimp [pi_equiv, ContinuousMulEquiv.prodCongr, Equiv.trans_apply, ContinuousMulEquiv.trans_apply]
        by_cases hi : i = i₀
        · subst hi
          simp [h_T, ψ i₀]
        · simp [h_T, ψ i, hi]
          -- Show the results are equal

      -- Now we need to relate the measures through the Option decomposition
      -- The key insight is that pi measure over ι decomposes as product measure

      -- First, let's work with the measures
      let μ_haar_pi := Measure.pi (fun i : ι => haar : ∀ i, Measure (H i))
      let μ_haar_i₀ := (haar : Measure (H i₀))
      let μ_haar_pi' : Measure (∀ i' : ι', H (i' : ι)) :=
        Measure.pi (fun i' : ι' => (haar : Measure (H (i' : ι))))

      let me : (∀ i : ι, H i) ≃ᵐ (H i₀ × ∀ i' : ι', H (i' : ι)) :=
        equivToMeasurableEquivOfFintype
          { toFun := fun f => (f i₀, fun i' => f (i' : ι))
            invFun := fun p i => if h : i = i₀ then h ▸ p.1 else p.2 ⟨i, h⟩
            left_inv := by
              intro f
              ext i
              simp only [Equiv.coe_fn_mk]
              split_ifs with h
              · exact h ▸ rfl
              · rfl
            right_inv := by
              intro ⟨x, g⟩
              ext
              · simp
              · ext i'
                simp only [Equiv.coe_fn_mk]
                have : (i' : ι) ≠ i₀ := i'.property
                simp [this] }

      -- Key measure identity: pi measure decomposes as product
      have measure_eq : μ_haar_pi = Measure.map me.symm (μ_haar_i₀.prod μ_haar_pi') :=
        (Measure.pi_prod_pi (fun i => (haar : Measure (H i))) i₀).symm-- Define the transformations
      let T := ContinuousMulEquiv.piCongrRight ψ
      let T_i₀ := ψ i₀
      let T_pi' := ContinuousMulEquiv.piCongrRight ψ'
      let C := ContinuousMulEquiv.prodCongr T_i₀ T_pi'

      -- The key conjugation property: T is conjugate to C via me
      have transform_conj : T = me_mul.symm.trans (C.trans me_mul) := by
        ext f i
        simp [T, C, me_mul, me, ContinuousMulEquiv.piCongrRight, ContinuousMulEquiv.prodCongr]
        split_ifs with h
        · subst h; rfl
        · rfl

      -- Main calculation using the decompositions
      calc Measure.map T μ_haar_pi
        _ = Measure.map T (Measure.map me.symm (μ_haar_i₀.prod μ_haar_pi')) := by
          rw [← measure_eq]
        _ = Measure.map (T ∘ me.symm) (μ_haar_i₀.prod μ_haar_pi') := by
          rw [← Measure.map_map me.symm.measurable T.continuous.measurable]
        _ = Measure.map (me.symm ∘ C) (μ_haar_i₀.prod μ_haar_pi') := by
          -- Use the conjugation property
          congr 1
          ext ⟨x, g⟩
          simp only [Function.comp_apply]
          have : T (me.symm ⟨x, g⟩) = me.symm (C ⟨x, g⟩) := by
            rw [transform_conj]
            simp [ContinuousMulEquiv.trans_apply]
          exact this
        _ = Measure.map me.symm (Measure.map C (μ_haar_i₀.prod μ_haar_pi')) := by
          rw [Measure.map_map C.continuous.measurable me.symm.measurable]
        _ = Measure.map me.symm (Measure.map (ContinuousMulEquiv.prodCongr T_i₀ T_pi') (μ_haar_i₀.prod μ_haar_pi')) := by
          rfl
        _ = Measure.map me.symm ((Measure.map T_i₀ μ_haar_i₀).prod (Measure.map T_pi' μ_haar_pi')) := by
          -- Use that map distributes over products for product maps
          rw [Measure.map_prod_map T_i₀.continuous.measurable T_pi'.continuous.measurable]
        _ = Measure.map me.symm ((mulEquivHaarChar T_i₀ • μ_haar_i₀).prod ((∏ i', mulEquivHaarChar (ψ' i')) • μ_haar_pi')) := by
          -- Apply the characterization of Haar measure and the inductive hypothesis
          congr 1
          constructor
          · exact mulEquivHaarChar_map μ_haar_i₀ T_i₀
          · exact ih_ι'
        _ = Measure.map me.symm ((mulEquivHaarChar T_i₀ * ∏ i', mulEquivHaarChar (ψ' i')) • (μ_haar_i₀.prod μ_haar_pi')) := by
          -- Use that product of scaled measures equals scaled product
          rw [Measure.prod_smul]
        _ = (mulEquivHaarChar T_i₀ * ∏ i', mulEquivHaarChar (ψ' i')) • Measure.map me.symm (μ_haar_i₀.prod μ_haar_pi') := by
          -- Scalar multiplication commutes with map
          rw [Measure.map_smul]
        _ = (mulEquivHaarChar (ψ i₀) * ∏ i', mulEquivHaarChar (ψ (i' : ι))) • μ_haar_pi := by
          -- Unfold definitions and use measure_eq
          simp only [T_i₀, ψ']
          rw [measure_eq]
        _ = (∏ i : ι, mulEquivHaarChar (ψ i)) • μ_haar_pi := by
          rw [← h_prod_decomp]

end HaarProductMeasure -- First prove the fundamental identity

/-! ## HaarProductCharacter Lemma -/

section HaarProductCharacter

@[to_additive]
theorem exists_pos_smul_eq_of_isHaarMeasure [Group G] [TopologicalSpace G]
  [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G]
  (μ ν : Measure G) [IsHaarMeasure μ] [IsHaarMeasure ν] :
  ∃ (c : ℝ≥0ˣ), μ = c • ν := by
  exact IsHaarMeasure.exists_unique_smul_eq μ ν

@[to_additive]
theorem exists_isHaarMeasure_eq_smul_isHaarMeasure [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [LocallyCompactSpace G] [IsTopologicalGroup G]
    (μ ν : Measure G) [IsHaarMeasure μ] [IsHaarMeasure ν] :
  ∃ (c : ℝ≥0ˣ), μ = c • ν := by
  exact IsHaarMeasure.exists_unique_smul_eq μ ν

@[to_additive "The Haar character of a product of topological group automorphisms
    equals the product of individual Haar characters."]
lemma mulEquivHaarChar_piCongrRight [Fintype ι] (ψ : Π i, (H i) ≃ₜ* (H i)) :
    letI : MeasurableSpace (Π i, H i) := borel _
    haveI : BorelSpace (Π i, H i) := ⟨rfl⟩
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = ∏ i, mulEquivHaarChar (ψ i) := by
  sorry -- FLT#521 -- induction on size of ι

@[to_additive]
lemma mulEquivHaarChar_piCongrRight_compactCase [Fintype ι]
  [∀ i, CompactSpace (H i)] (ψ : Π i, (H i) ≃ₜ* (H i)) :
    letI : MeasurableSpace (Π i, H i) := borel _
    haveI : BorelSpace (Π i, H i) := ⟨rfl⟩
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = ∏ i, mulEquivHaarChar (ψ i) := by
  letI : MeasurableSpace (∀ i, H i) := borel _
  haveI : BorelSpace (∀ i, H i) := BorelSpace.mk rfl
  -- Manually build the instances for the product space
  haveI : LocallyCompactSpace (∀ i, H i) := by
    haveI : ∀ i, LocallyCompactSpace (H i) := fun i => inferInstance
    exact Pi.locallyCompactSpace
  -- Key observation: each component has Haar character 1
  have h_comp : ∀ i, mulEquivHaarChar (ψ i) = 1 := fun i =>
    mulEquivHaarChar_eq_one_of_compactSpace (ψ i)

  -- So the product is 1
  simp [h_comp, Finset.prod_eq_one]

  -- And the product space is also compact
  haveI : CompactSpace (∀ i, H i) := Pi.compactSpace

  -- So its Haar character is also 1
  exact mulEquivHaarChar_eq_one_of_compactSpace _

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

-- Notes: v3 has full Mathlib (supported)
