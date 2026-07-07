/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import FLT.AutomorphicForm.Stuff
public import FLT.HaarMeasure.HaarChar.FiniteDimensional
public import FLT.Mathlib.GroupTheory.DoubleCoset
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Mathlib.Topology.Algebra.Group.CompactOpen
public import Mathlib.Topology.Algebra.Module.TransferInstance
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!

# Unimodular groups

We define unimodular groups,
and show that `[K₂ : gK₁g⁻¹] = [K₂ : K₁]` for open compacts in unimodular groups.

We also show that `GLₙ(K)` is unimodular for `K` a second countable locally compact Hausdorff
topological field.

-/

@[expose] public section

namespace MeasureTheory

lemma IsFiniteMeasureOnCompacts.withDensity
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    [OpensMeasurableSpace X] [T2Space X] (f : X → ENNReal) (hf : Continuous f)
    (hf' : ∀ x, f x < ⊤) :
    IsFiniteMeasureOnCompacts (μ.withDensity f) where
  lt_top_of_isCompact K hK := by
    rw [withDensity_apply _ hK.measurableSet]
    obtain rfl | hK' := K.eq_empty_or_nonempty
    · simp
    obtain ⟨x, hxK, hx⟩ := hK.exists_isMaxOn hK' hf.continuousOn
    refine (setLIntegral_mono (by fun_prop) hx).trans_lt ?_
    simp [ENNReal.mul_lt_top, hf', hK.measure_lt_top]

lemma Measure.IsOpenPosMeasure.withDensity
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    (μ : Measure X) [μ.IsOpenPosMeasure]
    [LocallyCompactSpace X] (f : X → ENNReal) (hf : Continuous f) (hf' : Measurable f)
    (hf0 : ∀ x, f x ≠ 0) :
    (μ.withDensity f).IsOpenPosMeasure where
  open_pos U hU hU' := by
    refine (ne_of_gt (lt_of_lt_of_le ?_ (withDensity_apply_le ..)))
    obtain ⟨K, hK⟩ := exists_positiveCompacts_subset hU hU'
    obtain ⟨x, hxK, hx⟩ := K.isCompact.exists_isMinOn K.nonempty hf.continuousOn
    grw [← hK]
    refine lt_of_lt_of_le ?_ (setLIntegral_mono hf' hx)
    simpa [measure_pos_of_nonempty_interior μ K.interior_nonempty] using (hf0 x).bot_lt

lemma Measure.haarScalarFactor_symm
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [μ.IsHaarMeasure] [ν.IsHaarMeasure] :
    μ.haarScalarFactor ν = (ν.haarScalarFactor μ)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← haarScalarFactor_eq_mul, haarScalarFactor_self]

lemma modularCharacter_eq_mulEquivHaarChar
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (g : G) :
    Measure.modularCharacter g =
      mulEquivHaarChar (MulDistribMulAction.toContinuousMulEquiv (ConjAct.toConjAct g) G) := by
  conv_lhs => rw [← inv_inv g, map_inv]
  simp only [mulEquivHaarChar, Measure.modularCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    Measure.modularCharacterFun_eq_haarScalarFactor Measure.haar,
    ← Measure.haarScalarFactor_symm]
  congr 1
  conv_lhs => rw [← Measure.IsMulLeftInvariant.map_mul_left_eq_self (μ := .haar) g]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

open scoped Pointwise in
lemma Measure.conjAct_smul
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.Regular] (g : ConjAct G) (s : Set G) :
    μ (g • s) = modularCharacter g.ofConjAct * μ s := by
  rw [modularCharacter_eq_mulEquivHaarChar, ← smul_eq_mul, ← Measure.smul_apply,
    Measure.coe_nnreal_smul, mulEquivHaarChar_smul_eq_comap]
  convert! ((MulDistribMulAction.toContinuousMulEquiv
    g G).toMeasurableEquiv.comap_apply μ s).symm using 1
  congr; ext; simp [Set.mem_smul_set_iff_inv_smul_mem]; rfl

open scoped Pointwise in
lemma relIndex_mul_measure {G : Type*}
    [MeasurableSpace G] [Group G] [MeasurableMul G] {H H' : Subgroup G}
    [H.IsFiniteRelIndex H'] (hH : MeasurableSet (H : Set G)) (hHH' : H ≤ H')
    (μ : Measure G) [μ.IsMulLeftInvariant] : ↑(H.relIndex H') * μ ↑H = μ H' := by
  have : (H' : Set G) = ⋃ i : H' ⧸ H.subgroupOf H', i.out • ↑H := by
    convert congr(Subtype.val '' $(QuotientGroup.univ_eq_iUnion_smul (H.subgroupOf H')))
    · simp
    · rw [Set.image_iUnion]
      congr! 2 with x
      generalize x.out = x
      ext y
      suffices x.1⁻¹ * y ∈ H → y ∈ H' by
        simpa [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
      exact fun h ↦ (Subgroup.mul_mem_cancel_left _ (inv_mem x.2)).mp (hHH' h)
  rw [this, measure_iUnion]
  · simp [measure_smul, ENNReal.tsum_const, ENat.card_eq_coe_natCard]; rfl
  · intro a b hab
    refine Set.disjoint_iff.mpr ?_
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, e⟩⟩
    have : a.out.1⁻¹ * b.out ∉ H := by
      simpa [hab] using QuotientGroup.eq (s := H.subgroupOf H') (a := a.out) (b := b.out)
    refine this ?_
    convert mul_mem hx (inv_mem hy) using 1
    simp_rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]
    simpa [Subgroup.smul_def] using e
  · exact fun _ ↦ .const_smul hH _

end MeasureTheory

open MeasureTheory

/-- A group with topolgoy is a unimodular group if it is a locally compact topological group
such that the modular character is trivial. (i.e. left haar measure = right haar measure) -/
class IsUnimodularGroup (G : Type*) [TopologicalSpace G] [Group G] : Prop extends
    IsTopologicalGroup G, LocallyCompactSpace G where
  modularCharacter_eq_one : Measure.modularCharacter (G := G) = 1

instance (priority := low) (G : Type*) [TopologicalSpace G] [CommGroup G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] : IsUnimodularGroup G where
  modularCharacter_eq_one := by
    borelize G
    ext1 g
    dsimp [Measure.modularCharacter]
    simp_rw [Measure.modularCharacterFun_eq_haarScalarFactor .haar, mul_comm _ g,
      Measure.IsMulLeftInvariant.map_mul_left_eq_self, Measure.haarScalarFactor_self]

open scoped Pointwise in
/--
If `G` is a locally compact group, and `K₁, K₂` are compact open subgroups of `G` such that `K₁`
contains both `K₁` and `gK₁g⁻¹`, then `Δ(g) * [K₂ : gK₁g⁻¹] = [K₂ : K₁]`, where `Δ` is the modular
character.
-/
lemma modularCharacter_mul_relIndex_conjAct
    {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] {K₁ K₂ : Subgroup G}
    (hOpen : IsOpen (X := G) K₁) (hCompact : IsCompact (X := G) K₂)
    (g : ConjAct G) (h₁ : K₁ ≤ K₂) (h₂ : g • K₁ ≤ K₂) :
    Measure.modularCharacter (ConjAct.ofConjAct g) * (g • K₁).relIndex K₂ = K₁.relIndex K₂ := by
  have : K₁.IsFiniteRelIndex K₂ := .of_isCompact hOpen hCompact
  have : (g • K₁).IsFiniteRelIndex K₂ := .of_isCompact (hOpen.smul _) hCompact
  let := borel G
  have : BorelSpace G := ⟨rfl⟩
  refine ENNReal.coe_injective ?_
  refine (ENNReal.mul_left_inj (hOpen.measure_ne_zero .haar (by simp)) ?_).mp ?_
  · exact (IsCompact.measure_lt_top (.of_isClosed_subset hCompact
      (Subgroup.isClosed_of_isOpen _ hOpen) h₁)).ne
  · simp [Subgroup.coe_pointwise_smul, Measure.conjAct_smul,
      relIndex_mul_measure hOpen.measurableSet h₁,
      ← relIndex_mul_measure (.const_smul hOpen.measurableSet _) h₂]
    ring

open scoped Pointwise in
/--
If `G` is a unimodular group, and `K₁, K₂` are compact open subgroups of `G` such that `K₁`
contains both `K₁` and `gK₁g⁻¹`, then `[K₂ : gK₁g⁻¹] = [K₂ : K₁]`.
-/
lemma relIndex_conjAct_eq
    {G : Type*} [TopologicalSpace G] [Group G] [IsUnimodularGroup G] {K₁ K₂ : Subgroup G}
    (hOpen : IsOpen (X := G) K₁) (hCompact : IsCompact (X := G) K₂)
    (g : ConjAct G) (h₁ : K₁ ≤ K₂) (h₂ : g • K₁ ≤ K₂) : (g • K₁).relIndex K₂ = K₁.relIndex K₂ := by
  simpa [IsUnimodularGroup.modularCharacter_eq_one] using
    modularCharacter_mul_relIndex_conjAct hOpen hCompact g h₁ h₂

open scoped Pointwise in
/--
If `G` is a unimodular group, and `K₁, K₂` are compact open subgroups of `G` such that `K₁`
contains both `K₁` and `gK₁g⁻¹`, then `[K₂ : gK₁g⁻¹] = [K₂ : K₁]`.
-/
lemma relIndex_conjAct_inv_smul_self
    {G : Type*} [TopologicalSpace G] [Group G] [IsUnimodularGroup G] {K : Subgroup G}
    (hOpen : IsOpen (X := G) K) (hCompact : IsCompact (X := G) K)
    (g : ConjAct G) : (g⁻¹ • K).relIndex K = (g • K).relIndex K := by
  simpa [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_right] using
    relIndex_conjAct_eq (K₁ := g • K ⊓ K) ((hOpen.smul g).inter hOpen) hCompact (g⁻¹)
      (by simp) (by simp)

open scoped Pointwise in
open QuotientGroup in
/-- There exists a set of coset representatives `βᵢ` of `UgU` such that `UgU = ⨆ βᵢgU` and
`Ug⁻¹U = ⨆ βᵢ⁻¹g⁻¹U` -/
lemma exists_bijOn_mk_image_mul_singleton_and_mk_image_mul_singleton_inv
    {G : Type*} [Group G] [TopologicalSpace G] [IsUnimodularGroup G]
    (U : Subgroup G) (hOpen : IsOpen (X := G) U) (hCompact : IsCompact (X := G) U) (g : G) :
    ∃ s : Finset G,
      Set.BijOn QuotientGroup.mk (s : Set G)
        (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ U)) ∧
      Set.BijOn (QuotientGroup.mk ∘ Inv.inv) (s : Set G)
        (QuotientGroup.mk '' (U * {g⁻¹}) : Set (G ⧸ U)) := by
  let n := (ConjAct.toConjAct g • U).relIndex U
  have : (ConjAct.toConjAct g • U).IsFiniteRelIndex U := .of_isCompact (hOpen.smul _) hCompact
  have : (ConjAct.toConjAct g⁻¹ • U).IsFiniteRelIndex U := .of_isCompact (hOpen.smul _) hCompact
  let e : Fin n ≃ (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ U)) :=
    (Finite.equivFin _).symm.trans QuotientGroup.quotientConjActEquivImageMulSingleton
  let e' : Fin n ≃ (QuotientGroup.mk '' (U * {g⁻¹}) : Set (G ⧸ U)) :=
    (Finite.equivFinOfCardEq (by exact relIndex_conjAct_inv_smul_self hOpen hCompact _)).symm.trans
      QuotientGroup.quotientConjActEquivImageMulSingleton
  have (i : Fin n) : ∃ a : G, ↑a = (e i).1 ∧ ↑a⁻¹ = (e' i).1 := by
    obtain ⟨x, hxU, hx⟩ := (e i).2
    obtain ⟨y, hyU, hy⟩ := (e' i).2
    exact ⟨x * g⁻¹ * y⁻¹, by simp_all [← hx, ← hy, QuotientGroup.eq, mul_assoc]⟩
  choose a ha₁ ha₂ using this
  have ha : Function.Injective a := fun i j h ↦ e.injective <| Subtype.ext <| by simp [← ha₁, h]
  refine ⟨Finset.univ.map ⟨a, ha⟩, ?_⟩
  simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Finset.coe_univ,
    ← Set.bijOn_comp_iff ha.injOn]
  constructor
  · convert Subtype.val_injective.injOn.bijOn_image.comp e.bijective.bijOn_univ
    · ext; simp [ha₁]
    · ext; simp
  · convert Subtype.val_injective.injOn.bijOn_image.comp e'.bijective.bijOn_univ
    · ext; simp [ha₂]
    · ext; simp

namespace MeasureTheory

attribute [-instance] Units.instMeasurableSpace

instance Units.instMeasurableSpace {M : Type*} [Monoid M] [MeasurableSpace M] :
    MeasurableSpace Mˣ := .comap (Units.embedProduct M) inferInstance

instance {M : Type*} [Monoid M] [MeasurableSpace M] [TopologicalSpace M]
    [BorelSpace M] [SecondCountableTopology M] :
    BorelSpace Mˣ where
  measurable_eq := by
    rw [Units.instMeasurableSpace, BorelSpace.measurable_eq (α := M × Mᵐᵒᵖ), borel_comap]

lemma Units.measurableEmbedding_val {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    [MeasurableSpace M] [BorelSpace M] [PolishSpace M] :
    MeasurableEmbedding ((↑) : Mˣ → M) :=
  Units.continuous_val.measurableEmbedding Units.val_injective

lemma Units.measurableEmbedding_val' {M : Type*} [Monoid M] [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [IsOpenUnits M] :
    MeasurableEmbedding ((↑) : Mˣ → M) :=
  IsOpenUnits.isOpenEmbedding_unitsVal.measurableEmbedding

attribute [mk_iff] Measure.IsMulLeftInvariant Measure.IsMulRightInvariant
attribute [fun_prop] measurable_mul_unop measurable_mul_op

lemma isMulLeftInvariant_map_op
    {M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul M] (μ : Measure M) :
    (μ.map MulOpposite.op).IsMulLeftInvariant ↔ μ.IsMulRightInvariant := by
  rw [Measure.isMulLeftInvariant_iff, Measure.isMulRightInvariant_iff]
  simp_rw [← (MulOpposite.opMeasurableEquiv (M := M)).measurableEmbedding.map_injective.eq_iff]
  simp (disch := fun_prop) [Measure.map_map]
  rfl

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [MeasurableSpace R] (μ : Measure R)

/-- Given a locally compact topological ring `R` such that `Rˣ → R` is an open embedding.
If `dx` is an additive haar measure on `R`, then `dx/δ(x)` is a multiplicative haar measure on `Rˣ`,
where `δ` is the Haar character. -/
noncomputable def Units.haarMeasure [BorelSpace R] : Measure Rˣ :=
    (μ.comap (↑)).withDensity fun r ↦ ringHaarChar r⁻¹

open scoped Classical in
/-- Can replace `IsOpenUnits R` + `SecondCountableTopology R` by `PolishSpace R`. -/
lemma Units.haarMeasure_apply [BorelSpace R] [IsOpenUnits R] [SecondCountableTopology R]
    (s : Set Rˣ) (hs : MeasurableSet s) :
    Units.haarMeasure μ s = ∫⁻ (a : R) in Units.val '' s,
      if h : IsUnit a then ↑(ringHaarChar h.unit⁻¹) else 0 ∂μ := by
  classical
  dsimp [Units.haarMeasure]
  rw [MeasureTheory.withDensity_apply _ hs]
  convert ((Units.measurableEmbedding_val' (M := R)).lintegral_map (μ := (μ.comap (↑)).restrict s)
    (f := fun r : R ↦ if h : IsUnit r then ringHaarChar h.unit⁻¹ else 0)).symm using 2
  · ext; simp
  rw [Units.measurableEmbedding_val'.restrict_comap, Units.measurableEmbedding_val'.map_comap,
    Measure.restrict_restrict Units.measurableEmbedding_val'.measurableSet_range,
    Set.inter_eq_right.mpr (Set.image_subset_range _ _)]

instance [BorelSpace R] [IsOpenUnits R] [SecondCountableTopology R] [T1Space R]
    [IsFiniteMeasureOnCompacts μ] : IsFiniteMeasureOnCompacts (Units.haarMeasure μ) :=
  have : IsFiniteMeasureOnCompacts (μ.comap Units.val) :=
    .comap' _ Units.continuous_val IsOpenUnits.isOpenEmbedding_unitsVal.measurableEmbedding
  .withDensity _ _ (by fun_prop) (by simp)

instance [BorelSpace R] [PolishSpace R] [IsFiniteMeasureOnCompacts μ] :
    IsFiniteMeasureOnCompacts (Units.haarMeasure μ) :=
  have : IsFiniteMeasureOnCompacts (μ.comap Units.val) :=
    .comap' _ Units.continuous_val Units.measurableEmbedding_val
  .withDensity _ _ (by fun_prop) (by simp)

instance [BorelSpace R] [μ.IsOpenPosMeasure] [IsOpenUnits R]
    [SecondCountableTopology R] [T1Space R] :
    (Units.haarMeasure μ).IsOpenPosMeasure :=
  have : (Measure.comap Units.val μ).IsOpenPosMeasure :=
    .comap _ IsOpenUnits.isOpenEmbedding_unitsVal
  .withDensity _ _ (by fun_prop) (by fun_prop) (by
    simpa using fun x ↦ (ringHaarChar.toHomUnits x).ne_zero)

instance [BorelSpace R] [μ.IsAddHaarMeasure] [IsOpenUnits R]
    [SecondCountableTopology R] [T1Space R] :
    (Units.haarMeasure μ).IsHaarMeasure := by
  classical
  apply +allowSynthFailures Measure.IsHaarMeasure.mk
  refine ⟨fun g ↦ ?_⟩
  ext s hs
  have : Units.val '' (fun x ↦ g * x) ⁻¹' s = MeasurableEquiv.smul g ⁻¹' Units.val '' s := by
    ext; simp [(Equiv.mulLeft g).exists_congr_left (p := fun a ↦ _ * a ∈ _ ∧ _),
      Units.smul_def, Units.inv_mul_eq_iff_eq_mul]
  have H : μ.map (MeasurableEquiv.smul g) =
      (ringHaarChar g)⁻¹ • μ := by
    rw [← MeasurableEquiv.comap_symm]
    refine (addEquivAddHaarChar_smul_eq_comap μ (ContinuousAddEquiv.smul _)).symm.trans ?_
    rw [ContinuousAddEquiv.smul_inv, addEquivAddHaarChar_symm]
    rfl
  rw [Units.haarMeasure_apply _ _ hs, Measure.map_apply (measurable_const_mul _) hs,
    Units.haarMeasure_apply _ _ (hs.preimage (measurable_const_mul _)), this,
    MeasurableEquiv.restrict_preimage,
    (MeasurableEquiv.smul g).symm.measurableEmbedding.lintegral_map, H]
  simp only [Measure.restrict_smul, MeasurableEquiv.symm_smul, MeasurableEquiv.smul_apply,
    lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  rw [← lintegral_const_mul' _ _ (by simp)]
  simp only [map_inv, mul_dite, mul_zero, ← ENNReal.coe_mul, ← mul_inv]
  simp [← map_mul, Units.smul_def]

lemma Units.isMulRightInvariant_haarMeasure
    [BorelSpace R] [μ.IsAddHaarMeasure] [IsOpenUnits R] [SecondCountableTopology R] [T1Space R]
    (H : ∀ x : Rˣ, ringHaarChar x = ringHaarChar (Units.opEquiv.symm (.op x))) :
    (Units.haarMeasure μ).IsMulRightInvariant := by
  have : (μ.comap MulOpposite.opHomeomorph.toMeasurableEquiv.symm).IsAddHaarMeasure :=
    .comap (mH := inferInstance)
    (f := (MulOpposite.opAddEquiv (α := R)).symm.toAddMonoidHom) μ
    MulOpposite.opHomeomorph.symm.isOpenEmbedding
  have : ((Units.haarMeasure (μ.comap MulOpposite.opHomeomorph.toMeasurableEquiv.symm)).comap
    Units.opContinuousMulEquiv.symm.toMonoidHom).IsMulLeftInvariant := .comap _
      Units.opContinuousMulEquiv.symm.toHomeomorph.measurableEmbedding
  rw [← isMulLeftInvariant_map_op]
  convert this
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.comap_apply _ (hs := hs)
    (by exact Units.opContinuousMulEquiv.symm.injective)
    (fun _ ↦ by exact Units.opContinuousMulEquiv.symm.measurableEmbedding.measurableSet_image.mpr)]
  rw [Units.haarMeasure_apply _ _ (hs.preimage measurable_mul_op),
    Units.haarMeasure_apply _ _ (by exact
      Units.opContinuousMulEquiv.symm.measurableEmbedding.measurableSet_image.mpr hs),
    MeasurableEquiv.comap_symm]
  have : MeasurePreserving MulOpposite.opHomeomorph.toMeasurableEquiv μ
    (μ.map MulOpposite.opHomeomorph.toMeasurableEquiv) := ⟨measurable_mul_op, rfl⟩
  rw [← this.setLIntegral_comp_preimage_emb MulOpposite.opHomeomorph.measurableEmbedding]
  congr! with x
  · ext; simp [← MulOpposite.unop_injective.eq_iff]
  · rw [H]; congr; ext; simp
  · simp

lemma Units.isUnimodularGroup [BorelSpace R] [T1Space R] [SecondCountableTopology R] [IsOpenUnits R]
    (H : ∀ x : Rˣ, ringHaarChar x = ringHaarChar (Units.opEquiv.symm (.op x))) :
    IsUnimodularGroup Rˣ := by
  refine ⟨?_⟩
  ext1 g
  refine (Measure.modularCharacterFun_eq_haarScalarFactor
    (Units.haarMeasure Measure.addHaar) g).trans ?_
  have := Units.isMulRightInvariant_haarMeasure Measure.addHaar H
  rw! [Measure.IsMulRightInvariant.map_mul_right_eq_self]
  exact Measure.haarScalarFactor_self _

section Matrix

variable [BorelSpace R] [SecondCountableTopology R] [μ.IsAddHaarMeasure] [IsOpenUnits R]
variable (n : Type*)

instance Matrix.instMeasurableSpace : MeasurableSpace (Matrix n n R) :=
  inferInstanceAs (MeasurableSpace (n → n → R))

instance [Countable n] : BorelSpace (Matrix n n R) :=
  inferInstanceAs (BorelSpace (n → n → R))

instance [Finite n] : LocallyCompactSpace (Matrix n n R) :=
  inferInstanceAs (LocallyCompactSpace (n → n → R))

instance [Countable n] : SecondCountableTopology (Matrix n n R) :=
  inferInstanceAs (SecondCountableTopology (n → _))

instance [Finite n] : IsModuleTopology R (Matrix n n R) :=
  inferInstanceAs (IsModuleTopology R (n → n → R))

instance {K : Type*} [Zero K] [Inv K] [TopologicalSpace K]
    [ContinuousInv₀ K] : ContinuousInv₀ Kᵐᵒᵖ where
  continuousAt_inv₀ x hx := MulOpposite.continuous_op.continuousAt.comp
      ((continuousAt_inv₀ (x := x.unop) (by simpa)).comp
        MulOpposite.continuous_unop.continuousAt)

instance {K : Type*} [DivisionRing K] [TopologicalSpace K]
    [IsTopologicalDivisionRing K] : IsTopologicalDivisionRing Kᵐᵒᵖ where

instance {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsOpenUnits R]
    [Fintype n] [DecidableEq n] : IsOpenUnits (Matrix n n R) := by
  refine ⟨⟨?_, ?_⟩⟩
  · refine Units.isEmbedding_val_mk' (f := (·⁻¹)) ?_ (by simp)
    refine .fun_smul ?_ continuous_id.matrix_adjugate.continuousOn
    · refine .comp' (t := {x : R | IsUnit x}) ?_ continuous_id.matrix_det.continuousOn ?_
      · rw [← Units.range_val, ← Set.image_univ]
        refine IsOpenUnits.isOpenEmbedding_unitsVal.continuousOn_image_iff.mpr ?_
        convert (Units.continuous_val.comp (continuous_inv (G := Rˣ))).continuousOn
        ext; simp
      · exact fun _ ↦ (Matrix.isUnit_iff_isUnit_det _).mp
  · convert (IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).isOpen_range.preimage
      (continuous_id.matrix_det (n := n))
    simp only [Units.range_val, id_eq, Set.preimage_setOf_eq]
    ext
    simp [Matrix.isUnit_iff_isUnit_det]

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
  [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

lemma Matrix.ringHaarChar_eq_of_field [Fintype n] [DecidableEq n] (x : (Matrix n n K)ˣ) :
    ringHaarChar x = ringHaarChar (x.map Matrix.detMonoidHom) ^ Fintype.card n := by
  refine (MeasureTheory.addEquivAddHaarChar_eq_ringHaarChar_det (F := K)
    { __ := ContinuousAddEquiv.mulLeft x, map_smul' r m := by simp }).trans ?_
  rw [← map_pow]
  congr 1
  ext1
  convert! Algebra.norm_eq_det x.1
  dsimp
  rfl

@[to_additive]
lemma Measure.haarScalarFactor_map' {G G' : Type*}
    [Group G] [TopologicalSpace G] [MeasurableSpace G]
    [BorelSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G'] [MeasurableSpace G']
    [BorelSpace G'] [IsTopologicalGroup G']
    (μ' μ : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure] (φ : G ≃ₜ* G') :
    (μ'.map φ).haarScalarFactor (μ.map φ) = μ'.haarScalarFactor μ := by
  -- The group has to be locally compact, otherwise the scalar factor is 1 by definition.
  by_cases hG : LocallyCompactSpace G; swap
  · have : ¬ LocallyCompactSpace G' :=
      fun _ ↦ hG φ.toHomeomorph.isOpenEmbedding.locallyCompactSpace
    simp [haarScalarFactor, hG, this]
  have := φ.symm.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  obtain ⟨⟨f, f_cont⟩, hf⟩ := exists_continuous_nonneg_pos (1 : G')
  have int_f_ne_zero : ∫ (x : G'), f x ∂(map φ μ) ≠ 0 :=
    ne_of_gt (f_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero hf.1 hf.2.1 hf.2.2)
  rw [← NNReal.coe_inj, haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos _ _ hf,
    haarScalarFactor_eq_integral_div μ' μ (f_cont.comp φ.continuous),
    integral_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop)]
  · rfl
  · exact hf.1.comp_homeomorph φ.toHomeomorph
  · change ∫ x, f (φ x) ∂μ ≠ 0
    rwa [← integral_map (by fun_prop) f_cont.aestronglyMeasurable]

@[to_additive addEquivAddHaarChar_conj]
lemma mulEquivHaarChar_conj {M N : Type*}
    [Group M] [TopologicalSpace M] [MeasurableSpace M]
    [BorelSpace M] [IsTopologicalGroup M] [LocallyCompactSpace M]
    [Group N] [TopologicalSpace N] [MeasurableSpace N]
    [BorelSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] (e : M ≃ₜ* N) (σ : M ≃ₜ* M) :
    mulEquivHaarChar (e.symm.trans <| σ.trans e) = mulEquivHaarChar σ := by
  have : ((Measure.haar (G := N)).comap e).IsHaarMeasure := .comap (mH := inferInstance)
    (f := e.toMonoidHom) _ e.isOpenEmbedding
  have : ((Measure.haar (G := N)).comap e).Regular := .comap _ e.toHomeomorph
  have H : Measure.haar.map e.symm = Measure.haar.comap e := e.toMeasurableEquiv.map_symm
  rw [mulEquivHaarChar_eq (Measure.haar.comap e), mulEquivHaarChar,
    ← Measure.haarScalarFactor_map' _ _ e.symm]
  congr
  rw [← H, Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr; ext; simp

@[to_additive addEquivAddHaarChar_conj']
lemma mulEquivHaarChar_conj' {M N : Type*}
    [Group M] [TopologicalSpace M] [MeasurableSpace M]
    [BorelSpace M] [IsTopologicalGroup M] [LocallyCompactSpace M]
    [Group N] [TopologicalSpace N] [MeasurableSpace N]
    [BorelSpace N] [IsTopologicalGroup N] [LocallyCompactSpace N] (e : N ≃ₜ* M) (σ : M ≃ₜ* M) :
    mulEquivHaarChar (e.trans <| σ.trans e.symm) = mulEquivHaarChar σ :=
  mulEquivHaarChar_conj e.symm σ

@[simp]
lemma Measure.modularCharacter_comp {G G' : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [LocallyCompactSpace G']
    (e : G ≃ₜ* G') (g) :
    Measure.modularCharacter (e g) = Measure.modularCharacter g := by
  borelize G G'
  rw [modularCharacter_eq_mulEquivHaarChar, modularCharacter_eq_mulEquivHaarChar,
    ← mulEquivHaarChar_conj e]
  congr; ext; simp [ConjAct.toConjAct_smul]

lemma ContinuousMulEquiv.isUnimodularGroup {G G' : Type*} [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] [IsUnimodularGroup G'] (e : G ≃ₜ* G') :
    IsUnimodularGroup G where
  __ := e.isTopologicalGroup
  __ := e.isOpenEmbedding.locallyCompactSpace
  modularCharacter_eq_one := by
    ext g
    rw [← Measure.modularCharacter_comp e]
    simp [IsUnimodularGroup.modularCharacter_eq_one]

lemma ringHaarChar_of_isHomeomorph {R S : Type*}
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [LocallyCompactSpace R] [MeasurableSpace R] [BorelSpace R]
    [Ring S] [TopologicalSpace S] [IsTopologicalRing S]
    [LocallyCompactSpace S] [MeasurableSpace S] [BorelSpace S]
    (e : R →+* S) (he : IsHomeomorph e) (x : Rˣ) :
    ringHaarChar (x.map e.toMonoidHom) = ringHaarChar x := by
  let e' : R ≃ₜ+ S := { __ := he.homeomorph, __ := e }
  have H (x : _) : e'.symm (e x) = x := e'.symm_apply_apply x
  rw [ringHaarChar_apply, ringHaarChar_apply, ← addEquivAddHaarChar_conj e']
  congr
  ext a
  obtain ⟨a, rfl⟩ := he.surjective a
  simp [H, ← map_mul]
  rfl

open _root_.MulOpposite in
/--
For any ring `R`, we have ring isomorphism `Matₙₓₙ(Rᵒᵖ) ≅ (Matₙₓₙ(R))ᵒᵖ` given by transpose.
-/
@[simps! apply symm_apply]
def Matrix.mopContinuousMulEquiv {m α} [Fintype m] [Mul α] [AddCommMonoid α]
    [TopologicalSpace α] :
    Matrix m m αᵐᵒᵖ ≃ₜ* (Matrix m m α)ᵐᵒᵖ where
  __ := RingEquiv.mopMatrix

open _root_.MulOpposite in
/--
For any ring `R`, we have ring isomorphism `Matₙₓₙ(Rᵒᵖ) ≅ (Matₙₓₙ(R))ᵒᵖ` given by transpose.
-/
@[simps! apply symm_apply]
def Matrix.transposeContinuousMulEquiv {m α} [Fintype m]
    [CommMagma α] [AddCommMonoid α] [TopologicalSpace α] :
    Matrix m m α ≃ₜ* (Matrix m m α)ᵐᵒᵖ where
  __ := Matrix.transposeRingEquiv m α
  continuous_toFun := show Continuous (op ∘ Matrix.transpose) by fun_prop
  continuous_invFun := show Continuous (Matrix.transpose ∘ unop) by fun_prop

lemma Matrix.ringHaarChar_eq_ringHaarChar_opEquiv
    [Fintype n] [DecidableEq n] (x : (Matrix n n K)ˣ) :
    ringHaarChar x = ringHaarChar (Units.opEquiv.symm (.op x)) := by
  rw [Matrix.ringHaarChar_eq_of_field, ← ringHaarChar_of_isHomeomorph (R := (Matrix _ _ _)ᵐᵒᵖ)
    (Matrix.transposeRingEquiv _ _).symm.toRingHom
    (by exact Matrix.transposeContinuousMulEquiv.symm.isHomeomorph),
    Matrix.ringHaarChar_eq_of_field]
  congr 2
  ext1
  simp

instance {n K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
    [LocallyCompactSpace K] [T1Space K] [SecondCountableTopology K] [Fintype n] [DecidableEq n] :
    IsUnimodularGroup (GL n K) := by
  borelize K
  exact Units.isUnimodularGroup (Matrix.ringHaarChar_eq_ringHaarChar_opEquiv _)

end Matrix

end MeasureTheory
