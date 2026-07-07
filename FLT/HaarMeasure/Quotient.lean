/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import FLT.Mathlib.MeasureTheory.Group.ModularCharacter
public import FLT.Mathlib.Topology.Polish

/-!

# Relation between the quotient haar measure and the measure on the whole group.

Let `G` be a second countable locally compact topological group,
and `N` be a closed normal subgroup of `G`.
Given haar measures `dn` on `N` and `d𝓍` on `G ⧸ N`, we can define a measure `dg` on `G` via
`∫ f(x) dx = ∫ (∫ f(xn) dn) d𝓍`. We show that this is a haar measure, and as a conclusion
we can relate the modular character of `G` to the one of `G / N`.

-/

@[expose] public section

open scoped Pointwise ENNReal Function NNReal

lemma exists_continuous_and_indicator_le_of_isCompact
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (f : X → ℝ), Continuous f ∧ HasCompactSupport f ∧
      K.indicator 1 ≤ f ∧ f ≤ U.indicator 1 := by
  classical
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  obtain ⟨f, hf0, hf1, H⟩ := exists_continuous_zero_one_of_isClosed (X := L)
    ((isOpen_interior (s := L)).isClosed_compl.preimage continuous_subtype_val)
    (hK.isClosed.preimage continuous_subtype_val)
    (Set.disjoint_compl_left_iff_subset.mpr (Set.preimage_mono hKL))
  refine ⟨fun x ↦ if h : x ∈ L then f ⟨x, h⟩ else 0, ⟨fun V hV ↦ ?_⟩, ?_, ?_, ?_⟩
  · by_cases hV0 : 0 ∈ V
    · obtain ⟨W, hW, hWV⟩ := hV.preimage f.continuous
      convert hW.union hL.isClosed.isOpen_compl
      ext a
      by_cases haL : a ∈ L
      · simpa [haL] using congr(⟨a, haL⟩ ∈ $hWV).symm
      · simpa [haL]
    · convert (isOpen_interior.isOpenEmbedding_subtypeVal.isOpenMap _
        (hV.preimage (f.continuous.comp (continuous_inclusion interior_subset))))
      ext a
      by_cases haL : a ∈ L
      · suffices f ⟨a, haL⟩ ∈ V → a ∉ interior L → False by
          simpa +contextual [haL, iff_iff_implies_and_implies]
        exact fun h₁ h₂ ↦ hV0 (hf0 (x := ⟨a, haL⟩) h₂ ▸ h₁:)
      · simp [haL, hV0, mt (interior_subset ·) haL]
  · exact exists_compact_iff_hasCompactSupport.mp ⟨L, hL, fun x hx ↦ by simp [hx]⟩
  · intro x
    by_cases hx : x ∈ K
    · simpa [hx, interior_subset (hKL hx)] using (hf1 (x := ⟨x, interior_subset (hKL hx)⟩) hx).ge
    · simp [hx]; grind
  · intro x
    by_cases hx : x ∈ L
    · simp [hx, hLU hx]; grind
    · simp [hx, Set.indicator_apply]; grind

lemma exists_continuous_nnreal_and_indicator_le_of_isCompact
    {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    {K U : Set X} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (f : X → ℝ≥0), Continuous f ∧ HasCompactSupport f ∧
      K.indicator 1 ≤ f ∧ f ≤ U.indicator 1 := by
  classical
  obtain ⟨f, hf, hf', hKf, hfU⟩ :=
    exists_continuous_and_indicator_le_of_isCompact hK hU hKU
  obtain ⟨f, rfl⟩ : ∃ g : X → ℝ≥0, f = (↑) ∘ g :=
    ⟨fun x ↦ ⟨f x, (Set.indicator_nonneg (by simp) _).trans (hKf _)⟩, rfl⟩
  refine ⟨f, NNReal.isEmbedding_coe.continuous_iff.mpr hf, ?_, ?_, ?_⟩
  · exact congr(IsCompact (closure $(Function.support_comp_eq _ (by simp) _))).le hf'
  · exact fun x ↦ by simpa [Set.indicator_apply, ← NNReal.coe_le_coe, apply_ite] using hKf x
  · exact fun x ↦ by simpa [Set.indicator_apply,
      ← NNReal.coe_le_coe, apply_ite NNReal.toReal] using hfU x

lemma MeasureTheory.setLIntegral_lt_top_of_isCompact_of_ne_top {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} [TopologicalSpace α] {s : Set α} (hs : μ s ≠ ∞) (hsc : IsCompact s)
    {f : α → ℝ≥0∞} (hf₁ : ∀ a, f a ≠ ∞) (hf : Continuous f) :
    ∫⁻ (x : α) in s, f x ∂μ < ∞ := by
  obtain ⟨f, rfl⟩ : ∃ g : α → ℝ≥0, f = (↑) ∘ g :=
    ⟨fun x ↦ (f x).toNNReal, funext fun _ ↦ by simp [hf₁ _]⟩
  exact setLIntegral_lt_top_of_isCompact hs hsc (ENNReal.isEmbedding_coe.continuous_iff.mpr hf)

open scoped Pointwise in
lemma Set.inv_smul_set_eq_preimage_mul {G : Type*} [Group G] (g : G) (s : Set G) :
    g⁻¹ • s = (g * ·) ⁻¹' s := by ext; simp [Set.mem_smul_set_iff_inv_smul_mem]

instance {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [SeparatelyContinuousMul G]
    [BorelSpace G] [PolishSpace G]
    (H : Subgroup G) [IsClosed (X := G) H] : BorelSpace (G ⧸ H) :=
  ⟨continuous_quotient_mk'.map_eq_borel (Y := G ⧸ H) QuotientGroup.mk_surjective⟩

instance {M : Type*} [Monoid M] [TopologicalSpace M] [SecondCountableTopology M] :
    SecondCountableTopology Mˣ :=
  TopologicalSpace.secondCountableTopology_induced _ _ _

namespace MeasureTheory

variable {G : Type*} [Group G] [MeasurableSpace G] {N : Subgroup G}
    (μ : Measure (G ⧸ N)) (μN : Measure N)

section

variable [MeasurableMul₂ G] [μN.IsMulLeftInvariant]

/-- The integrand appearing in `Measure.ofQuotient`. -/
noncomputable
def Measure.ofQuotientIntegrand (f : G → ℝ≥0∞) (g : G ⧸ N) : ℝ≥0∞ :=
  g.lift (fun g ↦ ∫⁻ x, f (g * x) ∂ μN) <| fun a b e ↦ by
    obtain ⟨⟨⟨n⟩, (hn : n ∈ N)⟩, rfl : b * n = a⟩ := e
    conv_rhs => rw [← lintegral_mul_left_eq_self _ ⟨n, hn⟩]
    simp [mul_assoc]

@[simp]
lemma Measure.ofQuotientIntegrand_mk (f : G → ℝ≥0∞) (g : G) :
    ofQuotientIntegrand μN f (QuotientGroup.mk g) = ∫⁻ x, f (g * x) ∂ μN := rfl

lemma Measure.ofQuotientIntegrand_indicator (s : Set G) (hs : MeasurableSet s) (g : G) :
    ofQuotientIntegrand μN (s.indicator 1) (QuotientGroup.mk g) = μN ((↑) ⁻¹' (g⁻¹ • s)) := by
  dsimp
  rw [← lintegral_indicator_one ((hs.const_smul _).preimage measurable_subtype_coe)]
  congr with x
  dsimp [Set.indicator]
  congr 1
  simp [Set.mem_inv_smul_set_iff]

instance {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {N : Subgroup G}
    [N.Normal] : ContinuousConstSMul (ConjAct G) N where
  continuous_const_smul g := continuous_induced_rng.mpr (by
    dsimp [Function.comp_def, ConjAct.Subgroup.val_conj_smul, ConjAct.smul_def]
    fun_prop)

instance {G : Type*} [Group G] [TopologicalSpace G] [LocallyCompactSpace G] {N : Subgroup G}
    [IsClosed (X := G) N] : LocallyCompactSpace N :=
  ‹IsClosed _›.isClosedEmbedding_subtypeVal.locallyCompactSpace

instance {G : Type*} [Group G] (N : Subgroup G) [TopologicalSpace G] [SecondCountableTopology G] :
    SecondCountableTopology N := Topology.IsEmbedding.subtypeVal.secondCountableTopology

instance
    {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [LocallyCompactSpace G] {μ : Measure G}
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] : μ.Regular :=
  have ⟨K, _⟩ := exists_positiveCompacts_subset (α := G) isOpen_univ (by simp)
  Measure.regular_of_isMulLeftInvariant
    K.isCompact K.interior_nonempty K.isCompact.measure_lt_top.ne

lemma Measure.ofQuotientIntegrand_indicator_mul_preimage
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] {N : Subgroup G} [IsClosed (X := G) N]
    (μN : Measure N) [μN.IsHaarMeasure]
    (s : Set G) (hs : MeasurableSet s) (a : G) (g : G ⧸ N) [N.Normal] :
    ofQuotientIntegrand μN (((· * a) ⁻¹' s).indicator 1) g =
    mulEquivHaarChar (MulDistribMulAction.toContinuousMulEquiv (ConjAct.toConjAct a) N) *
      ofQuotientIntegrand μN (s.indicator 1) (g * a) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  rw [Measure.ofQuotientIntegrand_indicator _ (hs := by exact hs.preimage (by fun_prop)),
    ← QuotientGroup.mk_mul, Measure.ofQuotientIntegrand_indicator _ _ hs]
  conv_lhs => rw [← MeasureTheory.mulEquivHaarChar_smul_map μN
    (MulDistribMulAction.toContinuousMulEquiv (ConjAct.toConjAct a) N),
    Measure.smul_apply]
  refine congr(_ • $((MulDistribMulAction.toContinuousMulEquiv (ConjAct.toConjAct a)
    N).toMeasurableEquiv.map_apply _)).trans ?_
  dsimp
  congr 2
  ext x
  simp [ConjAct.toConjAct_smul, ConjAct.Subgroup.val_conj_smul, Set.mem_smul_set_iff_inv_smul_mem,
    mul_assoc]

@[simp]
lemma Measure.ofQuotientIntegrand_zero (g : G ⧸ N) :
    ofQuotientIntegrand μN 0 g = 0 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  simp

@[simp]
lemma Measure.ofQuotientIntegrand_fun_zero (g : G ⧸ N) :
    ofQuotientIntegrand μN (fun _ ↦ 0) g = 0 := ofQuotientIntegrand_zero _ _

@[gcongr]
lemma Measure.ofQuotientIntegrand_mono {f₁ f₂ : G → ℝ≥0∞} (hfg : f₁ ≤ f₂) (g : G ⧸ N) :
    ofQuotientIntegrand μN f₁ g ≤ ofQuotientIntegrand μN f₂ g := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  refine lintegral_mono fun _ ↦ hfg _

lemma Measure.ofQuotientIntegrand_iUnion {ι : Type*} [Countable ι] (s : ι → Set G)
    (hs : ∀ i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) (g : G ⧸ N) :
    ofQuotientIntegrand μN ((⋃ i, s i).indicator 1) g =
      ∑' i, ofQuotientIntegrand μN ((s i).indicator 1) g := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  simp only [Measure.ofQuotientIntegrand_indicator, hs, MeasurableSet.iUnion hs]
  rw [Set.smul_set_iUnion, Set.preimage_iUnion, measure_iUnion]
  · simp [Pairwise, Set.disjoint_iff, Set.eq_empty_iff_forall_notMem,
      Set.mem_smul_set_iff_inv_smul_mem] at hs' ⊢
    grind
  · exact fun i ↦ ((hs i).const_smul _).preimage measurable_subtype_coe

variable [SFinite μN]

@[fun_prop]
lemma Measure.measurable_ofQuotientIntegrand (f : G → ℝ≥0∞) (hf : Measurable f) :
    Measurable (ofQuotientIntegrand μN f) := by
  refine measurable_from_quotient.mpr (Measurable.lintegral_prod_right ?_)
  exact (hf.comp measurable_mul).comp (.prodMap measurable_id measurable_subtype_coe)

/--
Let `G` be a second countable locally compact topological group,
and `N` be a closed normal subgroup of `G`.
Given haar measures `dn` on `N` and `d𝓍` on `G ⧸ N`, we can define a measure `dg` on `G` via
`∫ f(x) dx = ∫ (∫ f(xn) dn) d𝓍`.

We later show that this is also a haar measure.
-/
noncomputable
def Measure.ofQuotient : Measure G :=
  .ofMeasurable (fun s _ ↦ ∫⁻ g, ofQuotientIntegrand μN (s.indicator 1) g ∂μ) (by simp)
    fun s hs H ↦ by
    simp only [ofQuotientIntegrand_iUnion μN s hs H]
    rw [lintegral_tsum fun _ ↦ (measurable_ofQuotientIntegrand _ _
      (by exact measurable_const.indicator (hs _))).aemeasurable]

lemma Measure.ofQuotient_apply (s : Set G) (hs : MeasurableSet s) :
    ofQuotient μ μN s = ∫⁻ g, ofQuotientIntegrand μN (s.indicator 1) g ∂μ :=
  Measure.ofMeasurable_apply _ hs

instance {G : Type*} [Group G] (N : Subgroup G) [MeasurableSpace G] [MeasurableMul G]
    [N.Normal] : MeasurableMul (G ⧸ N) where
  measurable_const_mul g := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    exact measurable_from_quotient.mpr (measurable_quotient_mk''.comp (measurable_const_mul g))
  measurable_mul_const g := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    exact measurable_from_quotient.mpr (measurable_quotient_mk''.comp (measurable_mul_const g))

instance [N.Normal] [μ.IsMulLeftInvariant] : (Measure.ofQuotient μ μN).IsMulLeftInvariant where
  map_mul_left_eq_self g := by
    ext s hs
    rw [Measure.map_apply (measurable_const_mul _) hs, Measure.ofQuotient_apply _ _ _ hs,
      Measure.ofQuotient_apply _ _ _ (hs.preimage (measurable_const_mul _))]
    rw [← MeasureTheory.lintegral_mul_left_eq_self _ (QuotientGroup.mk g⁻¹)]
    congr with x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    dsimp only [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rw [Measure.ofQuotientIntegrand_indicator _ _ (hs.preimage (measurable_const_mul _)),
      Measure.ofQuotientIntegrand_indicator _ _ hs]
    simp [← Set.inv_smul_set_eq_preimage_mul, mul_smul]

end

section

variable [TopologicalSpace G] [OpensMeasurableSpace G] [IsTopologicalGroup G]

open scoped NNReal

lemma Measure.continuous_ofQuotientIntegrand [WeaklyLocallyCompactSpace G] [MeasurableMul₂ G]
    [μN.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μN]
    (hN : IsClosed (X := G) N)
    (f : G → ℝ≥0) (hf : Continuous f) (hf' : HasCompactSupport f) :
    Continuous (ofQuotientIntegrand μN (f ·)) := by
  refine continuous_coinduced_dom (f := QuotientGroup.mk).mpr ?_
  eta_expand
  dsimp
  have H (x : _) : Integrable (fun a : N ↦ (f (x * a) : ℝ)) μN :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) <|
      exists_compact_iff_hasCompactSupport.mp
        ⟨_, hN.isClosedEmbedding_subtypeVal.isCompact_preimage (hf'.smul x⁻¹), fun a ha ↦ by
    have : x * a ∉ tsupport f := by simpa [Set.mem_smul_set_iff_inv_smul_mem] using ha
    simp [image_eq_zero_of_notMem_tsupport this]⟩
  simp_rw [MeasureTheory.lintegral_coe_eq_integral _ (H _)]
  refine ENNReal.continuous_ofReal.comp ?_
  refine continuous_iff_continuousAt.mpr fun x₀ ↦ ?_
  obtain ⟨t, ht, ht'⟩ : ∃ t, IsCompact t ∧ t ∈ nhds x₀ := exists_compact_mem_nhds x₀
  refine ContinuousOn.continuousAt ?_ ht'
  refine continuousOn_integral_of_compact_support
    (hN.isClosedEmbedding_subtypeVal.isCompact_preimage (ht.inv.mul hf')) ?_ ?_
  · exact Continuous.continuousOn (by fun_prop)
  · simp only [SetLike.coe_sort_coe, Set.mem_preimage, NNReal.coe_eq_zero, Subtype.forall]
    intro a b hb ha H
    by_contra e
    exact H ⟨_, Set.inv_mem_inv.mpr ha, _, subset_closure e, by simp⟩

omit [OpensMeasurableSpace G] in
lemma Measure.ofQuotientIntegrand_lt_top [MeasurableMul₂ G]
    [μN.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μN]
    (hN : IsClosed (X := G) N)
    (f : G → ℝ≥0) (hf : Continuous f) (hf' : HasCompactSupport f) (a : G ⧸ N) :
    ofQuotientIntegrand μN (f ·) a < ∞ := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  dsimp
  rw [← setLIntegral_eq_of_support_subset (s := Subtype.val ⁻¹' (a⁻¹ • tsupport f))]
  · have := hN.isClosedEmbedding_subtypeVal.isCompact_preimage (hf'.smul a⁻¹)
    exact setLIntegral_lt_top_of_isCompact this.measure_ne_top this (by fun_prop)
  · grw [tsupport, ← subset_closure]
    simp [Set.mem_inv_smul_set_iff]

instance [LocallyCompactSpace G] [T2Space G] [IsFiniteMeasureOnCompacts μ]
    [IsClosed (X := G) N]
    [IsFiniteMeasureOnCompacts μN] [μN.IsMulLeftInvariant] [MeasurableMul₂ G] [SFinite μN] :
    IsFiniteMeasureOnCompacts (Measure.ofQuotient μ μN) where
  lt_top_of_isCompact K hK := by
    classical
    obtain ⟨f, hf, hf', hKf, -⟩ :=
      exists_continuous_nnreal_and_indicator_le_of_isCompact hK isOpen_univ (by simp)
    grw [Measure.ofQuotient_apply _ _ _ hK.measurableSet]
    refine (lintegral_mono (μN.ofQuotientIntegrand_mono (f₂ := (f ·)) ?_)).trans_lt ?_
    · exact fun x ↦ by simpa [Set.indicator_apply, ← ENNReal.coe_le_coe, apply_ite] using hKf x
    rw [← setLIntegral_eq_of_support_subset (s := QuotientGroup.mk '' tsupport f)]
    · exact setLIntegral_lt_top_of_isCompact_of_ne_top (hf'.image
        (by exact continuous_quotient_mk')).measure_ne_top
        (hf'.image (by exact continuous_quotient_mk'))
        (fun _ ↦ (μN.ofQuotientIntegrand_lt_top ‹_› _ hf hf' _).ne)
        (μN.continuous_ofQuotientIntegrand ‹_› _ hf hf')
    intro x hx
    contrapose! hx
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    simp only [Function.mem_support, Measure.ofQuotientIntegrand_mk, ne_eq, Decidable.not_not]
    refine lintegral_eq_zero_of_ae_eq_zero (.of_forall fun y ↦ ?_)
    contrapose! hx
    simp only [Pi.zero_apply, ne_eq, ENNReal.coe_eq_zero] at hx
    refine ⟨_, subset_closure hx, QuotientGroup.eq.mpr (by simp)⟩

instance [μN.IsOpenPosMeasure] [μ.IsOpenPosMeasure] [μN.IsMulLeftInvariant] [MeasurableMul₂ G]
    [SFinite μN] : (Measure.ofQuotient μ μN).IsOpenPosMeasure where
  open_pos U hU hU' := by
    rw [Measure.ofQuotient_apply _ _ _ hU.measurableSet]
    refine ((lintegral_pos_iff_support (μN.measurable_ofQuotientIntegrand _
      (measurable_const.indicator hU.measurableSet))).mpr ?_).ne'
    refine lt_of_lt_of_le ((QuotientGroup.isOpenQuotientMap_mk.isOpenMap _ hU).measure_pos _
      (by simpa)) (μ.mono ?_)
    rintro _ ⟨x, hx, rfl⟩
    refine (Measure.ofQuotientIntegrand_indicator _ _ hU.measurableSet _).trans_ne ?_
    refine ((hU.smul _).preimage_val.measure_pos _ ⟨1, ?_⟩).ne'
    simpa [Set.mem_smul_set_iff_inv_smul_mem]

instance [LocallyCompactSpace G] [T2Space G] [μN.IsHaarMeasure] [N.Normal] [μ.IsHaarMeasure]
    [IsClosed (X := G) N] [MeasurableMul₂ G] [SFinite μN] :
    (μ.ofQuotient μN).IsHaarMeasure where

lemma modularCharacter_eq_modularCharacter_quotient_mul_mulEquivHaarChar
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] (N : Subgroup G) [N.Normal]
    [IsClosed (X := G) N] (g : G) : Measure.modularCharacter g =
      Measure.modularCharacter (g : G ⧸ N) *
        mulEquivHaarChar (MulDistribMulAction.toContinuousMulEquiv (ConjAct.toConjAct g) N) := by
  have : PolishSpace G := polish_of_locally_compact_second_countable _
  have : LocallyCompactSpace N := ‹IsClosed _›.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨K, -⟩ := exists_positiveCompacts_subset (α := G) isOpen_univ (by simp)
  have := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure
    (((Measure.haar (G := G ⧸ N)).ofQuotient .haar).map (· * g))
    ((Measure.haar (G := G ⧸ N)).ofQuotient .haar) K.isCompact.closure
  rw [Measure.map_apply (by fun_prop) K.isCompact.measurableSet,
    Measure.ofQuotient_apply _ _ _ (K.isCompact.measurableSet.preimage <| by fun_prop)] at this
  simp_rw [Measure.ofQuotientIntegrand_indicator_mul_preimage
    .haar _ K.isCompact.measurableSet] at this
  rw [lintegral_const_mul _ (by exact (Measure.measurable_ofQuotientIntegrand _ _
      (measurable_const.indicator K.isCompact.measurableSet)).comp (by fun_prop))] at this
  conv_lhs at this => rw! [Measure.isMulLeftInvariant_eq_smul_of_regular (G := G ⧸ N)
    .haar (Measure.haar.map (· * g⁻¹))]
  simp only [lintegral_smul_measure, Algebra.mul_smul_comm] at this
  rw [MeasurableEmbedding.lintegral_map
    (by exact (MeasurableEquiv.mulRight _).measurableEmbedding),
    Measure.haarScalarFactor_symm] at this
  simp only [QuotientGroup.mk_inv, inv_mul_cancel_right, ← mul_assoc,
    ← Measure.modularCharacterFun_eq_haarScalarFactor, Algebra.smul_def] at this
  rw [← Measure.ofQuotient_apply _ _ _ K.isCompact.measurableSet] at this
  convert! (ENNReal.coe_injective ((ENNReal.mul_left_inj ?_ ?_).mp this)).symm
  · change Measure.modularCharacter _ = (Measure.modularCharacter _)⁻¹; simp
  · exact ((isOpen_interior.measure_pos ((Measure.haar (G := G ⧸ N)).ofQuotient Measure.haar)
      K.interior_nonempty).trans_le (OuterMeasure.mono _ interior_subset)).ne'
  · exact K.isCompact.measure_ne_top

/-- The quotient of a Hausdorff second countable unimodular group by a central normal closed
subgroup is still unimodular. -/
lemma _root_.QuotientGroup.isUnimodularGroup
    {G : Type*} [Group G] [TopologicalSpace G] [IsUnimodularGroup G]
    [T2Space G] [SecondCountableTopology G] (N : Subgroup G) [N.Normal]
    (hN : N ≤ .center G) (hN' : IsClosed (X := G) N) : IsUnimodularGroup (G ⧸ N) where
  modularCharacter_eq_one := by
    ext g
    borelize G
    have H : MulDistribMulAction.toContinuousMulEquiv (ConjAct.toConjAct g) N = .refl _ := by
      ext x
      simp [-SetLike.coe_eq_coe, ConjAct.Subgroup.val_conj_smul, ConjAct.toConjAct_smul,
        ← ((hN x.prop).comm g).eq]
    have := modularCharacter_eq_modularCharacter_quotient_mul_mulEquivHaarChar N g
    simpa [IsUnimodularGroup.modularCharacter_eq_one, H] using this.symm

end

end MeasureTheory
