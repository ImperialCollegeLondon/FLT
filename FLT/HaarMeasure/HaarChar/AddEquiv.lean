module

public import FLT.Mathlib.MeasureTheory.Group.Measure
public import FLT.Mathlib.MeasureTheory.Measure.Regular
public import FLT.Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
public import FLT.Mathlib.MeasureTheory.Constructions.BorelSpace.RestrictedProduct

@[expose] public section

open MeasureTheory.Measure
open scoped NNReal

namespace MeasureTheory

@[to_additive]
lemma _root_.ContinuousMulEquiv.isHaarMeasure_comap {G H : Type*}
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [MeasurableMul H] [BorelSpace H]
    (φ : G ≃ₜ* H) (μ : Measure H) [IsHaarMeasure μ] : IsHaarMeasure (comap φ μ) :=
  φ.toHomeomorph.isOpenEmbedding.isHaarMeasure_comap (φ := φ.toMulEquiv.toMonoidHom) μ

section basic

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G]

variable [BorelSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]

-- Version of `mulEquivHaarChar_smul_map` without the regularity assumption
-- In this case, the measures need only be equal on open sets
@[to_additive]
lemma mulEquivHaarChar_map_open (μ : Measure G)
    [IsHaarMeasure μ] (φ : G ≃ₜ* G) {s : Set G} (hs : IsOpen s) :
    ((mulEquivHaarChar φ) • map φ μ) s = μ s := by
  rw [mulEquivHaarChar, smul_apply, haarScalarFactor_eq_mul haar (map φ μ) (map φ haar), mul_comm,
    mul_smul, ← measure_isHaarMeasure_eq_smul_of_isOpen haar _ hs,
    measure_isHaarMeasure_eq_smul_of_isOpen haar μ hs, ← mul_smul, haarScalarFactor_map,
    ← haarScalarFactor_eq_mul, haarScalarFactor_self, one_smul]

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
  have : μX.Regular := Regular.comap' μY hf
  obtain ⟨⟨g, g_cont⟩, g_comp, g_nonneg, g_one⟩ :
    ∃ g : C(X, ℝ), HasCompactSupport g ∧ 0 ≤ g ∧ g 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_g_ne_zero : ∫ x, g x ∂μX ≠ 0 :=
    ne_of_gt (g_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero g_comp g_nonneg g_one)
  refine NNReal.coe_injective <| Or.resolve_right (mul_eq_mul_right_iff.mp ?_) int_g_ne_zero
  calc mulEquivHaarChar α • ∫ a, g a ∂μX
    _ = ∫ a, g a ∂(comap α μX) := (integral_comap_eq_mulEquivHaarChar_smul μX α).symm
    _ = ∫ a, g a ∂(comap (f ∘ α) μY) := by
      rw [comap_comap ?_ hf.injective hf.measurableEmbedding.measurableSet_image']
      exact α.measurableEmbedding.measurableSet_image'
    _ = ∫ a, g a ∂(comap (β ∘ f) μY) := by congr; exact funext hComm
    _ = ∫ a, g a ∂(comap f (comap β μY)) := by
      rw [comap_comap hf.measurableEmbedding.measurableSet_image' β.injective ?_]
      exact β.measurableEmbedding.measurableSet_image'
    _ = ∫ a, g a ∂(comap f (mulEquivHaarChar β • μY)) := by rw [← mulEquivHaarChar_smul_eq_comap]
    _ = ∫ a, g a ∂(comap f ((mulEquivHaarChar β : ENNReal) • μY)) := rfl
    _ = mulEquivHaarChar β • ∫ a, g a ∂μX := by rw [comap_smul, integral_smul_measure]; rfl

/-- A version of `mulEquivHaarChar_eq_mulEquivHaarChar_of_isOpenEmbedding` with the stronger
assumption that `f` is a `ContinuousMulEquiv`, for convenience. -/
@[to_additive
/-- A version of `addEquivAddHaarChar_eq_addEquivAddHaarChar_of_isOpenEmbedding` with the stronger
assumption that `f` is a `ContinuousAddEquiv`, for convenience. -/]
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
@[to_additive
/-- The product of two addition-preserving homeomorphisms is
an addition-preserving homeomorphism. -/]
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
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopologyEither G H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) :
    mulEquivHaarChar (φ.prodCongr ψ) = mulEquivHaarChar φ * mulEquivHaarChar ψ := by
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
    · exact hS.prod MeasurableSet.univ
    · intro T hT
      exact measurable_fst hT
  have : IsMulLeftInvariant ν := by
    refine (forall_measure_preimage_mul_iff ν).mp fun g s hs ↦ ?_
    rw [ν_apply hs, ν_apply (hs.preimage (measurable_const_mul g))]
    nth_rw 2 [← map_mul_left_eq_self haar ⟨g, 1⟩]
    conv in fun x ↦ (g, 1) * x => change fun x ↦ ((g * ·) x.1, (1 * ·) x.2)
    simp_rw [one_mul]
    rw [map_apply (by fun_prop), ← Set.prod_preimage_left]
    exact hs.prod hψYopen.measurableSet
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
    · exact MeasurableSet.univ.prod hS
    · intro T hT
      exact measurable_snd hT
  have : IsMulLeftInvariant μ := by
    refine (forall_measure_preimage_mul_iff μ).mp fun h s hs ↦ ?_
    rw [μ_apply hs, μ_apply (hs.preimage (measurable_const_mul h))]
    nth_rw 2 [← map_mul_left_eq_self haar ⟨1, h⟩]
    conv in fun x ↦ (1, h) * x => change fun x ↦ ((1 * ·) x.1, (h * ·) x.2)
    simp_rw [one_mul]
    rw [map_apply (by fun_prop), ← Set.prod_preimage_right]
    exact hXopen.measurableSet.prod hs
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
@[to_additive
/-- An arbitrary product of addition-preserving homeomorphisms
is an addition-preserving homeomorphism. -/]
def _root_.ContinuousMulEquiv.piCongrRight (ψ : Π i, (G i) ≃ₜ* (H i)) :
    (∀ i, G i) ≃ₜ* (∀ i, H i) where
  __ := MulEquiv.piCongrRight (fun i ↦ ψ i)
  continuous_toFun := Continuous.piMap (fun i ↦ (ψ i).continuous_toFun)
  continuous_invFun := Continuous.piMap (fun i ↦ (ψ i).continuous_invFun)

end piCongrRight

section pi

variable {ι : Type*} {H : ι → Type*} [Π i, Group (H i)] [Π i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, LocallyCompactSpace (H i)]
    [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] [∀ i, SecondCountableTopology (H i)]

open Classical ContinuousMulEquiv in
@[to_additive]
lemma mulEquivHaarChar_piCongrRight [Fintype ι] (ψ : Π i, (H i) ≃ₜ* (H i)) :
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = ∏ i, mulEquivHaarChar (ψ i) := by
  let P : (α : Type u_1) → [Fintype α] → Prop := fun ι _ ↦
    ∀ (H : ι → Type u_2) [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, LocallyCompactSpace (H i)]
    [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)] [∀ i, SecondCountableTopology (H i)]
    (ψ : (i : ι) → H i ≃ₜ* H i),
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = ∏ i, mulEquivHaarChar (ψ i)
  refine Fintype.induction_subsingleton_or_nontrivial (P := P) ι ?_ ?_ H ψ
  · intro α _ subsingleton_α H _ _ _ _ _ _ _ ψ
    by_cases hα : Nonempty α; swap
    · rw [not_nonempty_iff] at hα; simp [mulEquivHaarChar_eq_one_of_compactSpace]
    have : Unique α := @Unique.mk' α (Classical.inhabited_of_nonempty hα) subsingleton_α
    rw [Fintype.prod_subsingleton _ default]
    exact mulEquivHaarChar_eq_mulEquivHaarChar_of_continuousMulEquiv (piUnique H) _ _ (fun _ ↦ rfl)
  intro α fintype_α nontrivial_α ih H _ _ _ _ _ _ _ ψ
  have ⟨a, b, ne⟩ := nontrivial_α
  let β₁ := {i : α // i = a}
  let β₂ := {i : α // i ≠ a}
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

open RestrictedProduct

open Pointwise in
-- TODO this should be elsewhere
-- note: it can't be an instance because typeclass inference can't find C
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
    [∀ i, LocallyCompactSpace (G i)] -- follows from the hypotheses, but needed for *statement*
    [∀ i, SecondCountableTopology (G i)]

open ContinuousMulEquiv Filter in
@[to_additive]
lemma mulEquivHaarChar_restrictedProductCongrRight_of_principal {J : Set ι}
    [Countable ι]
    [J_cof : Fact (Filter.cofinite ≤ 𝓟 J)]
    (φ : Π i, (G i) ≃ₜ* (G i))
    (hφ : ∀ i ∈ J, Set.BijOn ⇑(φ i) ↑(C i) ↑(C i)) :
    mulEquivHaarChar
      (.restrictedProductCongrRight φ (eventually_principal.mpr hφ) :
        (Πʳ i, [G i, C i]_[𝓟 J]) ≃ₜ* (Πʳ i, [G i, C i]_[𝓟 J])) =
    ∏ᶠ i, mulEquivHaarChar (φ i) := by
  have hJcfinite : Finite (Jᶜ : Set ι) := (J_cof.out fun _ a ↦ a)
  have hJcfinite' : Set.Finite (Jᶜ : Set ι) := hJcfinite
  have : Fintype (Jᶜ : Set ι) := hJcfinite'.fintype
  have hφ' : ∀ i, i ∈ J → Set.BijOn (φ i).symm (C i) (C i) := fun i hi ↦
    (hφ i hi).symm <| ⟨fun _ _ ↦ apply_symm_apply _ _, fun _ _ ↦ symm_apply_apply _ _⟩
  set φ_C : ∀ i : J, C i ≃ₜ* C i := fun i ↦
  { toFun := hφ i i.2 |>.mapsTo.restrict
    invFun := hφ' i i.2 |>.mapsTo.restrict
    left_inv x := by ext; simp
    right_inv y := by ext; simp
    map_mul' _ _ := by ext; exact map_mul (φ i) _ _
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have hφJ (i : ι) (hi : i ∈ J) : mulEquivHaarChar (φ_C ⟨i, hi⟩) = mulEquivHaarChar (φ i) :=
    mulEquivHaarChar_eq_mulEquivHaarChar_of_isOpenEmbedding (f := (C i).subtype)
    ((hCopen.out i).isOpenEmbedding_subtypeVal) (φ_C ⟨i, hi⟩) (φ i) (fun _ ↦ rfl)
  set Φ : (Πʳ i, [G i, C i]_[𝓟 J]) ≃ₜ* (Πʳ i, [G i, C i]_[𝓟 J]) :=
    .restrictedProductCongrRight φ (eventually_principal.mpr hφ)
  set Ψ : (Π i : (J : Set ι), C i) × (Π i : (Jᶜ : Set ι), G i)
      ≃ₜ* (Π i : (J : Set ι), C i) × (Π i : (Jᶜ : Set ι), G i) :=
    .prodCongr (.piCongrRight φ_C) (.piCongrRight fun i ↦ φ i)
  set I : (Πʳ i, [G i, C i]_[𝓟 J]) ≃ₜ* _ := .restrictedProductPrincipal J
  have Ψ_I_eq (x) : I.toMulEquiv (Φ x) = Ψ (I.toMulEquiv x) := rfl
  have : ∀ (i : ↑J), SecondCountableTopology ↥(C ↑i) := fun i ↦
    TopologicalSpace.secondCountableTopology_induced (C i) (G i) _
  have hφj (i : ι) (hi : i ∈ J) : mulEquivHaarChar (φ i) = 1 := by
    rw [← hφJ i hi, mulEquivHaarChar_eq_one_of_compactSpace]
  have hsupp : Function.mulSupport (fun i : ι ↦ mulEquivHaarChar (φ i)) ⊆ Jᶜ :=
    fun i hi hiJ ↦ hi <| hφj i hiJ
  have hfin : (Function.mulSupport fun i : ι ↦ mulEquivHaarChar (φ i)).Finite :=
    hJcfinite'.subset hsupp
  rw [mulEquivHaarChar_eq_mulEquivHaarChar_of_isOpenEmbedding (f := I.toMulEquiv)
    I.isOpenEmbedding Φ Ψ Ψ_I_eq, mulEquivHaarChar_prodCongr,
    mulEquivHaarChar_eq_one_of_compactSpace, mulEquivHaarChar_piCongrRight, one_mul,
    Finset.prod_set_coe (f := fun i ↦ mulEquivHaarChar (φ i)),
    finprod_eq_prod_of_mulSupport_toFinset_subset _ hfin]
  simpa [← Finset.coe_subset, Set.coe_toFinset] using hsupp

variable [∀ i, WeaklyLocallyCompactSpace (G i)]

open ContinuousMulEquiv Filter Topology in
@[to_additive]
lemma mulEquivHaarChar_restrictedProductCongrRight [Countable ι] (φ : Π i, (G i) ≃ₜ* (G i))
    (hφ : ∀ᶠ (i : ι) in Filter.cofinite, Set.BijOn ⇑(φ i) ↑(C i) ↑(C i)) :
    mulEquivHaarChar
      (.restrictedProductCongrRight φ hφ : (Πʳ i, [G i, C i]) ≃ₜ* (Πʳ i, [G i, C i])) =
    ∏ᶠ i, mulEquivHaarChar (φ i) := by
  set Φ : (Πʳ i, [G i, C i]) ≃ₜ* (Πʳ i, [G i, C i]) := .restrictedProductCongrRight φ hφ
  set J := {i : ι | Set.BijOn ⇑(φ i) ↑(C i) ↑(C i)}
  have J_cof : Fact (Filter.cofinite ≤ 𝓟 J) := ⟨by simpa only [le_principal_iff] using hφ⟩
  have hφ_J : ∀ i ∈ J, Set.BijOn ⇑(φ i) ↑(C i) ↑(C i) := fun _ ↦ id
  set Φ_J : (Πʳ i, [G i, C i]_[𝓟 J]) ≃ₜ* (Πʳ i, [G i, C i]_[𝓟 J]) :=
    .restrictedProductCongrRight φ (eventually_principal.mpr hφ_J)
  set ι_J : (Πʳ i, [G i, C i]_[𝓟 J]) →* (Πʳ i, [G i, C i]) :=
    RestrictedProduct.mapAlongMonoidHom (B₁ := C) (B₂ := C) G G id (tendsto_id'.mpr J_cof.out)
      (fun _ ↦ .id _) (Eventually.of_forall fun _ _ a ↦ a)
  have ι_J_emb : IsOpenEmbedding ι_J :=
    RestrictedProduct.isOpenEmbedding_inclusion_principal hCopen.out J_cof.out
  have Φ_ι_J_eq (x) : Φ (ι_J x) = ι_J (Φ_J x) := rfl
  rw [← mulEquivHaarChar_eq_mulEquivHaarChar_of_isOpenEmbedding ι_J_emb Φ_J Φ Φ_ι_J_eq]
  exact mulEquivHaarChar_restrictedProductCongrRight_of_principal _ hφ_J

end restrictedproduct

end MeasureTheory
