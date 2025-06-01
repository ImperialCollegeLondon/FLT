import Mathlib.MeasureTheory.Measure.Haar.Unique
import FLT.Mathlib.Topology.Algebra.RestrictedProduct
import Mathlib.Topology.Algebra.RestrictedProduct
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
  sorry -- FLT#520

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


set_option maxHeartbeats 2000000000

@[to_additive]
lemma mulEquivHaarChar_piCongrRight [Fintype ι] (ψ : Π i, (H i) ≃ₜ* (H i)) :
    letI : MeasurableSpace (Π i, H i) := borel _
    haveI : BorelSpace (Π i, H i) := ⟨rfl⟩
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = ∏ i, mulEquivHaarChar (ψ i) := by
-- sorry -- FLT#521 -- induction on size of ι

  /-

  The above comment suggests using induction on the size of the index type ι.
  Since ι is a Fintype, we can use the fact that any finite type is either
  empty or has one element removed from a smaller finite type.
  Here's the proof strategy:

  * Handle the empty case (when ι is empty)
  * Use induction to reduce to the case where we add one element
  * Use the product formula for two groups (which should be available
      from mulEquivHaarChar_prodCongr)

  The proof uses the following key steps:

  1. Base case: When ι is empty, the product type Π i, H i
      is isomorphic to the unit group. Both sides equal 1.

  2. (LEAN 3) Inductive step:

    * `Pick` an element j : ι and decompose Π i, H i ≃ₗₜ* H j × Π i : ι',
      H i where ι' = ι \ {j}
    * `Show` that piCongrRight ψ decomposes as ψ j × piCongrRight (ψ|ι')
    * `Apply` mulEquivHaarChar_prodCongr to get the product formula
    * `Use` the induction hypothesis on the smaller index set ι'
    * `Rearrange` the finite product to complete the proof

  The key insight is that the Haar characteristic is multiplicative
  with respect to products, allowing us to reduce the finite product
  to a binary product and use induction.

  The key differences in the Lean 4 approach:

  1. (LEAN 4) No induction': Lean 4 doesn't have the induction' tactic
  from Mathlib3. Instead, we use:

  Standard induction on natural numbers with a suffices statement, or
  Fintype.induction_empty_option which is specifically designed for
  induction on finite types


  2. Fintype.induction_empty_option: This is a specialized induction
  principle for finite types that says:

  Prove the property for the empty type
  Prove that if the property holds for ι, then it holds for Option ι
  Then the property holds for all finite types


  3. Cleaner structure: The second approach using
  Fintype.induction_empty_option is cleaner because:

    * It directly handles the structure we need (empty base case, adding one element)
    * It uses the standard MulEquiv.piOptionEquivProd to split products
    * It avoids manual cardinality calculations

  The proof strategy remains the same: show that the Haar characteristic is multiplicative with respect to products, then use induction to reduce the finite product to the base cases.

  -/

    letI : MeasurableSpace (Π i, H i) := borel _
    haveI : BorelSpace (Π i, H i) := ⟨rfl⟩
    -- Use Fintype.induction_empty_option for cleaner induction
    apply Fintype.induction_empty_option (P := fun ι => ∀ (H : ι → Type*)
      [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
      [∀ i, IsTopologicalGroup (H i)] [∀ i, LocallyCompactSpace (H i)]
      [∀ i, MeasurableSpace (H i)] [∀ i, BorelSpace (H i)]
      (ψ : Π i, (H i) ≃ₜ* (H i)),
      letI : MeasurableSpace (Π i, H i) := borel _
      haveI : BorelSpace (Π i, H i) := ⟨rfl⟩
      mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = ∏ i, mulEquivHaarChar (ψ i))
    · -- Base case: empty type
      intro H _ _ _ _ _ _ ψ
      letI : MeasurableSpace (Π i : Empty, H i) := borel _
      haveI : BorelSpace (Π i : Empty, H i) := ⟨rfl⟩
      simp only [Fintype.prod_empty]
      -- The pi type over Empty is isomorphic to Unit
      have piEmpty : (Π i : Empty, H i) ≃ₜ* Unit :=
        ⟨⟨MulEquiv.piEmpty H, continuous_const, continuous_of_isEmpty_domain⟩⟩
      have : ContinuousMulEquiv.piCongrRight ψ = piEmpty.symm.trans piEmpty := by
        ext x i
        exact Empty.elim i
      rw [this, mulEquivHaarChar_trans]
      simp [mulEquivHaarChar_eq_one_of_compactSpace]

    · -- Inductive case: Option ι
      intro ι _ IH H _ _ _ _ _ _ ψ
      letI : MeasurableSpace (Π i : Option ι, H i) := borel _
      haveI : BorelSpace (Π i : Option ι, H i) := ⟨rfl⟩
      -- Split the product as H none × (Π i : ι, H (some i))
      let e : (Π i : Option ι, H i) ≃ₜ* H none × (Π i : ι, H (some i)) :=
        ⟨⟨MulEquiv.piOptionEquivProd H,
          continuous_prod_mk.mpr ⟨continuous_apply none, continuous_pi fun i => continuous_apply (some i)⟩,
          continuous_pi fun i => i.casesOn continuous_fst (fun j => (continuous_apply j).comp continuous_snd)⟩⟩
      -- Show that piCongrRight commutes with this splitting
      have comm : e.trans ((ψ none).prodCongr (ContinuousMulEquiv.piCongrRight fun i => ψ (some i))).trans e.symm =
                  ContinuousMulEquiv.piCongrRight ψ := by
        ext x i
        cases i with
        | none => simp [e, MulEquiv.piOptionEquivProd]
        | some j => simp [e, MulEquiv.piOptionEquivProd]
      -- Apply the product formula
      rw [← comm, mulEquivHaarChar_trans, mulEquivHaarChar_trans]
      rw [mulEquivHaarChar_prodCongr]
      -- Use the induction hypothesis
      rw [IH (fun i => H (some i)) (fun i => ψ (some i))]
      -- Rearrange the product
      rw [Fintype.prod_option]
      rfl

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
