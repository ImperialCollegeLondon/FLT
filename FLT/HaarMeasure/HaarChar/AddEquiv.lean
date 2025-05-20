import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib
import FLT.Mathlib.MeasureTheory.Measure.Comap

open MeasureTheory.Measure
open scoped NNReal

namespace MeasureTheory

open Topology in
@[to_additive]
lemma isHaarMeasure_comap_of_isOpenEmbedding {G H : Type*}
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    {φ : G →* H} (hφ : IsOpenEmbedding φ) (μ : Measure H) [IsHaarMeasure μ] :
    IsHaarMeasure (comap φ μ) := by
  sorry -- issue FLT#507

@[to_additive]
lemma _root_.ContinuousMulEquiv.isHaarMeasure_comap {G H : Type*}
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    (φ : G ≃ₜ* H) (μ : Measure H) [IsHaarMeasure μ] : IsHaarMeasure (comap φ μ) :=
  isHaarMeasure_comap_of_isOpenEmbedding (φ := φ.toMulEquiv.toMonoidHom)
  (φ.toHomeomorph.isOpenEmbedding) μ

open Topology in
lemma regular_comap_of_isOpenEmbedding {G H : Type*}
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    (φ : G → H) (hφ : IsOpenEmbedding φ) (μ : Measure H) [Regular μ] : Regular (comap φ μ) := by
  sorry -- issue FLT#513

lemma _root_.Homeomorph.regular_comap {G H : Type*}
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    (φ : G ≃ₜ H) (μ : Measure H) [Regular μ] : Regular (comap φ μ) :=
  regular_comap_of_isOpenEmbedding φ φ.isOpenEmbedding μ

section basic

variable {G : Type*} [Group G] [TopologicalSpace G]

@[to_additive]
lemma IsHaarMeasure.nnreal_smul [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
    [h : IsHaarMeasure μ] {c : ℝ≥0} (hc : 0 < c) : IsHaarMeasure (c • μ) :=
  h.smul _ (by simp [hc.ne']) (not_eq_of_beq_eq_false rfl)

variable [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- If `φ : G ≃ₜ* G` then `mulEquivHaarChar φ` is the positive real factor by which
`φ` scales Haar measure on `G`. -/
@[to_additive "If `φ : A ≃ₜ+ A` then `addEquivAddHaarChar φ` is the positive
real factor by which `φ` scales Haar measure on `A`."]
noncomputable def mulEquivHaarChar [MeasurableSpace G] [BorelSpace G] (φ : G ≃ₜ* G) : ℝ≥0 :=
  haarScalarFactor haar (map φ haar)

@[to_additive]
lemma smul_haarScalarFactor_smul [MeasurableSpace G] [BorelSpace G] (μ' μ : Measure G)
    [IsHaarMeasure μ] [IsFiniteMeasureOnCompacts μ'] [IsMulLeftInvariant μ'] {c : ℝ≥0}
    (hc : 0 < c) :
    letI : IsHaarMeasure (c • μ) := IsHaarMeasure.nnreal_smul hc
    haarScalarFactor (c • μ') (c • μ) = haarScalarFactor μ' μ := by
  letI : IsHaarMeasure (c • μ) := IsHaarMeasure.nnreal_smul hc
  obtain ⟨⟨g, g_cont⟩, g_comp, g_nonneg, g_one⟩ :
    ∃ g : C(G, ℝ), HasCompactSupport g ∧ 0 ≤ g ∧ g 1 ≠ 0 := exists_continuous_nonneg_pos 1
  have int_g_ne_zero : ∫ x, g x ∂μ ≠ 0 :=
    ne_of_gt (g_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero g_comp g_nonneg g_one)
  apply NNReal.coe_injective
  calc
    ((c • μ').haarScalarFactor (c • μ)) = (∫ x, g x ∂(c • μ')) / ∫ x, g x ∂(c • μ) :=
      haarScalarFactor_eq_integral_div _ _ g_cont g_comp (by simp [int_g_ne_zero, hc.ne'])
    _ = (c • (∫ x, g x ∂μ')) / (c • ∫ x, g x ∂μ) := by simp
    _ = (∫ x, g x ∂μ') / (∫ x, g x ∂μ) := by
      rw [NNReal.smul_def, NNReal.smul_def, smul_eq_mul, smul_eq_mul]
      exact mul_div_mul_left (∫ (x : G), g x ∂μ') (∫ (x : G), g x ∂μ) (by simp [hc.ne'])
    _ = μ'.haarScalarFactor μ :=
      (haarScalarFactor_eq_integral_div _ _ g_cont g_comp int_g_ne_zero).symm

@[to_additive]
lemma mulEquivHaarChar_eq [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ]
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
  have := haarScalarFactor_pos_of_isHaarMeasure haar μ
  simp_rw [MeasureTheory.Measure.map_smul]
  apply smul_haarScalarFactor_smul
  exact this

-- do we need G locally compact? Feel free to add it if we do, but the linter was complaining.
lemma mulEquivHaarChar_comap [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) :
    (mulEquivHaarChar φ) • map φ μ = μ := by
  haveI : Regular (map φ μ) := sorry
  haveI : IsHaarMeasure (comap φ μ) := φ.isHaarMeasure_comap μ
  rw [mulEquivHaarChar_eq μ φ]
  exact (isMulLeftInvariant_eq_smul_of_regular μ (map φ μ)).symm

@[to_additive addEquivAddHaarChar_mul_integral]
lemma mulEquivHaarChar_mul_integral [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsHaarMeasure μ] {f : G → ℝ} (hf : Measurable f) (φ : G ≃ₜ* G) :
    ∫ (a : G), f a ∂(comap φ μ) = (mulEquivHaarChar φ) * ∫ a, f a ∂μ := sorry -- FLT#510
  -- use mulEquivHaarChar_comap. Is measurability needed?

@[to_additive addEquivAddHaarChar_mul_volume]
lemma mulEquivHaarChar_mul_volume [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsHaarMeasure μ] {X : Set G} (hX : MeasurableSet X) (φ : G ≃ₜ* G) :
    μ (φ '' X) = (mulEquivHaarChar φ) * μ X := sorry -- FLT#509,
    -- use MeasureTheory.Measure.comap_apply. Is measurability of X needed?

@[to_additive]
lemma mulEquivHaarChar_refl [MeasurableSpace G] [BorelSpace G] :
    mulEquivHaarChar (ContinuousMulEquiv.refl G) = 1 := by
  simp [mulEquivHaarChar, Function.id_def]

@[to_additive]
lemma mulEquivHaarChar_trans [MeasurableSpace G] [BorelSpace G] {φ ψ : G ≃ₜ* G} :
    mulEquivHaarChar (ψ.trans φ) = mulEquivHaarChar ψ * mulEquivHaarChar φ :=
  sorry -- FLT#511
  -- use `MeasureTheory.Measure.haarScalarFactor_eq_mul`?

end basic

section prodCongr

variable {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]

example (f : A → B) (g : C → D) (hf : Continuous f) (hg : Continuous g) :
  Continuous (Prod.map f g) := by exact Continuous.prodMap hf hg
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
@[to_additive ContinuousAddEquiv.piCongrRight "An arbitrary product of
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

@[to_additive]
lemma mulEquivHaarChar_piCongrRight [Fintype ι] (ψ : Π i, (H i) ≃ₜ* (H i)) :
    letI : MeasurableSpace (Π i, H i) := borel _
    haveI : BorelSpace (Π i, H i) := ⟨rfl⟩
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = ∏ i, mulEquivHaarChar (ψ i) := by
  sorry -- FLT#521 -- induction

end pi

end MeasureTheory

section restrictedproductapi

namespace RestrictedProduct

variable {ι : Type*}
variable {R : ι → Type*} {A : (i : ι) → Set (R i)}
variable {𝓕 : Filter ι}

abbrev mk (x : Π i, R i) (hx : ∀ᶠ i in 𝓕, x i ∈ A i) : Πʳ i, [R i, A i]_[𝓕] :=
  ⟨x, hx⟩

@[simp]
lemma mk_apply (x : Π i, R i) (hx : ∀ᶠ i in 𝓕, x i ∈ A i) (i : ι) :
    (mk x hx) i = x i := rfl

@[simp]
lemma mul_apply {S : ι → Type*} [(i : ι) → SetLike (S i) (R i)] {B : (i : ι) → S i}
    [(i : ι) → Mul (R i)] [∀ (i : ι), MulMemClass (S i) (R i)]
    (x y : Πʳ (i : ι), [R i, ↑(B i)]_[𝓕]) (i : ι) : (x * y) i = x i * y i := rfl

end RestrictedProduct

end restrictedproductapi

namespace MeasureTheory

section restrictedproduct

open ENNReal

example (X : Type*) [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
    [IsHaarMeasure μ] [Regular μ] (C : Set X) [Nonempty C]
    (hCopen : IsOpen C) (hCcompact : IsCompact C) :
    0 < μ C ∧ μ C < ∞ := by
  constructor
  · exact IsOpen.measure_pos μ hCopen Set.Nonempty.of_subtype
  · exact IsCompact.measure_lt_top hCcompact

variable
    -- let ι be an index set.
    {ι : Type*}
    -- Let Gᵢ be a family of locally compact abelian groups
    {G : ι → Type*} [Π i, Group (G i)] [Π i, TopologicalSpace (G i)]
    [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)]
    [∀ i, MeasurableSpace (G i)] [∀ i, BorelSpace (G i)]
    -- Let Cᵢ ⊆ Gᵢ be a compact open subgroup for all i
    {C : (i : ι) → Subgroup (G i)} [Fact (∀ i, IsOpen (C i : Set (G i)))]
    (hCcompact : ∀ i, CompactSpace (C i))
    -- Let φᵢ : Gᵢ → Gᵢ be a multiplication-preserving homeomorphism
    (φ : (i : ι) → G i ≃ₜ* G i)
    -- and assume φᵢ(Cᵢ) = Cᵢ for all but finitely many i
    (hφ : ∀ᶠ i in Filter.cofinite, φ i ⁻¹' (C i : Set (G i)) = (C i : Set (G i)))

open RestrictedProduct

def ContinuousMulEquiv.restrictedProductCongrRight :
    (Πʳ i, [G i, C i]) ≃ₜ* (Πʳ i, [G i, C i]) where
  toFun x := ⟨fun i ↦ φ i (x i), sorry⟩
  invFun y := ⟨fun i ↦ (φ i).symm (y i), sorry⟩
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp
  map_mul' x₁ x₂ := by ext; simp
  continuous_toFun := sorry
  continuous_invFun := sorry

open Topology in
@[to_additive]
lemma mulEquivHaarChar_eq_mulEquivHaarChar_of_isOpenEmbedding {X Y : Type*}
    [TopologicalSpace X] [Group X] [IsTopologicalGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [Group Y] [IsTopologicalGroup Y] [LocallyCompactSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    {f : X →* Y} (hf : IsOpenEmbedding f) (α : X ≃ₜ* X) (β : Y ≃ₜ* Y)
    (hComm : ∀ x, f (α x) = β (f x)) : mulEquivHaarChar α = mulEquivHaarChar β := by
  sorry

open ContinuousMulEquiv in
lemma mulEquivHaarChar_restrictedProductCongrRight :
    letI : MeasurableSpace (Πʳ i, [G i, C i]) := borel _
    haveI : BorelSpace (Πʳ i, [G i, C i]) := ⟨rfl⟩
    mulEquivHaarChar (restrictedProductCongrRight φ :(Πʳ i, [G i, C i]) ≃ₜ* (Πʳ i, [G i, C i])) =
    ∏ᶠ i, mulEquivHaarChar (φ i) := by
  letI : MeasurableSpace (Πʳ i, [G i, C i]) := borel _
  haveI : BorelSpace (Πʳ i, [G i, C i]) := ⟨rfl⟩
  -- -- the below code creates a compact open in the restricted product and shows
  -- it has Haar measure 0 < μ < ∞ but I'm not sure I want to go this way
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
  sorry

-- #check Set.pi
