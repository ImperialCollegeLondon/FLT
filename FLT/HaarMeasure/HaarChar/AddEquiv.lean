import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib

open MeasureTheory.Measure
open scoped NNReal

namespace MeasureTheory

@[to_additive]
lemma isHaarMeasure_comap {G H : Type*}
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    (φ : G ≃ₜ* H) (μ : Measure H) [IsHaarMeasure μ] : IsHaarMeasure (comap φ μ) := by
  sorry -- issue FLT#507

lemma regular_comap {G H : Type*}
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    (φ : G ≃ₜ H) (μ : Measure H) [Regular μ] : Regular (comap φ μ) := by
  sorry -- issue FLT#513

section basic

variable {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- If `φ : G ≃ₜ* G` then `mulEquivHaarChar φ` is the positive real factor by which
`φ` scales Haar measure on `G`. -/
@[to_additive "If `φ : A ≃ₜ+ A` then `addEquivAddHaarChar φ` is the positive
real factor by which `φ` scales Haar measure on `A`."]
noncomputable def mulEquivHaarChar (φ : G ≃ₜ* G) : ℝ≥0 :=
  letI := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  haveI : IsHaarMeasure (comap φ haar) := isHaarMeasure_comap φ haar
  haarScalarFactor (comap φ haar) haar

@[to_additive]
lemma mulEquivHaarChar_eq [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ]
    [LocallyCompactSpace G] [Regular μ] (φ : G ≃ₜ* G) :
    haveI : IsHaarMeasure (comap φ μ) := isHaarMeasure_comap φ μ
    mulEquivHaarChar φ = haarScalarFactor (comap φ μ) μ :=
  sorry -- FLT#508
  -- use MeasureTheory.Measure.haarScalarFactor_eq_mul
  -- and haarScalarFactor_pos_of_isHaarMeasure

-- do we need G locally compact? Feel free to add it if we do, but the linter was complaining.
lemma mulEquivHaarChar_comap [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsHaarMeasure μ] [Regular μ] (φ : G ≃ₜ* G) :
    comap φ μ = (mulEquivHaarChar φ) • μ := by
  haveI : Regular (comap φ μ) := regular_comap φ.toHomeomorph μ
  haveI : IsHaarMeasure (comap φ μ) := isHaarMeasure_comap φ μ
  rw [isMulLeftInvariant_eq_smul_of_regular (comap φ μ) μ, mulEquivHaarChar_eq μ φ]

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
lemma mulEquivHaarChar_refl : mulEquivHaarChar (ContinuousMulEquiv.refl G) = 1 := by
  simp [mulEquivHaarChar, Function.id_def]

@[to_additive]
lemma mulEquivHaarChar_trans {φ ψ : G ≃ₜ* G} :
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
lemma mulEquivHaarChar_prodCongr (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) :
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

@[to_additive]
lemma mulEquivHaarChar_piCongrRight [Fintype ι] (ψ : Π i, (H i) ≃ₜ* (H i)) :
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = ∏ i, mulEquivHaarChar (ψ i) := by
  sorry -- FLT#521 -- induction

end pi

section restrictedproductapi

open RestrictedProduct

variable {ι : Type*}
variable (R : ι → Type*) (A : (i : ι) → Set (R i))
variable {𝓕 : Filter ι}

lemma _root_.RestrictedProduct.coe_mk (x : Π i, R i) (hx : ∀ᶠ i in 𝓕, x i ∈ A i) (i : ι) :
    (id ⟨x, hx⟩ : Πʳ i, [R i, A i]_[𝓕]) i = x i := rfl

/-

@[to_additive (attr := simp)]
theorem coe_mk (f : M ≃ N) (hf : ∀ x y, f (x * y) = f x * f y) : (mk f hf : M → N) = f := rfl

-/


end restrictedproductapi

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
    -- Let Cᵢ ⊆ Gᵢ be a compact open subgroup for all i
    {C : (i : ι) → Subgroup (G i)} [Fact (∀ i, IsOpen (C i : Set (G i)))]
    (hCcompact : ∀ i, CompactSpace (C i))
    -- Let φᵢ : Gᵢ → Gᵢ be a multiplication-preserving homeomorphism
    (φ : (i : ι) → G i ≃ₜ* G i)
    -- and assume φᵢ(Cᵢ) = Cᵢ for all but finitely many i
    (hφ : ∀ᶠ i in Filter.cofinite, φ i ⁻¹' (C i : Set (G i)) = (C i : Set (G i)))

open RestrictedProduct

set_option linter.flexible false in
def ContinuousMulEquiv.restrictedProductCongrRight :
    (Πʳ i, [G i, C i]) ≃ₜ* (Πʳ i, [G i, C i]) where
  toFun x := ⟨fun i ↦ φ i (x i), sorry⟩
  invFun y := ⟨fun i ↦ (φ i).symm (y i), sorry⟩
  left_inv x := by
    ext i
    --refine RestrictedProduct.ext G (fun i ↦ ↑(C i)) fun i ↦ ?_
    simp only
    dsimp only
    change (φ i).symm (φ i (x i)) = x i
    exact ContinuousMulEquiv.symm_apply_apply (φ i) (x i)
  right_inv := sorry
  map_mul' := sorry
  continuous_toFun := sorry
  continuous_invFun := sorry

open ContinuousMulEquiv in
lemma mulEquivHaarChar_restrictedProductCongrRight :
    mulEquivHaarChar (restrictedProductCongrRight φ :(Πʳ i, [G i, C i]) ≃ₜ* (Πʳ i, [G i, C i])) =
    ∏ᶠ i, mulEquivHaarChar (φ i) := by
  sorry
