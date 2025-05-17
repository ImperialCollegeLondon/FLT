import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib

open MeasureTheory.Measure
open scoped NNReal

namespace MeasureTheory

@[to_additive]
lemma isHaarMeasure_comap {G H : Type*}
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    (φ : G ≃ₜ* H) (μ : Measure H) [IsHaarMeasure μ] : IsHaarMeasure (comap φ μ) :=
  sorry -- issue FLT#task001

/-- If `φ : A ≃ₜ+ A` then `addEquivAddHaarChar φ` is the positive real factor by which
`φ` scales Haar measure on `A`. -/
noncomputable def addEquivAddHaarChar {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    (φ : A ≃ₜ+ A): ℝ≥0 :=
  letI := borel A
  haveI : BorelSpace A := ⟨rfl⟩
  haveI : IsAddHaarMeasure (comap φ addHaar) := isAddHaarMeasure_comap φ addHaar
  addHaarScalarFactor (comap φ addHaar) (addHaar (G := A))

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G]
    (φ : G ≃ₜ* G)

variable {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    (ρ : A ≃ₜ+ A)

/-- If `φ : G ≃ₜ* G` then `mulEquivHaarChar φ` is the positive real factor by which
`φ` scales Haar measure on `G`. -/
@[to_additive existing]
noncomputable def mulEquivHaarChar : ℝ≥0 :=
  letI := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  haveI : IsHaarMeasure (comap φ haar) := isHaarMeasure_comap φ haar
  haarScalarFactor (comap φ haar) haar

@[to_additive]
lemma mulEquivHaarChar_eq [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ] :
    haveI : IsHaarMeasure (comap φ μ) := isHaarMeasure_comap φ μ
    mulEquivHaarChar φ = haarScalarFactor (comap φ μ) μ :=
  sorry -- FLT#task002
  -- use MeasureTheory.Measure.haarScalarFactor_eq_mul?

lemma addEquivAddHaarChar_mul_integral [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [IsAddHaarMeasure μ]
    {f : A → ℝ} (hf : Measurable f) :
    (addEquivAddHaarChar ρ) * ∫ (a : A), f a ∂(comap ρ μ) = ∫ a, f a ∂μ := sorry -- FLT#task004
    -- integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport

@[to_additive existing "addEquivAddHaarChar_mul_integral"]
lemma mulEquivHaarChar_mul_integral [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ]
    {f : G → ℝ} (hf : Measurable f) :
    (mulEquivHaarChar φ) * ∫ (a : G), f a ∂(comap φ μ) = ∫ a, f a ∂μ := sorry -- FLT#task004
    -- integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport

lemma addEquivAddHaarChar_mul_volume [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [IsAddHaarMeasure μ]
    {X : Set A} (hX : MeasurableSet X) :
    μ (ρ '' X) = (addEquivAddHaarChar ρ) * μ X := sorry -- FLT#task003
    -- apply previous lemma to char fn of X
    -- Is it true in Lean without the assumption of measurability?

@[to_additive existing "addEquivAddHaarChar_mul_volume"]
lemma mulEquivHaarChar_mul_volume [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ]
    {X : Set G} (hX : MeasurableSet X) :
    μ (φ '' X) = (mulEquivHaarChar φ) * μ X := sorry -- FLT#task003
    -- apply previous lemma to char fn of X
    -- Is it true in Lean without the assumption of measurability?

@[to_additive]
lemma mulEquivHaarChar_refl : mulEquivHaarChar (ContinuousMulEquiv.refl G) = 1 := by
  simp [mulEquivHaarChar, Function.id_def]

@[to_additive]
lemma mulEquivHaarChar_trans {φ ψ : G ≃ₜ* G} :
    mulEquivHaarChar (ψ.trans φ) = mulEquivHaarChar ψ * mulEquivHaarChar φ :=
  sorry -- FLT#task005
  -- MeasureTheory.Measure.haarScalarFactor_eq_mul

section prodCongr

variable {A B C D : Type*} [Group A] [Group B] [Group C] [Group D]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]

@[to_additive ContinuousAddEquiv.prodCongr]
def _root_.ContinuousMulEquiv.prodCongr (φ : A ≃ₜ* B) (ψ : C ≃ₜ* D) : A × C ≃ₜ* B × D where
  __ := φ.toMulEquiv.prodCongr ψ
  continuous_toFun := sorry -- FLt#task013
  continuous_invFun := sorry -- FLT#task013

end prodCongr

section prod

variable {H : Type*} [CommGroup H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H]
    (ψ : H ≃ₜ* H)

@[to_additive MeasureTheory.addEquivAddHaarChar_prodCongr]
lemma mulEquivHaarChar_prodCongr :
    mulEquivHaarChar (φ.prodCongr ψ) = mulEquivHaarChar φ * mulEquivHaarChar ψ := by
  sorry -- FLT#task014

end prod

section piCongrRight

variable {ι : Type*} {G H : ι → Type*}
    [Π i, CommGroup (G i)] [Π i, TopologicalSpace (G i)]
    [Π i, CommGroup (H i)] [Π i, TopologicalSpace (H i)]

-- should be in mathlib?
@[to_additive ContinuousAddEquiv.piCongrRight]
def _root_.ContinuousMulEquiv.piCongrRight (ψ : Π i, (G i) ≃ₜ* (H i)) :
    (∀ i, G i) ≃ₜ* (∀ i, H i) where
  __ := MulEquiv.piCongrRight (fun i ↦ ψ i)
  continuous_toFun := sorry -- FLT#task015
  continuous_invFun := sorry -- FLT#task015

end piCongrRight

section pi

variable {ι : Type*} {H : ι → Type*} [Π i, CommGroup (H i)] [Π i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, LocallyCompactSpace (H i)]

@[to_additive MeasureTheory.addEquivAddHaarChar_piCongrRight]
lemma mulEquivHaarChar_piCongrRight [Fintype ι] (ψ : Π i, (H i) ≃ₜ* (H i)) :
    mulEquivHaarChar (ContinuousMulEquiv.piCongrRight ψ) = ∏ i, mulEquivHaarChar (ψ i) := by
  sorry -- FLT#task016 -- induction

end pi
