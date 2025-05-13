import Mathlib.MeasureTheory.Measure.Haar.DistribChar

open MeasureTheory.Measure
open scoped NNReal Pointwise ENNReal

namespace MeasureTheory

@[to_additive]
lemma isHaarMeasure_comap {G H : Type*}
    [Group G] [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [Group H] [TopologicalSpace H] [MeasurableSpace H] [BorelSpace H]
    (φ : G ≃ₜ* H) (μ : Measure H) [IsHaarMeasure μ] : IsHaarMeasure (comap φ μ) := sorry

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

@[to_additive existing]
noncomputable def mulEquivHaarChar : ℝ≥0 :=
  letI := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  haveI : IsHaarMeasure (comap φ haar) := isHaarMeasure_comap φ haar
  haarScalarFactor (comap φ haar) haar

variable [MeasurableSpace G] [BorelSpace G]
variable [MeasurableSpace A] [BorelSpace A]

@[to_additive]
lemma mulEquivHaarChar_eq (μ : Measure G) [IsHaarMeasure μ] :
    haveI : IsHaarMeasure (comap φ μ) := isHaarMeasure_comap φ μ
    mulEquivHaarChar φ = haarScalarFactor (comap φ μ) μ :=
  sorry -- MeasureTheory.Measure.haarScalarFactor_eq_mul

lemma addEquivAddHaarChar_mul_integral (μ : Measure A) [IsAddHaarMeasure μ]
    {f : A → ℝ} (hf : Measurable f) :
    (addEquivAddHaarChar ρ) * ∫ (a : A), f a ∂(comap ρ μ) = ∫ a, f a ∂μ := sorry

@[to_additive existing "addEquivAddHaarChar_mul_integral"]
lemma mulEquivHaarChar_mul_integral (μ : Measure G) [IsHaarMeasure μ]
    {f : G → ℝ} (hf : Measurable f) :
    (mulEquivHaarChar φ) * ∫ (a : G), f a ∂(comap φ μ) = ∫ a, f a ∂μ := sorry
    -- integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport

lemma addEquivAddHaarChar_mul_volume (μ : Measure A) [IsAddHaarMeasure μ]
    {X : Set A} (hX : MeasurableSet X) :
    μ (ρ '' X) = (addEquivAddHaarChar ρ) * μ X := sorry
    -- apply previous lemma to char fn of X
    -- Is it true in Lean without the assumption of measurability?

@[to_additive existing "addEquivAddHaarChar_mul_volume"]
lemma mulEquivHaarChar_mul_volume (μ : Measure G) [IsHaarMeasure μ]
    {X : Set G} (hX : MeasurableSet X) :
    μ (φ '' X) = (mulEquivHaarChar φ) * μ X := sorry
    -- apply previous lemma to char fn of X
    -- Is it true in Lean without the assumption of measurability?

@[to_additive]
lemma mulEquivHaarChar_refl : mulEquivHaarChar (ContinuousMulEquiv.refl G) = 1 := by
  sorry -- rfl

@[to_additive]
lemma mulEquivHaarChar_trans {φ ψ : G ≃ₜ* G} :
    mulEquivHaarChar (ψ.trans φ) = mulEquivHaarChar ψ * mulEquivHaarChar φ :=
  sorry -- MeasureTheory.Measure.haarScalarFactor_eq_mul
