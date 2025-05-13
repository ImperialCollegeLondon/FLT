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

variable {A : Type*} [CommGroup A] [TopologicalSpace A]
    [IsTopologicalGroup A] [LocallyCompactSpace A]
    (φ : A ≃ₜ* A)

@[to_additive existing]
noncomputable def mulEquivHaarChar : ℝ≥0 :=
  letI := borel A
  haveI : BorelSpace A := ⟨rfl⟩
  haveI : IsHaarMeasure (comap φ haar) := isHaarMeasure_comap φ haar
  haarScalarFactor (comap φ haar) (haar (G := A))

variable [MeasurableSpace A] [BorelSpace A]

@[to_additive]
lemma mulEquivHaarChar_eq (μ : Measure A) [IsHaarMeasure μ] :
    haveI : IsHaarMeasure (comap φ μ) := isHaarMeasure_comap φ μ
    mulEquivHaarChar φ = haarScalarFactor (comap φ μ) μ :=
  sorry



@[to_additive]
lemma mulEquivHaarChar_refl : mulEquivHaarChar (ContinuousMulEquiv.refl A) = 1 := by
  sorry

@[to_additive]
lemma mulEquivHaarChar_comp {φ ψ : A ≃ₜ* A} :
    mulEquivHaarChar (ψ.trans φ) = mulEquivHaarChar ψ * mulEquivHaarChar φ :=
  sorry
