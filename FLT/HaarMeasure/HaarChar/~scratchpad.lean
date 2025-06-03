import Mathlib
import FLT
import Mathlib.Data.ENNReal.Basic
--import Mathlib.MeasureTheory.Haar.Basic

open scoped BigOperators ENNReal
open MeasureTheory

/-!
# `mulEquivHaarChar_piCongrRight`

For a finite product of *locally-compact* groups `Π i, H i` and a family
`φ : Π i, H i ≃ₜ* H i`, the multiplicative Haar-character of the product
equivalence `piCongrRight φ` is the product of the individual characters.
This is the natural finite-product analogue of
`mulEquivHaarChar_prodCongr`.
-/

variable {ι : Type*} [Fintype ι]
variable {H : ι → Type*}

-- **Standing assumptions on every component group**
variable [∀ i, Group (H i)]
variable [∀ i, TopologicalSpace (H i)]
variable [∀ i, IsTopologicalGroup (H i)]
variable [∀ i, LocallyCompactSpace (H i)]

def mulEquivHaarChar {G H : Type*} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  [LocallyCompactSpace G] [LocallyCompactSpace H]
  (φ : G ≃ₜ* H) : ℝ≥0∞ := sorry

lemma Fintype.induction_empty_or_nonempty
  {P : ∀ {ι : Type*} [Fintype ι], (∀ i, H i) → Prop}
  (hempty : ∀ φ, P (ι := Empty) φ)
  (hstep : ∀ {ι₁ : Type*} (i₀ : ι) (h : ι₁ = { j // j ≠ i₀ })
           (IH : ∀ φ₁, P φ₁) (φ : (i : ι) → H i), P φ) :
  ∀ {ι : Type*} [Fintype ι] (φ : (i : ι) → H i), P φ := by
  sorry -- Implementation would go here

/--  **Multiplicativity of Haar-characters for finite products**. -/
lemma mulEquivHaarChar_piCongrRight
    (φ : (i : ι) → H i ≃ₜ* H i) :
    mulEquivHaarChar (piCongrRight φ) = ∏ i, mulEquivHaarChar (φ i) := by
  classical
  -- We perform induction on the finite index type `ι`.
  -- `Fintype.card` 0/1 gives the trivial and singleton cases automatically.
  -- The `nonempty` branch is the genuine inductive step.
  refine Fintype.induction_empty_or_nonempty _
    (fun _ ↦ by                      -- **empty product** (trivial group)
      simp [piCongrRight, Finset.prod_empty])
    (fun {ι₁ : Type*} (i₀ : ι) (ι₁fin : ι₁ = { j // j ≠ i₀ }) IH φ ↦ ?_) -- step
  -- Re-express `Π i, H i`  as  `H i₀ × Π j:ι₁, H j`, apply the binary lemma,
  -- then stitch things back together with the canonical re-indexing equiv.
  -- --------------------------------------------------------------------
  -- 1.  Split the index set
  let φ₁ : (j : {j // j ≠ i₀}) → H j ≃ₜ* H j := fun j ↦ φ j
  -- 2.  Induction hypothesis for the *smaller* product
  have IH' : mulEquivHaarChar (piCongrRight φ₁)
      = ∏ j, mulEquivHaarChar (φ₁ j) := by
    exact IH φ₁
  -- 3.  Binary product lemma for  `(φ i₀) × (Π j, φ₁ j)`
  have hProd : mulEquivHaarChar
        ((φ i₀).prodCongr (piCongrRight φ₁))
      = mulEquivHaarChar (φ i₀) * mulEquivHaarChar (piCongrRight φ₁) := by
    simpa using mulEquivHaarChar_prodCongr (φ i₀) (piCongrRight φ₁)
  -- 4.  Canonical coordinate-shuffle equivalence; its Haar-character is `1`
  --     because it merely re-orders factors.
  let reindex :
      (Π i, H i) ≃ₜ* (H i₀ × Π j, H j) :=
    (Homeomorph.piCongrRightSwap i₀ H).symm
  have hReindex : mulEquivHaarChar reindex = (1 : ℝ≥0∞) := by
    simpa using mulEquivHaarChar_coordinateSwap _ _
  -- 5.  `piCongrRight φ` is  `reindex.symm ≪≫ (φ i₀)×Πφ₁ ≪≫ reindex`
  --     so apply functoriality of Haar-characters twice
  simpa [IH', hProd, hReindex, Finset.prod_attach,
         Finset.prod_insert, Finset.mem_univ]
    using
      mulEquivHaarChar_conj reindex
        ((φ i₀).prodCongr (piCongrRight φ₁))
