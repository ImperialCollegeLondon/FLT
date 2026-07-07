/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.DimensionTheorem.DimEqDelta
public import FLT.Slop.DimensionTheorem.DimLeGrowth
public import FLT.Slop.DimensionTheorem.GrowthLeDelta

/-!
# The dimension theorem for Noetherian local rings

For a Noetherian local ring `(R, 𝔪)`, the following three quantities coincide
(Atiyah–Macdonald, Thm. 11.14; Stacks Project, tag 00KQ):

* `dim R` — the Krull dimension (Mathlib's `ringKrullDim R`);
* `d(R)` — the growth degree of the Hilbert–Samuel function `n ↦ ℓ(R ⧸ 𝔪ⁿ)`
  (`growthDeg R`);
* `δ(R)` — the least number of generators of an ideal of definition, i.e. of
  an `𝔪`-primary ideal (`minGenPrimary R`).

The proof is the classical cycle `dim ≤ d ≤ δ ≤ dim`:

* `dim ≤ d` — Artin–Rees induction (`FLT/Slop/DimensionTheorem/DimLeGrowth.lean`);
* `d ≤ δ` — monomial counting (`FLT/Slop/DimensionTheorem/GrowthLeDelta.lean`);
* `δ ≤ dim` — existence of systems of parameters, from the converse of Krull's
  height theorem (`FLT/Slop/DimensionTheorem/DimEqDelta.lean`); the direct inequality
  `dim ≤ δ` (Krull's height theorem) is also proved there, so `dim = δ` does
  not depend on the Hilbert–Samuel machinery.

## Main results

* `DimensionTheorem.dimension_theorem` — `dim R = d(R)` and `dim R = δ(R)`.
* `DimensionTheorem.ringKrullDim_eq_growthDeg`, `ringKrullDim_le_growthDeg`,
  `growthDeg_eq_minGenPrimary` — the individual identities.

## Formal scope

This development identifies dimension with the polynomial-growth degree of the
Hilbert–Samuel function; it does **not** construct the eventual Hilbert–Samuel
polynomial itself (the Hilbert–Serre theorem), for which the growth-order and
polynomial-degree definitions of `d(R)` agree. The results depend only on the
standard axioms (`propext`, `Classical.choice`, `Quot.sound`); the development
is `sorry`-free.
-/

@[expose] public section

namespace DimensionTheorem

open IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- `dim R ≤ d(R)`. -/
theorem ringKrullDim_le_growthDeg :
    ringKrullDim R ≤ (growthDeg R : WithBot ℕ∞) :=
  ringKrullDim_le_of_growthLE (growthDeg R) R (growthLE_hilbertSamuel_growthDeg R)

/-- **The dimension theorem** for Noetherian local rings, first equality:
the Krull dimension equals the growth degree of the Hilbert–Samuel function. -/
theorem ringKrullDim_eq_growthDeg :
    ringKrullDim R = (growthDeg R : WithBot ℕ∞) := by
  refine le_antisymm (ringKrullDim_le_growthDeg R) ?_
  calc (growthDeg R : WithBot ℕ∞)
      ≤ (minGenPrimary R : WithBot ℕ∞) := by
        exact_mod_cast Nat.cast_le.mpr (growthDeg_le_minGenPrimary R)
    _ ≤ ringKrullDim R := minGenPrimary_le_ringKrullDim R

/-- **The dimension theorem** for Noetherian local rings:
`dim R = d(R) = δ(R)`. -/
theorem dimension_theorem :
    ringKrullDim R = (growthDeg R : WithBot ℕ∞) ∧
      ringKrullDim R = (minGenPrimary R : WithBot ℕ∞) :=
  ⟨ringKrullDim_eq_growthDeg R, ringKrullDim_eq_minGenPrimary R⟩

/-- The three quantities as natural numbers: `d(R) = δ(R)`. -/
theorem growthDeg_eq_minGenPrimary : growthDeg R = minGenPrimary R := by
  have h1 := ringKrullDim_eq_growthDeg R
  have h2 := ringKrullDim_eq_minGenPrimary R
  have := h1.symm.trans h2
  exact_mod_cast this

end DimensionTheorem
