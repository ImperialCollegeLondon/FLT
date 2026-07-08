/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.DimensionTheorem.Main

/-!
# Dimension theorem for Noetherian local rings

Umbrella module for the `FLT.Slop.DimensionTheorem` library. See
`FLT/Slop/DimensionTheorem/README.md` for an overview and sources.

The main result is `DimensionTheorem.dimension_theorem`
(`FLT/Slop/DimensionTheorem/Main.lean`): for a Noetherian local ring `(R, 𝔪)`, the
Krull dimension, the growth degree `d(R)` of the Hilbert–Samuel function
`n ↦ ℓ(R ⧸ 𝔪ⁿ)`, and the least number of generators `δ(R)` of an ideal of
definition all agree (Atiyah–Macdonald, Thm. 11.14; Stacks Project, tag 00KQ).

File overview:

* `FLT/Slop/DimensionTheorem/Numeric.lean` — arithmetic growth lemmas (telescoping,
  monomial counting); no ring theory.
* `FLT/Slop/DimensionTheorem/Defs.lean` — `hilbertSamuel`, `growthDeg` (= `d(R)`),
  `minGenPrimary` (= `δ(R)`); finiteness via Hopkins–Levitzki.
* `FLT/Slop/DimensionTheorem/DimEqDelta.lean` — `dim R = δ(R)`, from Mathlib's Krull
  height theorem and its converse.
* `FLT/Slop/DimensionTheorem/GrowthLeDelta.lean` — `d(R) ≤ δ(R)` by monomial counting.
* `FLT/Slop/DimensionTheorem/DimLeGrowth.lean` — `dim R ≤ d(R)` by Artin–Rees
  induction.
* `FLT/Slop/DimensionTheorem/Main.lean` — assembly of the cycle `dim ≤ d ≤ δ ≤ dim`.

The formalization deliberately phrases the Hilbert–Samuel side in terms of
polynomial growth (`GrowthLE`) rather than constructing the eventual
Hilbert–Samuel polynomial. Mathlib has a separate `Polynomial.hilbertPoly`
backend for rational functions of the form `p / (1 - X)^d`, but the graded
module theorem producing such a rational Hilbert series (Hilbert–Serre) is
not used here.
-/
