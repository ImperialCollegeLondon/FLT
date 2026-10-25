/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.SpectralSequence.CategoryTheory
public import FLT.Slop.SpectralSequence.DoubleComplex
public import FLT.Slop.SpectralSequence.ExactCoupleBridge

/-!
# The spectral sequence of a filtered complex

Umbrella module for the `FLT.Slop.SpectralSequence` library: the spectral
sequence of a filtered differential module and of a filtered cochain complex,
following the Stacks Project (tags 012A and 012K).

* `FLT.Slop.SpectralSequence.FilteredModule` — the pages, differentials,
  `E_{r+1} ≅ H(E_r, d_r)` (`FilteredDifferentialModule.pageSuccEquiv`) and the
  convergence theory of a filtered differential module.
* `FLT.Slop.SpectralSequence.FilteredComplex` — the graded refinement for a
  filtered cochain complex (`FilteredComplex.pageSuccEquiv`,
  `FilteredComplex.pageEquivGrHOfBounded`).
* `FLT.Slop.SpectralSequence.FiveTerm` — the five-term exact sequence of
  low-degree terms (`FilteredComplex.five_term_exact`).
* `FLT.Slop.SpectralSequence.DoubleComplex` — the two spectral sequences of a
  first-quadrant double complex (`DoubleComplex.colPageOneEquiv`,
  `DoubleComplex.rowPageOneEquiv`, `DoubleComplex.colFiltered_five_term_exact`).
* `FLT.Slop.SpectralSequence.ExactCoupleBridge` — the exact couple of a
  filtered differential module
  (`FilteredDifferentialModule.gradedExactCouple`), bridging to
  `FLT.Slop.ExactCouple`.
* `FLT.Slop.SpectralSequence.CategoryTheory` — packages the concrete pages as
  mathlib's `CategoryTheory.CohomologicalSpectralSequence` via
  `FilteredComplex.toCohomologicalSpectralSequence`.
-/
