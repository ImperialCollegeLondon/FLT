# The spectral sequence of a filtered complex

This folder constructs, from scratch at module level, the spectral sequence of
a filtered differential module and of a filtered cochain complex, through to
the classical applications: convergence to the associated graded of
(co)homology, the five-term exact sequence of low-degree terms, and the two
spectral sequences of a first-quadrant double complex with their
`E₁ = column/row cohomology` identifications.

```lean
-- each page is the homology of the previous one
noncomputable def FilteredComplex.pageSuccEquiv ... :
    K.page (r + 1) p n ≃ₗ[R] (ker (K.dPage r p n) ⧸ ...)

-- convergence at a bounded spot: E_r^{p,n} ≅ gr^p H^n
noncomputable def FilteredComplex.pageEquivGrHOfBounded ...

-- the five-term exact sequence for a first-quadrant filtered complex
theorem FilteredComplex.five_term_exact (hK : K.FirstQuadrant) :
    Function.Injective K.f1 ∧ ... -- 0 → E₂^{1,0} → H¹ → E₂^{0,1} → E₂^{2,0} → H²

-- E₁ of the column filtration is vertical cohomology
noncomputable def DoubleComplex.colPageOneEquiv ...
```

## File Guide

- `FilteredModule.lean` — `FilteredDifferentialModule R M`: a module with a
  differential `d` (`d² = 0`) and a decreasing `ℤ`-filtration preserved by
  `d`. Pages `E_r^p = Z_r^p / B_r^p`, page differentials with `d_r² = 0`, the
  main theorem `pageSuccEquiv : E_{r+1}^p ≅ ker d_r / im d_r`, `E₀` = the
  associated graded, and the convergence theory: stabilization, the limit
  page, `E_∞ ≅ gr H` for bounded filtrations, one-sided unbounded results,
  functoriality and the mapping lemma.
- `FilteredComplex.lean` — the graded refinement `FilteredComplex R`
  (`ℤ`-indexed modules, differential of degree one, filtration `F^p`): graded
  pages `E_r^{p,n}`, the same main theorem per bidegree, and per-spot
  convergence `pageEquivGrHOfBounded : E_r^{p,n} ≅ gr^p H^n`.
- `FiveTerm.lean` — for first-quadrant filtered complexes: the transgression
  `d₂`, the edge maps, and `five_term_exact`:
  `0 → E₂^{1,0} → H¹ → E₂^{0,1} → E₂^{2,0} → H²`.
- `DoubleComplex.lean` — anticommuting double complexes, the total complex,
  the column and row filtrations (on literally the same total complex, so
  comparing the two abutments is `rfl`), first-quadrant boundedness, the
  identifications `E₀` = the double complex itself with `d₀ = dv` (resp.
  `dh`), the full first-page identifications `colPageOneEquiv` /
  `rowPageOneEquiv` (`E₁` = vertical/horizontal cohomology, FOAG §1.7), and
  the two five-term exact sequences `colFiltered_five_term_exact` /
  `rowFiltered_five_term_exact`.
- `ExactCoupleBridge.lean` — the exact couple of a filtered differential
  module, bridging to `FLT.Slop.ExactCouple`: `D^p = H(F^p M)`,
  `E^p = E₁^p`, the maps `i, j, k`, and the three exactness theorems
  `range_iMap_eq_ker_jMap`, `range_jMap_eq_ker_kMap`,
  `range_kMap_eq_ker_iMap`, per filtration degree.

## What Is Proved

Everything is for modules over an arbitrary ring, with `ℤ`-indexed decreasing
filtrations and no boundedness assumptions except where stated:

- The full page/differential calculus of a filtered differential module and
  of a filtered complex, with `E_{r+1} ≅ H(E_r, d_r)` at every page and spot.
- Convergence: `E_∞` and `E_r ≅ gr H` under (per-spot) boundedness; separated
  and exhaustive statements in the unbounded case; functoriality of pages and
  the mapping lemma (a filtered map inducing isomorphisms on one page does so
  on all later pages).
- The five-term exact sequence for any first-quadrant filtered complex, hence
  for both filtrations of any first-quadrant double complex.
- `E₁` of the column (row) filtration of a double complex *is* vertical
  (horizontal) cohomology, at the level of differentials and of pages.
- The per-degree exact couple of a filtered differential module.

## What Is Not Proved Here

- The per-degree exact couple is not assembled into a
  `GradedExactCouple` on `⨁_p H(F^p M)` (direct-sum packaging of the three
  exactness statements), and the pages of the iterated couple are not yet
  reconciled with the concrete `Z_r/B_r` pages — the classical comparison
  theorem. This is the natural next step for the `ExactCouple` folder.
- The abelian-category version of this machinery (it exists in the upstream
  development this folder is extracted from, over any abelian category via
  `Subobject`s, but is not part of this contribution).
- Unbounded *conditional* convergence (Boardman) and multiplicative
  structures.
- Adapters from mathlib's `HomologicalComplex`/`HomologicalComplex₂` (also
  existing upstream, not included here).

## Verification

`lake build FLT.Slop.SpectralSequence` compiles with no errors, no warnings,
and no `sorry`, and the following all report exactly
`[propext, Classical.choice, Quot.sound]`:

```lean
#print axioms FilteredDifferentialModule.pageSuccEquiv
#print axioms FilteredComplex.pageSuccEquiv
#print axioms FilteredComplex.five_term_exact
#print axioms DoubleComplex.colPageOneEquiv
#print axioms DoubleComplex.rowPageOneEquiv
#print axioms DoubleComplex.colFiltered_five_term_exact
#print axioms FilteredDifferentialModule.range_iMap_eq_ker_jMap
```

## Sources, and how the formalization deviates from them

1. Stacks Project, tags 012A (filtered differential objects) and 012K
   (filtered complexes) — the construction of the pages follows the Stacks
   presentation.
2. C. Weibel, *An Introduction to Homological Algebra*, §5.4–5.5; R. Vakil,
   *The Rising Sea* (FOAG), §1.7 — for double complexes and the five-term
   sequence.
3. Deviations chosen for formalization: the differential of a filtered
   complex is an "all-pairs" family `d i j` (only `d n (n+1)` is nonzero),
   and cycle/boundary submodules carry flexible index arguments, so that
   index arithmetic like `(n+1)-1 = n` rewrites an *argument* of a
   submodule-valued function rather than transporting along a type equality —
   the entire development is free of `Eq.rec`. The column and row filtrations
   of a double complex are filtrations of literally the same total complex,
   so the two spectral sequences converge to the same abutment by `rfl`.
   The five-term sequence is stated at concrete indices `0, 1, 2`, letting
   the kernel discharge the index arithmetic definitionally.

## Relation to existing formalizations

Mathlib's abstract `SpectralObject`/`SpectralSequence` frameworks (see the
discussion in `FLT/Slop/ExactCouple/README.md`) contain no spectral sequence
of a filtered complex of modules; the concrete construction here is
independent of them. The sibling folder `FLT/Slop/ExactCouple` provides
Massey's exact couples; `ExactCoupleBridge.lean` connects the two.

## Possible next steps

- Assemble `ExactCoupleBridge` into a `GradedExactCouple` on `⨁_p H(F^p M)`
  and reconcile the couple's pages with `Z_r/B_r`.
- The abelian-category version and the mathlib `HomologicalComplex` adapters.
- The Hochschild–Serre spectral sequence: the descended `G ⧸ S`-action on
  `H^q(S, A)` (the `E₂` coefficient system) is already available in the
  `FLT/Slop/HochschildSerre` development.
