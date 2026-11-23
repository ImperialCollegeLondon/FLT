# The spectral sequence of a filtered complex

This folder constructs the spectral sequence of a filtered differential module
and of a filtered cochain complex, using mathlib's standard complex and
bicomplex structures, through to
the classical applications: convergence to the associated graded of
(co)homology, the five-term exact sequence of low-degree terms, and the two
spectral sequences of a first-quadrant double complex with their
`E₁ = column/row cohomology` identifications.

```lean
-- each page is the homology of the previous one
noncomputable def FilteredComplex.pageSuccEquiv ... :
    K.page (r + 1) p n ≃ₗ[R] (ker (K.dPage r p n) ⧸ ...)

-- the concrete pages packaged in mathlib's categorical API
noncomputable def FilteredComplex.toCohomologicalSpectralSequence ... :
    CategoryTheory.CohomologicalSpectralSequence (ModuleCat R) r₀

-- convergence at a bounded spot: E_r^{p,n} ≅ gr^p H^n
noncomputable def FilteredComplex.pageEquivGrHOfBounded ...

-- the actual limit term has the same bounded identification
noncomputable def FilteredComplex.pageInfEquivGrH ...

-- the five-term exact sequence for a first-quadrant filtered complex
theorem FilteredComplex.five_term_exact (hK : K.IsFirstQuadrant) :
    Function.Injective K.f1 ∧ ... -- 0 → E₂^{1,0} → H¹ → E₂^{0,1} → E₂^{2,0} → H²

-- E₁ of the column filtration is vertical cohomology
noncomputable def DoubleComplex.colPageOneEquiv ...
```

## File Guide

- `FilteredModule.lean` — `FilteredDifferentialModule R M`: a module with a
  differential `d` (`d² = 0`) and a decreasing `ℤ`-filtration preserved by
  `d`. Pages `E_r^p = Z_r^p / B_r^p`, page differentials with `d_r² = 0`, the
  main theorem `pageSuccEquiv : E_{r+1}^p ≅ ker d_r / im d_r`, `E₀` = the
  associated graded, and the convergence theory: the limit term
  `E_∞ = (⋂ (Z_r + F^{p+1}))/(⋃ (B_r + F^{p+1}))` (formed in `E₀`), the separate
  associated-graded homology target, their identification under two-sided local
  bounds, bounded-page convergence, and one-sided unbounded results,
  functoriality and the mapping lemma.
- `FilteredComplex.lean` — the graded refinement `FilteredComplex R`, whose
  underlying object is a standard `CochainComplex (ModuleCat R) ℤ` equipped
  with a filtration by subcomplexes: graded pages `E_r^{p,n}`, the same main
  theorem per bidegree, and per-spot convergence
  `pageEquivGrHOfBounded : E_r^{p,n} ≅ gr^p H^n`.
- `FiveTerm.lean` — for first-quadrant filtered complexes: the transgression
  `d₂`, the edge maps, and `five_term_exact`:
  `0 → E₂^{1,0} → H¹ → E₂^{0,1} → E₂^{2,0} → H²`.
- `DoubleComplex.lean` — mathlib `HomologicalComplex₂` objects, their standard
  signed total differential, and column and row filtrations on the same
  concrete total complex (hence with definitionally the same underlying
  cohomology),
  first-quadrant boundedness, the
  identifications `E₀` = the double complex itself with `d₀ = dv` (resp.
  `dh`), the full first-page identifications `colPageOneEquiv` /
  `rowPageOneEquiv` (`E₁` = vertical/horizontal cohomology, FOAG §1.7), and
  the two five-term exact sequences `colFiltered_five_term_exact` /
  `rowFiltered_five_term_exact`.
- `ExactCoupleBridge.lean` — the exact couple of a filtered differential
  module, bridging to `FLT.Slop.ExactCouple`: `D^p = H(F^p M)`,
  `E^p = E₁^p`, the maps `i, j, k`, and the three exactness theorems
  `range_iMap_eq_ker_jMap`, `range_jMap_eq_ker_kMap`,
  `range_kMap_eq_ker_iMap`, assembled as
  `FilteredDifferentialModule.gradedExactCouple` on direct sums over the
  filtration degree.
- `CategoryTheory.lean` — packages each bigraded page as a
  `HomologicalComplex (ModuleCat R)` and the full construction as mathlib's
  `CategoryTheory.CohomologicalSpectralSequence`.

## What Is Proved

Everything is for modules over an arbitrary ring, with `ℤ`-indexed decreasing
filtrations and no boundedness assumptions except where stated:

- The full page/differential calculus of a filtered differential module and
  of a filtered complex, with `E_{r+1} ≅ H(E_r, d_r)` at every page and spot.
- Convergence: the true limit term `E_∞` is distinguished from the
  associated-graded homology target; under two-sided local bounds they are
  canonically isomorphic, and bounded finite pages satisfy `E_r ≅ gr H`.
  There are also separated and exhaustive statements in the unbounded case.
  Functoriality for `FilteredDifferentialModule.Hom` and its mapping lemma show
  that a filtered map inducing isomorphisms on one page does so on all later
  pages. `FilteredComplex.Hom` also induces maps on every page and a categorical
  page functor.
- The five-term exact sequence for any first-quadrant filtered complex, hence
  for both filtrations of any first-quadrant double complex.
- `E₁` of the column (row) filtration of a double complex *is* vertical
  (horizontal) cohomology, at the level of differentials and of pages.
- The graded exact couple of a filtered differential module, with `i`, `j`,
  and `k` of filtration degrees `-1`, `0`, and `1`.

## What Is Not Proved Here

- The pages of the iterated exact couple are not yet reconciled with the
  concrete `Z_r/B_r` pages; that is the classical comparison theorem.
- Naturality of `pageHomologyIso`, and hence a functor from filtered complexes
  to `CategoryTheory.SpectralSequence`. The categorical construction is
  packaged objectwise and is functorial page by page.
- The abelian-category version of this machinery (it exists in the upstream
  development this folder is extracted from, over any abelian category via
  `Subobject`s, but is not part of this contribution).
- Unbounded *conditional* convergence (Boardman) and multiplicative
  structures.

## Verification

`lake build FLT.Slop.SpectralSequence` compiles with no errors, no warnings,
and no `sorry`, and the following all report exactly
`[propext, Classical.choice, Quot.sound]`:

```lean
#print axioms Slop.FilteredDifferentialModule.pageSuccEquiv
#print axioms Slop.FilteredDifferentialModule.pageInfEquivGrHomology
#print axioms Slop.FilteredDifferentialModule.gradedExactCouple
#print axioms Slop.FilteredComplex.pageSuccEquiv
#print axioms Slop.FilteredComplex.pageInfEquivGrH
#print axioms Slop.FilteredComplex.toCohomologicalSpectralSequence
#print axioms Slop.FilteredComplex.five_term_exact
#print axioms Slop.DoubleComplex.totalIso
#print axioms Slop.DoubleComplex.colPageOneEquiv
#print axioms Slop.DoubleComplex.rowPageOneEquiv
#print axioms Slop.DoubleComplex.colFiltered_five_term_exact
#print axioms Slop.FilteredDifferentialModule.range_iMap_eq_ker_jMap
```

## Sources, and how the formalization deviates from them

1. Stacks Project, tags 012A (filtered differential objects) and 012K
   (filtered complexes) — the construction of the pages follows the Stacks
   presentation.
2. C. Weibel, *An Introduction to Homological Algebra*, §5.4–5.5; R. Vakil,
   *The Rising Sea* (FOAG), §1.7 — for double complexes and the five-term
   sequence.
3. Formalization choices: the underlying filtered complex uses mathlib's
   all-pairs `HomologicalComplex` differential (its shape axiom forces every
   nonconsecutive component to be zero), and cycle/boundary submodules carry
   flexible index arguments, so that
   index arithmetic like `(n+1)-1 = n` rewrites an *argument* of a
   submodule-valued function rather than transporting along a type equality.
   The column and row filtrations use literally the same total complex, so
   their underlying cohomology objects agree definitionally; the induced
   filtrations and associated-graded objects are different.
   The five-term sequence is stated at concrete indices `0, 1, 2`, letting
   the kernel discharge the index arithmetic definitionally.

## Relation to existing formalizations

Mathlib's abstract `SpectralObject`/`SpectralSequence` frameworks (see the
discussion in `FLT/Slop/ExactCouple/README.md`) do not themselves construct the
spectral sequence of a filtered complex of modules. The concrete construction
here is independent at the proof level, while `CategoryTheory.lean` packages
its pages and successor isomorphisms in mathlib's `SpectralSequence` API. The
sibling folder `FLT/Slop/ExactCouple` provides Massey's exact couples;
`ExactCoupleBridge.lean` connects the two.

## Possible next steps

- Reconcile the iterated exact couple's pages with the concrete `Z_r/B_r`
  construction.
- Develop the abelian-category version.
- The Hochschild–Serre spectral sequence: the descended `G ⧸ S`-action on
  `H^q(S, A)` (the `E₂` coefficient system) is already available in the
  `FLT/Slop/HochschildSerre` development.
