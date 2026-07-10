# Exact couples and their spectral sequences

This folder formalizes exact couples, the derived-couple theorem, and the
resulting spectral sequence, together with the graded (bidegree) bookkeeping.

An exact couple consists of `R`-modules `D`, `E` and maps `i : D → D`,
`j : D → E`, `k : E → D`, exact at each vertex of the triangle. The
differential `d = j ∘ k` satisfies `d² = 0`, and the derived couple

```lean
noncomputable def ExactCouple.derivedCouple : ExactCouple R
-- D' = im i,  E' = ker d / im d,  with the induced maps i', j', k'
```

is again an exact couple — the three exactness proofs
(`derived_exact_ij`, `derived_exact_jk`, `derived_exact_ki`) are the
derived-couple theorem. Iterating yields the spectral sequence:

```lean
noncomputable def ExactCouple.derived : ℕ → ExactCouple R
noncomputable def ExactCouple.pageSuccEquiv (r : ℕ) :
    C.page (r + 1) ≃ₗ[R] (ker (C.pageDiff r) ⧸ (range (C.pageDiff r)).comap _)
-- E_{r+1} ≃ ker d_r / im d_r, definitionally the identity map
```

In the graded upgrade, `D` and `E` carry gradings by an arbitrary abelian
group `ι` of degrees (`ℤ`, `ℤ × ℤ`, …), with `i, j, k` homogeneous of degrees
`di, dj, dk` and the `D`-grading internally direct. Then each derived couple
is again graded, `j'` drops degree by `di`, and

```lean
theorem GradedExactCouple.gradedDerived_homog_d (r : ℕ) (p : ι) :
    ((C.gradedDerived r).gradE p).map (C.gradedDerived r).d ≤
      (C.gradedDerived r).gradE (p + ((C.dj + C.dk) - r • C.di))
-- deg d_r = (dj + dk) - r • di
```

For the exact couple of a filtered complex one has `ι = ℤ × ℤ` and
`di = (-1, 1)`, `dj = (0, 0)`, `dk = (1, 0)`, and page `r` of the couple is
the classical page `E_{r+1}`; the closed form gives its differential the
degree `(r + 1, -r)` — the familiar bidegree of the classical
`d_{r+1} : E_{r+1}^{p,q} → E_{r+1}^{p+r+1, q-r}`.

## File Guide

- `Basic.lean` defines `ExactCouple R` (a bundled structure: two modules and
  three exact maps), the differential `d = j ∘ k` with `d² = 0`, the derived
  couple (`D' = im i`; `E' = ker d / im d`; `i'` the restriction of `i`; `j'`
  induced via the first isomorphism theorem from `x ↦ [j x]`, which kills
  `ker i = im k`; `k'` induced by `[e] ↦ k e`), the three exactness proofs,
  and the iterated pages `derived`, `page`, `pageDiff` with
  `pageDiff_comp_pageDiff` (`d_r² = 0`) and `pageSuccEquiv`.
- `Graded.lean` defines `GradedExactCouple R ι` (extending `ExactCouple R` by
  gradings and degree data), proves the homogeneous-image lemma
  `DirectSum.IsInternal.inf_range_le_map` (a homogeneous element in the
  image of a homogeneous endomorphism is the image of a homogeneous element —
  the reason `j'` drops degree), the homogeneity of the derived maps, the
  bidegree drop `derivedCouple_homog_d`, the fact that `im i` is a graded
  submodule (`isInternal_derGradD` — what makes the construction iterable),
  and the iteration `gradedDerived` with the closed form
  `gradedDerived_homog_d`. The graded and ungraded iterations agree
  (`gradedDerived_toExactCouple`), so the degree information applies to the
  pages of the underlying couple.

## What Is Proved

Over an arbitrary (not necessarily commutative) ring `R`, with `D` and `E` in
a common universe independent of the universe of `R`:

- The derived couple of an exact couple is an exact couple (Massey's
  derived-couple theorem).
- The iterated pages form a spectral sequence in the literal sense that
  `E_{r+1}` **is** (definitionally) the homology `ker d_r / im d_r` of the
  previous page.
- In the graded setting, only internal directness of the `D`-grading is
  needed; the `E`-grading may be arbitrary. Each derivation preserves the
  degrees of `i` and `k`, drops the degree of `j` by `di`, and the `r`-th
  differential is homogeneous of degree `(dj + dk) - r • di`.

## What Is Not Proved Here

- No concrete exact couple is constructed in this folder (no instance from a
  filtered complex, a double complex, or a Bockstein short exact sequence).
  A construction of the per-degree exact couple of a filtered differential
  module (`D^p = H(F^p M)`, `E^p = E₁^p`, with the three exactness
  statements) exists in draft form outside this repository; assembling it
  into a `GradedExactCouple` on `⨁_p H(F^p M)` and reconciling the resulting
  pages with the classical `Z_r/B_r` description is the natural next step.
- Nothing about convergence or abutments.
- No comparison with Mathlib's abstract `SpectralObject` framework.

## Verification

`lake build FLT.Slop.ExactCouple` compiles with no errors, no warnings, and
no `sorry`, and

```lean
#print axioms ExactCouple.derivedCouple
-- [propext, Classical.choice, Quot.sound]

#print axioms GradedExactCouple.gradedDerived_homog_d
-- [propext, Classical.choice, Quot.sound]
```

## Sources, and how the formalization deviates from them

1. W. S. Massey, *Exact couples in algebraic topology*, Ann. of Math. 56
   (1952), 363–396 — the origin of exact couples and the derived couple.
2. Stacks Project, tag 011P (exact couples and their spectral sequences); the
   construction here follows the Stacks presentation at module level, and
   `ExactCouple.derivedCouple` carries the `@[stacks 011P]` attribute.
3. C. Weibel, *An Introduction to Homological Algebra*, §5.9; J. McCleary,
   *A User's Guide to Spectral Sequences*, §2.2 — for the graded/bidegree
   bookkeeping.
4. Deviations: the couple is ungraded by default, with the grading added as a
   layer (`GradedExactCouple`) rather than baked in; degrees live in an
   arbitrary abelian group `ι` rather than `ℤ × ℤ`, so single gradings,
   bigradings, and multigradings are all instances. Only the `D`-grading is
   required to be internally direct — the textbooks assume both, but the
   derived-couple degree bookkeeping never uses directness of the
   `E`-grading, and weakening the hypothesis makes the iteration cleaner.

## Relation to existing formalizations

Mathlib has an abstract `SpectralObject` framework
(`Mathlib/Algebra/Homology/SpectralObject/`), with instances coming from
t-structures on triangulated categories and from the mapping-cone spectral
object of a functor `ι ⥤ CochainComplex C ℤ` in the homotopy category
(`Mathlib/Algebra/Homology/HomotopyCategory/SpectralObject.lean`). It also
has an abstract `CategoryTheory.SpectralSequence` structure
(`Mathlib/Algebra/Homology/SpectralSequence/Basic.lean`) recording pages
together with isomorphisms `E_{r+1} ≅ H(E_r)`. Neither development contains
exact couples, and no spectral sequence of a filtered complex of modules is
derived from them in mathlib. This folder is independent of both; packaging
the pages of an `ExactCouple` as a `CategoryTheory.SpectralSequence` in
`ModuleCat R` would be a natural compatibility layer when upstreaming.

## Possible next steps

- The exact couple of a filtered differential module / filtered complex, as a
  `GradedExactCouple` over `ι = ℤ`, and the identification of its pages with
  the classical `Z_r^p / B_r^p`.
- The Bockstein exact couple of `0 → ℤ/p → ℤ/p² → ℤ/p → 0`.
- Convergence statements (bounded filtrations, `E_∞` and the abutment).
