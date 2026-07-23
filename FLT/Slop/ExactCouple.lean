/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.ExactCouple.Graded

/-!
# Exact couples and their spectral sequences

Umbrella module for the `FLT.Slop.ExactCouple` library.  See
`FLT/Slop/ExactCouple/README.md` for an overview and sources.

An exact couple (Massey, 1952) is the most economical input datum for a
spectral sequence: modules `D`, `E` with maps `i : D → D`, `j : D → E`,
`k : E → D`, exact at each vertex.  The main results:

* `ExactCouple.derivedCouple` (`FLT/Slop/ExactCouple/Basic.lean`) — the
  derived-couple theorem: `D' = im i`, `E' = ker(jk)/im(jk)` with the induced
  maps again form an exact couple; iterating gives the pages of a spectral
  sequence with `page (r + 1) = H(page r, d_r)` holding by construction
  (`ExactCouple.pageSuccEquiv` is definitionally the identity).
* `GradedExactCouple.gradedDerived` (`FLT/Slop/ExactCouple/Graded.lean`) — the
  graded upgrade: if `D`, `E` are internal direct sums graded by an abelian
  group of degrees and `i, j, k` are homogeneous of degrees `di, dj, dk`, each
  derived couple is again graded and the `r`-th page differential is homogeneous
  of degree
  `(dj + dk) - r • di` (`GradedExactCouple.gradedDerived_homog_d`) — the
  classical bidegree bookkeeping (for the couple of a filtered complex, whose
  page `0` is the classical `E₁`, this degree is `(r + 1, -r)`, the bidegree
  of the classical `d_{r+1}`).
-/
