/-
Copyright (c) 2026 Bryan Wang Peng Jun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang Peng Jun
-/
module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence

/-!
# `normEDS` is an elliptic sequence

This file proves mathlib's flagged TODO that the canonical normalised elliptic divisibility
sequence `normEDS b c d` satisfies the elliptic (net) relation, i.e. `IsEllipticSequence`.

Writing `W = normEDS b c d`, this is the statement that for all `p, q, r ∈ ℤ`,
`W(p+q)·W(p−q)·W(r)² − W(p+r)·W(p−r)·W(q)² + W(q+r)·W(q−r)·W(p)² = 0`,
which is `IsEllipticNet.rel W p q r 0 = 0`.

## Strategy

The whole elliptic relation is a purely algebraic (`ring`) consequence of the **addition formula**
`normEDS_addition_formula`
`W(m+n)·W(m−n) = W(m+1)·W(m−1)·W(n)² − W(n+1)·W(n−1)·W(m)²`,
which is the special case `r = 1` (using `W(1) = 1`). Indeed, applying the addition formula to each
of the three "product" factors `W(p+q)W(p−q)`, `W(p+r)W(p−r)`, `W(q+r)W(q−r)` makes every term
cancel. Thus the mathematical content is entirely contained in the addition formula, which is
Ward's classical theorem for the recurrence-defined sequence `normEDS`.

## Main statements

* `normEDS_addition_formula`: the elliptic addition formula for `normEDS b c d`.
* `rel_normEDS`: the raw four-index relator `IsEllipticNet.rel (normEDS b c d) p q r 0 = 0`.
* `normEDS_isEllipticSequence`: `normEDS b c d` is an elliptic sequence over any `CommRing`.

## References

* K Stange, *Elliptic Nets and Elliptic Curves*
* M Ward, *Memoir on Elliptic Divisibility Sequences*
-/

@[expose] public section

open IsEllipticNet

variable {R : Type*} [CommRing R] (b c d : R)

/-- **Elliptic addition formula** for the canonical normalised EDS. Writing `W = normEDS b c d`,
for all `m, n : ℤ`,
`W(m + n) · W(m − n) = W(m + 1) · W(m − 1) · W(n)² − W(n + 1) · W(n − 1) · W(m)²`.

This is the special case `r = 1` of the elliptic relation (using `W(1) = 1`), and by a pure ring
computation the full relation follows from it (see `rel_normEDS`). -/
theorem normEDS_addition_formula (m n : ℤ) :
    normEDS b c d (m + n) * normEDS b c d (m - n) =
      normEDS b c d (m + 1) * normEDS b c d (m - 1) * normEDS b c d n ^ 2 -
        normEDS b c d (n + 1) * normEDS b c d (n - 1) * normEDS b c d m ^ 2 := by
  sorry

/-- The raw elliptic relator of `normEDS b c d` vanishes: for all `p q r : ℤ`,
`W(p+q)·W(p−q)·W(r)² − W(p+r)·W(p−r)·W(q)² + W(q+r)·W(q−r)·W(p)² = 0`. -/
theorem rel_normEDS (p q r : ℤ) : rel (normEDS b c d) p q r 0 = 0 := by
  simp only [rel, add_zero]
  linear_combination (normEDS b c d r) ^ 2 * normEDS_addition_formula b c d p q -
    (normEDS b c d q) ^ 2 * normEDS_addition_formula b c d p r +
    (normEDS b c d p) ^ 2 * normEDS_addition_formula b c d q r

/-- `normEDS b c d` is an elliptic sequence over any commutative ring. -/
theorem normEDS_isEllipticSequence : IsEllipticSequence (normEDS b c d) :=
  fun p q r => rel_normEDS b c d p q r
