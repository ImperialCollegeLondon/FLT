/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Bryan Wang Peng Jun
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!

# The division-polynomial ↔ torsion dictionary

Mathlib knows the division polynomials `Ψ`, `ΨSq`, `Φ` of a Weierstrass curve and their
degrees, but not yet their relationship to the torsion points. This file states that
dictionary. It is the missing arithmetic input to two sorried results in
`FLT.KnownIn1980s.EllipticCurves.Flat`:

* `WeierstrassCurve.resultant_Φ_ΨSq` — the resultant identity: its proof needs that a common
  root of `Φₙ` and `ΨSqₙ` over a field is the `x`-coordinate of a nonzero point that is
  simultaneously `n`- and `(n±1)`-torsion, hence trivial (a contradiction unless `Δ = 0`);
* `WeierstrassCurve.torsion_unramified_of_good_reduction` — via the integrality corollary
  below (the `x`-coordinates of `n`-torsion points are roots of a polynomial whose leading
  coefficient `n²` is a unit when `n` is invertible in the base, hence integral).

The two statements below are the classical facts [Silverman, *The Arithmetic of Elliptic
Curves*, Exercise 3.7]; their proofs are inductions on the division-polynomial recurrences
(already in mathlib), and are left as `sorry` here.

-/

@[expose] public section

open scoped Polynomial WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

-- Work over a field `F`; `DecidableEq` is needed for the group law on points.
variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} [W.IsElliptic]

/-- **Torsion criterion.** A nonzero point `P = (x, y)` of `E` is `n`-torsion if and only if
the `n`-th division polynomial square `ΨSqₙ` (a polynomial in `x` alone) vanishes at the
`x`-coordinate of `P`. -/
theorem Point.smul_eq_zero_iff_eval_ΨSq {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0) :
    n • Point.some x y h = 0 ↔ (W.ΨSq n).eval x = 0 :=
  sorry

/-- The `x`-coordinate of a nonzero `n`-torsion point is a root of `ΨSqₙ`. This is the form
consumed by the integrality argument: since `ΨSqₙ` has leading coefficient `n²`
(`WeierstrassCurve.leadingCoeff_ΨSq`), when `n` is invertible in a subring `R ⊆ F` carrying
the coefficients of `W` the polynomial `ΨSqₙ` is monic up to a unit, so its roots — the
`x`-coordinates of the `n`-torsion — are integral over `R`. -/
theorem Point.eval_ΨSq_eq_zero_of_smul_eq_zero {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0) (htors : n • Point.some x y h = 0) :
    (W.ΨSq n).eval x = 0 :=
  (Point.smul_eq_zero_iff_eval_ΨSq h hn).mp htors

/-- **`x`-coordinate under multiplication by `n`.** If `n • P ≠ O` for a nonzero point
`P = (x, y)`, then the `x`-coordinate of `n • P` is `Φₙ(x) / ΨSqₙ(x)`. Stated in the form
"if `n • P = (x', y')` then `x' * ΨSqₙ(x) = Φₙ(x)`", avoiding division. -/
theorem Point.xCoord_smul {x y x' y' : F} (h : W.toAffine.Nonsingular x y)
    (h' : W.toAffine.Nonsingular x' y') {n : ℤ} (hn : n ≠ 0)
    (hP : n • Point.some x y h = Point.some x' y' h') :
    x' * (W.ΨSq n).eval x = (W.Φ n).eval x :=
  sorry

end WeierstrassCurve.Affine
