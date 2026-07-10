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

The statements below are the classical facts [Silverman, *The Arithmetic of Elliptic
Curves*, Exercise 3.7]. Everything is reduced to a single geometric induction, isolated as the
positive-case helper `WeierstrassCurve.Affine.Point.smul_dichotomy_pos` (for `0 < n`, with the
`n = 1` and `n = 2` (doubling) base cases discharged and the `n ≥ 3` step left as `sorry`); the
negative-`n` reduction,
the master dichotomy, and both user-facing corollaries are proved unconditionally from it.

-/

@[expose] public section

open scoped Polynomial WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine

-- Work over a field `F`; `DecidableEq` is needed for the group law on points.
variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} [W.IsElliptic]

private lemma bridge_ΨSq {x y : F} (hxy : W.toAffine.polynomial.evalEval x y = 0) (n : ℤ) :
    (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have key := congrArg (AdjoinRoot.evalEval hxy)
    ((congrArg (· ^ 2) (CoordinateRing.mk_ψ n)).trans (CoordinateRing.mk_Ψ_sq n))
  simpa only [map_pow, AdjoinRoot.evalEval_mk, Polynomial.evalEval_C] using key

private lemma bridge_Φ {x y : F} (hxy : W.toAffine.polynomial.evalEval x y = 0) (n : ℤ) :
    (W.φ n).evalEval x y = (W.Φ n).eval x := by
  have key := congrArg (AdjoinRoot.evalEval hxy) (CoordinateRing.mk_φ n)
  simpa only [AdjoinRoot.evalEval_mk, Polynomial.evalEval_C] using key

/-- **Positive case of the division-polynomial dictionary.** This is the geometric heart of the
file: the same dichotomy as `Point.smul_dichotomy`, but only for `0 < n`. The full statement is
recovered from this by the negation reduction in `Point.smul_dichotomy` (the `x`-coordinate is
negation-invariant and `ΨSq`, `Φ` are even in `n`), so this helper is strictly smaller in content.

It is the classical multiplication-by-`n` formula [Silverman, *The Arithmetic of Elliptic Curves*,
Exercise 3.7]: proved by strong induction on `n`, using the elliptic-divisibility-sequence
recurrences `preΨ_even`/`preΨ_odd`/`ΨSq_even`/`ΨSq_odd` together with the affine group-law addition
formulas `WeierstrassCurve.Affine.addX`/`slope` (via `Point.add_some`). The base case `n = 1`
(`ΨSq₁ = 1`, `Φ₁ = X`, so `x(1 • P) = x`) and the doubling case `n = 2` are proved below: for
`n = 2` one computes `2 • P = P + P` directly from the affine group law, using that on the curve
`ΨSq₂` evaluates to `ψ₂(x, y)² = (2y + a₁x + a₃)²` and matching the doubling `x`-coordinate
`addX x x ℓ` against `Φ₂` by clearing the slope's denominator (`linear_combination` in the
Weierstrass equation). The inductive step for `n ≥ 3` expresses `x((m+1) • P)` through the addition
formula for `(m • P) + P` and matches it against `Φ_{m+1}/ΨSq_{m+1}` using the EDS relation
`Ψ_{m+1} Ψ_{m-1} = Ψ_m² · (…)`.

TODO: prove the `n ≥ 3` inductive step (the `n = 1, 2` base cases are done). It requires an
evaluation bridge from the bivariate `ψ`/`φ` at a point to the univariate `ΨSq`/`Φ` (mathlib's
`mk_Ψ_sq`/`mk_φ` coordinate-ring congruences, specialised at a point where the Weierstrass
polynomial vanishes) and the group-law addition formulas. -/
private theorem Point.smul_dichotomy_pos {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ}
    (hn : 0 < n) :
    (n • Point.some x y h = 0 ∧ (W.ΨSq n).eval x = 0) ∨
      (n • Point.some x y h ≠ 0 ∧ (W.ΨSq n).eval x ≠ 0 ∧
        ∀ (x' y' : F) (h' : W.toAffine.Nonsingular x' y'),
          n • Point.some x y h = Point.some x' y' h' →
            x' * (W.ΨSq n).eval x = (W.Φ n).eval x) := by
  by_cases hn1 : n = 1
  · -- Base case `n = 1`: here `1 • P = P ≠ O`, `ΨSq₁ = 1`, `Φ₁ = X`, so `x' = x = Φ₁(x)/ΨSq₁(x)`.
    subst hn1
    refine Or.inr ⟨by rw [one_smul]; exact Point.some_ne_zero h, by rw [ΨSq_one]; simp, ?_⟩
    intro x' y' h' hP
    rw [one_smul] at hP
    rw [ΨSq_one, Φ_one]
    simp only [Polynomial.eval_one, Polynomial.eval_X, mul_one]
    injection hP with hx hy
    exact hx.symm
  · by_cases hn2 : n = 2
    · -- **Base case `n = 2` (the doubling formula).** Here `2 • P = P + P`, computed directly from
      -- the affine group law: `2 • P = O` exactly when `P` is `2`-torsion, i.e. `y = negY x y`,
      -- which is exactly when `ΨSq₂(x) = ψ₂(x, y)² = (2y + a₁x + a₃)²` vanishes; otherwise the
      -- doubling `x`-coordinate `addX x x ℓ` satisfies the Silverman relation against `Φ₂`.
      subst hn2
      have heq : y ^ 2 + W.a₁ * x * y + W.a₃ * y = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ :=
        (W.toAffine.equation_iff x y).mp h.1
      -- On the curve, `ΨSq₂` evaluates to `ψ₂(x, y)² = (2y + a₁x + a₃)²`.
      have hΨ2 : (W.ΨSq 2).eval x = (2 * y + W.a₁ * x + W.a₃) ^ 2 := by
        rw [ΨSq_two, Ψ₂Sq, b₂, b₄, b₆]
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_C, Polynomial.eval_X]
        linear_combination (-4 : F) * heq
      have hdouble : (2 : ℤ) • Point.some x y h = Point.some x y h + Point.some x y h :=
        two_zsmul _
      by_cases hy : y = W.toAffine.negY x y
      · -- Two-torsion: `2 • P = O` and `ΨSq₂(x) = 0`.
        refine Or.inl ⟨by rw [hdouble]; exact add_self_of_Y_eq hy, ?_⟩
        have hy' : y = -y - W.a₁ * x - W.a₃ := hy
        have hd : 2 * y + W.a₁ * x + W.a₃ = 0 := by linear_combination hy'
        rw [hΨ2, hd]; ring
      · -- Non-torsion: `2 • P ≠ O`, `ΨSq₂(x) ≠ 0`, and the doubling `x`-coordinate formula holds.
        have hd : (2 * y + W.a₁ * x + W.a₃) ≠ 0 := fun hcon =>
          hy (by change y = -y - W.a₁ * x - W.a₃; linear_combination hcon)
        have hne : (2 : ℤ) • Point.some x y h ≠ 0 := by
          rw [hdouble, add_self_of_Y_ne hy]; exact some_ne_zero _
        refine Or.inr ⟨hne, by rw [hΨ2]; exact pow_ne_zero 2 hd, ?_⟩
        intro x' y' h' hP
        rw [hdouble, add_self_of_Y_ne hy, Point.some.injEq] at hP
        -- The defining relation of the doubling slope `ℓ`, cleared of its denominator.
        set ℓ := W.toAffine.slope x x y y with hℓ
        have hden : y - W.toAffine.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
          change y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃; ring
        have hℓd : ℓ * (2 * y + W.a₁ * x + W.a₃) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
          rw [hℓ, W.toAffine.slope_of_Y_ne rfl hy, hden]
          exact div_mul_cancel₀ _ hd
        rw [hΨ2, ← hP.1]
        simp only [Affine.addX, Φ_two, Polynomial.eval_sub, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
        rw [b₄, b₆, b₈]
        linear_combination
          (ℓ * (2 * y + W.a₁ * x + W.a₃) + (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) +
              W.a₁ * (2 * y + W.a₁ * x + W.a₃)) * hℓd +
            (-(W.a₁ ^ 2 + 4 * W.a₂) - 8 * x) * heq
    · -- Inductive step `n ≥ 3`: the elliptic-divisibility-sequence induction described above.
      -- This is the remaining geometric content.
      sorry

/-- **Division-polynomial dictionary (master induction).** For a nonzero point `P = (x, y)` and
`n ≠ 0`, exactly one of the following holds:

* `n • P = O` and `ΨSqₙ` vanishes at `x` (the torsion / degenerate case), or
* `n • P ≠ O`, `ΨSqₙ(x) ≠ 0`, and the `x`-coordinate `x'` of `n • P` satisfies the
  Silverman relation `x' · ΨSqₙ(x) = Φₙ(x)`.

This is the geometric content of [Silverman, *The Arithmetic of Elliptic Curves*, Exercise 3.7]:
one proves by strong induction on `n` (via the elliptic-divisibility-sequence recurrences for
`preΨ`/`ΨSq`/`Φ` in `Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic`, combined
with the affine group-law addition formulas `WeierstrassCurve.Affine.addX`/`slope`) that the
multiplication-by-`n` map has `x`-coordinate `Φₙ(x) / ΨSqₙ(x)`, degenerating to `O` exactly when
`ΨSqₙ(x) = 0`. The two user-facing theorems below are immediate corollaries.

The geometric difficulty is concentrated in the positive case `Point.smul_dichotomy_pos`; the
negative case is a routine reduction, so both frozen statements are proved unconditionally from
the positive case. -/
theorem Point.smul_dichotomy {x y : F} (h : W.toAffine.Nonsingular x y) {n : ℤ} (hn : n ≠ 0) :
    (n • Point.some x y h = 0 ∧ (W.ΨSq n).eval x = 0) ∨
      (n • Point.some x y h ≠ 0 ∧ (W.ΨSq n).eval x ≠ 0 ∧
        ∀ (x' y' : F) (h' : W.toAffine.Nonsingular x' y'),
          n • Point.some x y h = Point.some x' y' h' →
            x' * (W.ΨSq n).eval x = (W.Φ n).eval x) := by
  -- Reduce to the positive case `smul_dichotomy_pos`. The negative case follows because the
  -- `x`-coordinate is invariant under negation (`Point.neg_some`) and the polynomials `ΨSq`, `Φ`
  -- are even in `n` (`ΨSq_neg`, `Φ_neg`); `n • P = -((-n) • P)` by `neg_smul`.
  rcases lt_or_gt_of_ne hn with hneg | hpos
  · have hpos : (0 : ℤ) < -n := by omega
    -- `n • P = -((-n) • P)`, and `(-n) • P` is governed by `smul_dichotomy_pos`.
    have e1 : n • Point.some x y h = -((-n) • Point.some x y h) := by rw [neg_smul, neg_neg]
    have eΨ : W.ΨSq (-n) = W.ΨSq n := ΨSq_neg W n
    have eΦ : W.Φ (-n) = W.Φ n := Φ_neg W n
    rcases Point.smul_dichotomy_pos h hpos with ⟨hz, he⟩ | ⟨hne, hΨne, hx⟩
    · refine Or.inl ⟨by rw [e1, hz, neg_zero], ?_⟩
      rw [← eΨ]; exact he
    · refine Or.inr ⟨by rw [e1]; exact neg_ne_zero.mpr hne, by rw [← eΨ]; exact hΨne, ?_⟩
      intro x' y' h' hP
      -- From `n • P = some x' y' h'` deduce `(-n) • P = -(some x' y' h') = some x' (negY ..) _`.
      have hneg2 : (-n) • Point.some x y h = -(Point.some x' y' h') :=
        neg_eq_iff_eq_neg.mp (e1.symm.trans hP)
      rw [Point.neg_some] at hneg2
      have := hx _ _ _ hneg2
      rwa [eΨ, eΦ] at this
  · exact Point.smul_dichotomy_pos h hpos

/-- **Torsion criterion.** A nonzero point `P = (x, y)` of `E` is `n`-torsion if and only if
the `n`-th division polynomial square `ΨSqₙ` (a polynomial in `x` alone) vanishes at the
`x`-coordinate of `P`. -/
theorem Point.smul_eq_zero_iff_eval_ΨSq {x y : F} (h : W.toAffine.Nonsingular x y)
    {n : ℤ} (hn : n ≠ 0) :
    n • Point.some x y h = 0 ↔ (W.ΨSq n).eval x = 0 := by
  rcases Point.smul_dichotomy h hn with ⟨hzero, heval⟩ | ⟨hne, heval, _⟩
  · exact ⟨fun _ => heval, fun _ => hzero⟩
  · exact ⟨fun hz => absurd hz hne, fun hz => absurd hz heval⟩

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
    x' * (W.ΨSq n).eval x = (W.Φ n).eval x := by
  rcases Point.smul_dichotomy h hn with ⟨hzero, _⟩ | ⟨_, _, hx⟩
  · exact absurd (hP.symm.trans hzero) (Point.some_ne_zero h')
  · exact hx x' y' h' hP

end WeierstrassCurve.Affine
