/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram, Samuel Yin
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurveSeries
public import FLT.KnownIn1980s.EllipticCurves.TateCurveEquation
public import FLT.KnownIn1980s.EllipticCurves.TateCurvePoint
public import FLT.KnownIn1980s.EllipticCurves.TateCurveGroupLaw
public import FLT.KnownIn1980s.EllipticCurves.TateCurveSurjectivity

/-!

# The Tate curve `E_q` and its uniformisation `kˣ/qᶻ → E_q(k)`

Let `k` be a nonarchimedean local field and let `q ∈ kˣ` have `|q| < 1`. This file
constructs the Tate curve `E_q : y² + xy = x³ + a₄(q)x + a₆(q)`
(`WeierstrassCurve.tateCurve`) and the map

`tateCurvePoint : kˣ → E_q(k)`, `u ↦ (X(u, q), Y(u, q))` for `u ∉ qᶻ`, `qᶻ ↦ O`,

given by Silverman's explicit series (ATAEC V.3), together with everything needed to make
it a well-defined map on `kˣ/qᶻ` landing on the curve:

* the nonarchimedean summation calculus for the defining series (the geometric family
  `hasSum_geometric_deriv`, `hasSum_geometric_div_cube`, `hasSum_geometric_sq_div_cube`,
  and the divisor-regrouping engines `hasSum_sum_divisors_mul_pow`, `hasSum_geom_rows`);
* the discriminant computation `Δ(q) = q∏(1-qⁿ)²⁴` (`tateΔ_eq_prod`, via Jacobi's formal
  identity `TateCurve.ΔFormal_eq`), giving `Δ(q) ≠ 0` and nonsingularity of every point;
* Silverman's `q`-expansions of `X` and `Y` on the fundamental annulus `|q| < |u| ≤ 1`
  (`tateX_eq_annulus`, `tateY_eq_annulus`) and the evaluation calculus
  `TateCurve.evalK`/`TateCurve.EvalBounded` on `k`-coefficient power series, through
  which the formal Weierstrass identity `TateCurve.weierstrass_equation_field`
  (descended from `ℂ` in `TateCurveConstruction`/`TateCurveDescent`) evaluates to the
  statement that `(X(u, q), Y(u, q))` lies on `E_q` (`tateCurve_equation`);
* the `qᶻ`-invariance of the coordinates (`tateX_zpow_mul_left`, `tateY_zpow_mul_left`)
  and the fundamental domain `exists_zpow_mul_mem_annulus`;
* Stage 1 of the group-law compatibility: parameter inversion is negation on the curve
  (`tateX_inv`, `tateY_inv`, `tateCurvePoint_inv`).

Following Silverman's proof of ATAEC V.3.1(c), the remaining content of Tate's theorem
`WeierstrassCurve.tateCurveEquiv` (in `FLT.KnownIn1980s.EllipticCurves.TateCurve`, which
imports this file) is reduced to **three pillars** about `tateCurvePoint`, stated at the
end of this file:

* **additivity** `tateCurvePoint_mul` : `φ(uv) = φ(u) + φ(v)`, which by the
  auxiliary-element trick `map_mul_of_generic` (Silverman's Lemma 3.1.2) reduces to the
  chord-law identities `tateX_mul_of_ne`, `tateY_mul_of_ne` for pairs in general
  position — currently `sorry`, awaiting the two-variable analogue of the descent in
  `TateCurveDescent` (the analytic input over `ℂ` is the addition theorem for `℘`);
* **injectivity**, which is *free* given additivity: the kernel of `tateCurvePoint` is
  `qᶻ` by construction (`tateCurvePoint_eq_zero_iff` — affine points are never `O`), so
  `φ(u) = φ(v)` forces `φ(u⁻¹v) = O`, i.e. `u⁻¹v ∈ qᶻ` (`tateCurvePoint_eq_iff`). (This
  is Silverman's argument; no theta-function machinery is needed.)
* **surjectivity** `exists_tateCurvePoint_eq` — currently `sorry`; the intended proof is
  Silverman's elementary filtration argument (ATAEC V.4), see the docstring there.

## File organisation

This file is a re-export; the development is split across
`TateCurveSeries` (defs, coordinate series, convergence, discriminant),
`TateCurveEquation` (annulus expansions, `evalK` calculus, the Weierstrass equation),
`TateCurvePoint` (the point map `tateCurvePoint` and its structure),
`TateCurveGroupLaw` (chord law, additivity, injectivity), and
`TateCurveSurjectivity` (`exists_tateCurvePoint_eq`).
-/
