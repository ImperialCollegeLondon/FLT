/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram, Samuel Yin
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurveGroupLaw

import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import FLT.Slop.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# The Tate curve `E_q`: surjectivity of the uniformisation

`WeierstrassCurve.exists_tateCurvePoint_eq` — every point of `E_q(k)` is `φ(u)` for some `u ∈ kˣ`
(Silverman, ATAEC V.4). Isolated in its own file for its forthcoming (long) proof, which uses the
group law from `TateCurveGroupLaw`.

Fifth of the files split out of `TateCurveUniformisation`.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄k).Point` notation for the group of `k`-points
open scoped PowerSeries -- `ℤ⟦X⟧` notation for `PowerSeries ℤ`
open scoped Topology -- `𝓝` notation for neighbourhood filters
open ValuativeRel -- `𝒪[k]` notation for the ring of integers of `k`, and `valuation`

-- Can be deleted when mathlib#41391 lands
set_option linter.overlappingInstances false

-- let k be a nonarchimedean local field
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-- **Surjectivity of Tate's uniformisation** (Silverman, ATAEC V.4): every point of
`E_q(k)` is `φ(u)` for some `u ∈ kˣ`.

Intended proof, following Silverman's elementary filtration argument (which uses only
valuation estimates and the discreteness of the valuation — both available here):

* *the formal-group piece*: for `u = 1 + t` with `0 < |t| < 1`, the coordinates have
  Laurent expansions `X(1+t, q) = t⁻²(1 + O(t))`, `Y(1+t, q) = t⁻³(1 + O(t))` with
  integral coefficients; series inversion (`PowerSeries.substInv`, as used for
  `TateCurve.jInvReverse`) shows `t ↦ (X, Y)` maps `{|t| < 1}` *onto* the points with
  `|x| > 1`;
* *the unit piece*: for `|u| = 1` with `u ≢ 1` in the residue field,
  `(X(u), Y(u)) ≡ (ū/(1-ū)², ū²/(1-ū)³) (mod 𝔪)` hits every nonsingular point of the
  reduction `y² + xy = x³` (whose smooth locus is `k̄ˣ`, via `(x, y) ↦ x/y`), and the
  formal-group piece fills in each residue disc;
* *the component piece*: points with `|x| < 1` fall into `ord q - 1` explicit classes
  `Uₙ, Vₙ, W` cut out by the valuations of `y` and `x + y` (Silverman's Lemmas
  4.1.1–4.1.4), which are permuted simply transitively by translation by `φ(π)`-type
  points; a counting argument then shows `φ` hits every class.

Alternatively, the zero-counting route: `f(u) = X(u, q) - x` is a theta-type function
whose Newton polygon has exactly two zeros mod `qᶻ`, one of which has `Y`-value `y`. -/
theorem WeierstrassCurve.exists_tateCurvePoint_eq (q : kˣ)
    (hq : valuation k (q : k) < 1) (P : ((tateCurve (q : k))⁄k).Point) :
    ∃ u : kˣ, tateCurvePoint q hq u = P :=
  sorry
