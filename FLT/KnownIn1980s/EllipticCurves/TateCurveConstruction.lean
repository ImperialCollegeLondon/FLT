/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Mathlib.NumberTheory.LSeries.RiemannZeta

import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finsupp.Encodable
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.NumberTheory.ZetaValues

/-!

# The power series identity underlying the construction of the Tate curve

If `k` is a nonarchimedean local field and `q ∈ kˣ` has `|q| < 1`, then Tate showed
that `kˣ/qᶻ` is the group of `k`-points of an elliptic curve `E_q/k` with Weierstrass
equation `y² + xy = x³ + a₄(q)x + a₆(q)`, for certain explicit power series `a₄` and
`a₆` in `q` with integer coefficients; the map `kˣ → E_q(k)` is given by explicit
power series `X(u,q)` and `Y(u,q)` in `q` whose coefficients are Laurent polynomials
in `u`.

The purely algebraic input to this construction is the identity
`Y² + XY = X³ + a₄X + a₆` in `ℚ(u)⟦q⟧`, which this file states and proves
(`TateCurve.weierstrass_equation`). The identity is extracted from Theorem V.1.1 of
[Silverman, *Advanced topics in the arithmetic of elliptic curves*], where it is
deduced from the complex-analytic theory of the Weierstrass `℘`-function, using also
its supporting results Theorem I.6.2 (the `q`-expansions of `℘` and `℘'`) and
Theorem I.7.1 (the `q`-expansions of `g₂` and `g₃`); see also the remark "In other
words, we want to verify that this identity holds in the ring `ℚ(u)[[q]]`" in
Silverman's proof of Theorem V.3.1(c).

Silverman's argument is complex-analytic, so an extra step (which Silverman leaves
implicit) is needed to descend from an identity of convergent series of complex numbers
to the identity of *formal* power series over `ℚ(u)`: the coefficients of both sides are
rational functions of `u`, and the analytic identity shows that they agree at infinitely
many complex values of `u`, hence they agree in `ℚ(u)`.

## Strategy of the proof

Fix `τ` in the upper half plane and `z ∈ ℂ`, and set `q = e(τ)`, `u = e(z)`, where
`e(w) = exp(2πiw)`; let `Λ_τ = ℤτ + ℤ` (the `PeriodPair.lattice` of the pair `(τ, 1)`).

1. *`q`-expansions* (Silverman I.6.2, I.7.1). Prove
   * `℘(z; Λ_τ) = (2πi)²(1/12 + Xₐ(u, q))` (`weierstrassP_q_expansion`),
   * `℘'(z; Λ_τ) = (2πi)³(Xₐ(u, q) + 2Yₐ(u, q))` (`derivWeierstrassP_q_expansion`),
   * `g₂(Λ_τ) = (2πi)⁴(1 + 240s₃(q))/12` (`g₂_q_expansion`),
   * `g₃(Λ_τ) = -(2πi)⁶(1 - 504s₅(q))/216` (`g₃_q_expansion`),

   where `Xₐ`, `Yₐ`, `sₖ` are the analytic functions defined below (sums over `n : ℤ`,
   resp. the convergent version of `TateCurve.s`). The main tool is the "row sum"
   identity `∑_{m : ℤ} (w + m)⁻ᵏ = ((-2πi)ᵏ/(k-1)!) ∑_{d ≥ 1} dᵏ⁻¹ e(w)ᵈ`, obtained by
   differentiating the classical partial-fraction expansion of the cotangent; this is
   `EisensteinSeries.qExpansion_identity` in Mathlib (see also `cot_series_rep` and
   `pi_mul_cot_pi_q_exp`).
2. *The analytic Weierstrass equation* (Silverman V.1.1(a)). Substitute the expansions
   of step 1 into the differential equation `℘'² = 4℘³ - g₂℘ - g₃` (Mathlib's
   `PeriodPair.derivWeierstrassP_sq`) and simplify; after dividing by `(2πi)⁶` and by
   `4`, everything cancels to give `analytic_weierstrass`:

   `Yₐ² + XₐYₐ = Xₐ³ - 5s₃Xₐ - (5s₃ + 7s₅)/12`.
3. *Rearrangement*. For `0 < ‖q‖ < ‖u‖ < 1`, expand each term of the sums over `n : ℤ`
   defining `Xₐ`, `Yₐ` as a geometric-type series (`v/(1-v)² = ∑ m vᵐ`,
   `v²/(1-v)³ = ∑ (m choose 2) vᵐ` for `‖v‖ < 1`), and rearrange the resulting
   absolutely convergent double series by powers of `q`. The coefficients that appear
   are exactly the coefficients of the formal series `X` and `Y` evaluated at `u`
   (`hasSum_X_eval`, `hasSum_Y_eval`; for transcendental `u`, so that evaluation of
   coefficients at `u` is a ring homomorphism).
4. *Descent*. If `F ∈ ℚ(u)⟦q⟧` is such that, for infinitely many `u₀ ∈ ℂ`, the series
   `∑ₙ Fₙ(u₀)q₀ⁿ` converges with sum `0` for all sufficiently small nonzero `q₀`, then
   `F = 0` (`eq_zero_of_forall_hasSum_zero`): indeed each `Fₙ(u₀)` vanishes by
   uniqueness of coefficients of convergent power series, and a rational function with
   infinitely many zeros is zero. Applying this to
   `F = Y² + XY - X³ - a₄X - a₆` with `u₀` ranging over the (uncountably many, hence
   infinitely many) transcendental points of the punctured unit disc, steps 2 and 3
   provide the vanishing hypothesis, and `TateCurve.weierstrass_equation` follows.

The supporting material lives in the namespace `TateCurve.Blueprint`.

## Implementation notes

We work in `(RatFunc ℚ)⟦X⟧`, formal power series over the field `ℚ(u)` of rational
functions. Beware of the clash of notation: the power series variable (written `q`
above and in the references) is `PowerSeries.X`, whereas the rational function
variable `u` is `RatFunc.X`, and neither has anything to do with the coordinate `X`
on the curve, which is the power series `TateCurve.X` defined below.

There is also the possibility of a purely algebraic proof of the identity, avoiding
complex analysis entirely; see
https://mathoverflow.net/questions/469021/low-level-proof-of-identity-related-to-weierstrass-p-function
This file does not take that route.

-/

@[expose] public section

open scoped PowerSeries -- `R⟦X⟧` notation for `PowerSeries R`

open scoped ArithmeticFunction.sigma -- `σ k n` notation for the sum of the `k`th
                                     -- powers of the positive divisors of `n`

open scoped PeriodPair -- `℘[L]` and `℘'[L]` notation for the Weierstrass `℘`-function
                       -- of the lattice attached to a pair of periods, and its derivative

open Complex

open scoped Topology -- `𝓝` and `𝓝[≠]` notation for (punctured) neighbourhood filters

noncomputable section

namespace TateCurve

section


/-- The variable `u` of the field `ℚ(u)` of coefficients. -/
local notation "u" => (RatFunc.X : RatFunc ℚ)

/-- The power series `sₖ = ∑_{n ≥ 1} σₖ(n)qⁿ ∈ ℚ(u)⟦q⟧` (where `σₖ(n)` is the sum of
the `k`th powers of the positive divisors of `n`). Up to a normalising constant, these
are the `q`-expansions of the Eisenstein series of weight `k + 1`. -/
def s (k : ℕ) : (RatFunc ℚ)⟦X⟧ :=
  .mk fun n ↦ (σ k n : RatFunc ℚ)

/-- The coefficient `a₄ = -5s₃ = -5q - 45q² - ⋯` of the Tate curve
`y² + xy = x³ + a₄x + a₆`. -/
def a₄ : (RatFunc ℚ)⟦X⟧ := -5 * s 3

/-- The coefficient `a₆ = -(5s₃ + 7s₅)/12 = -q - 23q² - ⋯` of the Tate curve
`y² + xy = x³ + a₄x + a₆`. (Division by `12` is implemented as scalar multiplication
by `12⁻¹ ∈ ℚ(u)`; note that `5σ₃(n) + 7σ₅(n)` is always divisible by `12`, so `a₆`
in fact has integer coefficients, though we do not need this.) -/
def a₆ : (RatFunc ℚ)⟦X⟧ := (12 : RatFunc ℚ)⁻¹ • -(5 * s 3 + 7 * s 5)

/-- The power series
`X(u,q) = u/(1-u)² + ∑_{n ≥ 1} (∑_{d ∣ n} d(uᵈ + u⁻ᵈ - 2)) qⁿ ∈ ℚ(u)⟦q⟧`,
the `x`-coordinate of the uniformisation `kˣ/qᶻ ≃ E_q(k)` of the Tate curve. -/
def X : (RatFunc ℚ)⟦X⟧ :=
  .C (u / (1 - u) ^ 2) +
    .mk fun n ↦ ∑ d ∈ n.divisors, d * (u ^ d + u⁻¹ ^ d - 2)

/-- The power series
`Y(u,q) = u²/(1-u)³ + ∑_{n ≥ 1} (∑_{d ∣ n} ((d choose 2)uᵈ - (d+1 choose 2)u⁻ᵈ + d)) qⁿ`
in `ℚ(u)⟦q⟧`, the `y`-coordinate of the uniformisation `kˣ/qᶻ ≃ E_q(k)` of the
Tate curve. -/
def Y : (RatFunc ℚ)⟦X⟧ :=
  .C (u ^ 2 / (1 - u) ^ 3) +
    .mk fun n ↦ ∑ d ∈ n.divisors,
      (d.choose 2 * u ^ d - (d + 1).choose 2 * u⁻¹ ^ d + d)

end

namespace Blueprint

/-! ## The analytic actors -/

/-- `e z = exp (2πiz)`. We will take `u = e z` and `q = e τ`. -/
def e (z : ℂ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * I * z)

lemma e_ne_zero (w : ℂ) : e w ≠ 0 := Complex.exp_ne_zero _

lemma e_add (z w : ℂ) : e (z + w) = e z * e w := by
  rw [e, e, e, ← Complex.exp_add]
  congr 1
  ring

lemma e_neg (w : ℂ) : e (-w) = (e w)⁻¹ := by
  rw [e, e, ← Complex.exp_neg]
  congr 1
  ring

lemma e_intMul (n : ℤ) (w : ℂ) : e (n * w) = e w ^ n := by
  rw [e, e, ← Complex.exp_int_mul]
  congr 1
  ring

lemma norm_e (w : ℂ) : ‖e w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
  rw [e, Complex.norm_exp]
  congr 1
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
  ring

lemma norm_e_lt_one {w : ℂ} (hw : 0 < w.im) : ‖e w‖ < 1 := by
  rw [norm_e, Real.exp_lt_one_iff]
  nlinarith [Real.pi_pos]

lemma norm_e_lt_norm_e {z w : ℂ} (h : w.im < z.im) : ‖e z‖ < ‖e w‖ := by
  rw [norm_e, norm_e, Real.exp_lt_exp]
  nlinarith [Real.pi_pos]

lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
  norm_num [Complex.ext_iff, Real.pi_ne_zero]

/-- The pair of periods `(τ, 1)`, for `τ` not real. Its `PeriodPair.lattice` is
`Λ_τ = ℤτ + ℤ`. -/
def periodPair (τ : ℂ) (hτ : τ.im ≠ 0) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    refine linearIndependent_fin2.mpr ⟨by simp, fun a h ↦ hτ ?_⟩
    have h' : (a : ℂ) = τ := by simpa [Complex.real_smul] using h
    rw [← h', Complex.ofReal_im]

@[simp] lemma periodPair_ω₁ (τ : ℂ) (hτ : τ.im ≠ 0) : (periodPair τ hτ).ω₁ = τ := rfl

@[simp] lemma periodPair_ω₂ (τ : ℂ) (hτ : τ.im ≠ 0) : (periodPair τ hτ).ω₂ = 1 := rfl

/-- The convergent power series `sₖ(q) = ∑_{n ≥ 1} σₖ(n)qⁿ`, for `‖q‖ < 1` (junk value
otherwise); the evaluation of the formal series `TateCurve.s k` at `q`. Convergence
follows from the crude estimate `σₖ(n) ≤ n^(k+1)`. -/
def sAn (k : ℕ) (q : ℂ) : ℂ := ∑' n : ℕ, (σ k n : ℂ) * q ^ n

/-- The analytic function `Xₐ(u, q) = ∑_{n : ℤ} qⁿu/(1 - qⁿu)² - 2s₁(q)`, defined for
`0 < ‖q‖ < 1` and `u ∉ qᶻ` (junk value otherwise). This is the function called `X(u, q)`
in [Silverman, *Advanced topics*, Theorem V.1.1]. The sum converges absolutely: the
terms for `n → ∞` are `O(‖q‖ⁿ)`, and likewise for `n → -∞` after rewriting
`v/(1-v)² = v⁻¹/(1-v⁻¹)²` with `v = qⁿu`. -/
def XAn (u q : ℂ) : ℂ := (∑' n : ℤ, q ^ n * u / (1 - q ^ n * u) ^ 2) - 2 * sAn 1 q

/-- The analytic function `Yₐ(u, q) = ∑_{n : ℤ} (qⁿu)²/(1 - qⁿu)³ + s₁(q)`, defined for
`0 < ‖q‖ < 1` and `u ∉ qᶻ` (junk value otherwise). This is the function called `Y(u, q)`
in [Silverman, *Advanced topics*, Theorem V.1.1]. -/
def YAn (u q : ℂ) : ℂ := (∑' n : ℤ, (q ^ n * u) ^ 2 / (1 - q ^ n * u) ^ 3) + sAn 1 q

/-! ## `q`-expansions

The basic tool is the "row sum" identity, obtained from the partial-fraction expansion
of the cotangent (`cot_series_rep`, `pi_mul_cot_pi_q_exp` in Mathlib) by repeated
differentiation; for exponents `k ≥ 2` and `w` in the upper half plane this is
`EisensteinSeries.qExpansion_identity` in Mathlib. We state the two special cases we
need, with the Lambert-type sums on the right-hand side in closed form
(`∑_{d ≥ 1} d vᵈ = v/(1-v)²` and `∑_{d ≥ 1} d² vᵈ = v(1+v)/(1-v)³` for `‖v‖ < 1`,
by differentiating the geometric series). -/

/-- The Lambert-type sum `∑_{n ≥ 0} (n choose 2)rⁿ = r²/(1 - r)³` for `‖r‖ < 1`, by
shifting the index in `∑' n, ((n + 2).choose 2) * rⁿ = 1/(1 - r)³`. -/
private lemma hasSum_choose_two_mul_geometric {r : ℂ} (hr : ‖r‖ < 1) :
    HasSum (fun n : ℕ ↦ ((n.choose 2 : ℕ) : ℂ) * r ^ n) (r ^ 2 * ((1 - r) ^ 3)⁻¹) := by
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hr).mul_left (r ^ 2)
  have heq : (fun n : ℕ ↦ r ^ 2 * ((((n + 2).choose 2 : ℕ) : ℂ) * r ^ n)) =
      fun n : ℕ ↦ ((((n + 2).choose 2 : ℕ) : ℂ) * r ^ (n + 2)) := by
    funext n
    ring
  rw [heq] at h
  have h' := (hasSum_nat_add_iff (f := fun n : ℕ ↦ ((n.choose 2 : ℕ) : ℂ) * r ^ n) 2).mp h
  simpa [Finset.sum_range_succ] using h'

/-- The Lambert-type sum `∑_{n ≥ 0} n²rⁿ = r(1 + r)/(1 - r)³` for `‖r‖ < 1`, from the
`n(n-1)/2`- and `n`-sums (`hasSum_choose_two_mul_geometric`,
`hasSum_coe_mul_geometric_of_norm_lt_one`). -/
private lemma tsum_sq_mul_geometric_of_norm_lt_one {r : ℂ} (hr : ‖r‖ < 1) :
    ∑' n : ℕ, (n : ℂ) ^ 2 * r ^ n = r * (1 + r) / (1 - r) ^ 3 := by
  have hr1 : (1 : ℂ) - r ≠ 0 := by
    intro hr1
    rw [sub_eq_zero] at hr1
    simp [← hr1] at hr
  have h2 : HasSum (fun n : ℕ ↦ ((n.choose 2 : ℕ) : ℂ) * r ^ n) (r ^ 2 * ((1 - r) ^ 3)⁻¹) :=
    hasSum_choose_two_mul_geometric hr
  have h1 : HasSum (fun n : ℕ ↦ (n : ℂ) * r ^ n) (r / (1 - r) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hr
  -- combine via `n² = 2(n choose 2) + n`
  have h3 := (h2.mul_left 2).add h1
  have heq : (fun n : ℕ ↦ 2 * (((n.choose 2 : ℕ) : ℂ) * r ^ n) + (n : ℂ) * r ^ n) =
      fun n : ℕ ↦ (n : ℂ) ^ 2 * r ^ n := by
    funext n
    rw [Nat.cast_choose_two]
    ring
  rw [heq] at h3
  rw [h3.tsum_eq]
  field_simp
  ring

/-- Row sum, exponent `2`: for `w` in the upper half plane,
`∑_{m : ℤ} (w + m)⁻² = (2πi)² e(w)/(1 - e(w))²`.
This is the case `k = 1` of `EisensteinSeries.qExpansion_identity` together with the
closed form of the Lambert sum. -/
theorem sum_int_inv_sq (w : ℂ) (hw : 0 < w.im) :
    ∑' m : ℤ, ((w + m) ^ 2)⁻¹ = (2 * (Real.pi : ℂ) * I) ^ 2 * (e w / (1 - e w) ^ 2) := by
  have hq : ‖Complex.exp (2 * (Real.pi : ℂ) * I * w)‖ < 1 := by
    simpa [UpperHalfPlane.coe_mk] using UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨w, hw⟩
  have h := EisensteinSeries.qExpansion_identity (k := 1) le_rfl (⟨w, hw⟩ : UpperHalfPlane)
  simp only [one_div, pow_one, Nat.factorial_one, Nat.cast_one, div_one, Nat.reduceAdd] at h
  simp only [e]
  rw [h, tsum_coe_mul_geometric_of_norm_lt_one hq]
  ring

/-- Row sum, exponent `3`: for `w` in the upper half plane,
`∑_{m : ℤ} (w + m)⁻³ = -(2πi)³/2 ⬝ e(w)(1 + e(w))/(1 - e(w))³`
(note the sign: the exponent is odd, and the general formula has `(-2πi)ᵏ/(k-1)!`).
This is the case `k = 2` of `EisensteinSeries.qExpansion_identity` together with the
closed form of the Lambert sum. -/
theorem sum_int_inv_cube (w : ℂ) (hw : 0 < w.im) :
    ∑' m : ℤ, ((w + m) ^ 3)⁻¹ =
      -(2 * (Real.pi : ℂ) * I) ^ 3 / 2 * (e w * (1 + e w) / (1 - e w) ^ 3) := by
  have hq : ‖Complex.exp (2 * (Real.pi : ℂ) * I * w)‖ < 1 := by
    simpa [UpperHalfPlane.coe_mk] using UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨w, hw⟩
  have h := EisensteinSeries.qExpansion_identity (k := 2) one_le_two (⟨w, hw⟩ : UpperHalfPlane)
  simp only [one_div, Nat.factorial_two, Nat.cast_ofNat, Nat.reduceAdd] at h
  simp only [e]
  rw [h, tsum_sq_mul_geometric_of_norm_lt_one hq]
  ring

/-- The rational-function identity `v⁻¹/(1 - v⁻¹)² = v/(1 - v)²` (true for `v ≠ 0`,
including `v = 1` where both sides are junk `0`). -/
private lemma inv_div_one_sub_inv_sq {v : ℂ} (hv : v ≠ 0) :
    v⁻¹ / (1 - v⁻¹) ^ 2 = v / (1 - v) ^ 2 := by
  rcases eq_or_ne v 1 with rfl | hv1
  · norm_num
  · have h1 : 1 - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
    have h2 : 1 - v⁻¹ ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h ↦ hv1 (inv_eq_one.mp h.symm)
    field_simp
    ring

/-- Norm bound for `v/(1 - v)²` when `‖v‖ ≤ a < 1`. -/
private lemma norm_div_one_sub_sq_le {v : ℂ} {a : ℝ} (hva : ‖v‖ ≤ a) (ha : a < 1) :
    ‖v / (1 - v) ^ 2‖ ≤ ‖v‖ / (1 - a) ^ 2 := by
  have h0 : (0 : ℝ) < 1 - a := by linarith
  have h1 : 1 - a ≤ ‖1 - v‖ := by
    have h2 := norm_sub_norm_le (1 : ℂ) v
    rw [norm_one] at h2
    linarith
  have h2 : (1 - a) ^ 2 ≤ ‖1 - v‖ ^ 2 := pow_le_pow_left₀ h0.le h1 2
  have h3 : (0 : ℝ) < ‖1 - v‖ ^ 2 := lt_of_lt_of_le (pow_pos h0 2) h2
  rw [norm_div, norm_pow, div_le_div_iff₀ h3 (pow_pos h0 2)]
  exact mul_le_mul_of_nonneg_left h2 (norm_nonneg v)

/-- If `‖x‖ < 1` and `‖xy‖ < 1` then `∑_{n ≥ 1} xⁿy/(1 - xⁿy)²` converges (the terms
decay geometrically). -/
private lemma summable_aux {x y : ℂ} (hx : ‖x‖ < 1) (hxy : ‖x * y‖ < 1) :
    Summable fun n : ℕ ↦ x ^ (n + 1) * y / (1 - x ^ (n + 1) * y) ^ 2 := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left (‖x * y‖ / (1 - ‖x * y‖) ^ 2))
  intro n
  have hveq : ‖x ^ (n + 1) * y‖ = ‖x‖ ^ n * ‖x * y‖ := by
    rw [pow_succ, mul_assoc, norm_mul, norm_pow]
  have hva : ‖x ^ (n + 1) * y‖ ≤ ‖x * y‖ := by
    rw [hveq]
    calc ‖x‖ ^ n * ‖x * y‖ ≤ 1 * ‖x * y‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg x) hx.le) (norm_nonneg _)
      _ = ‖x * y‖ := one_mul _
  calc ‖x ^ (n + 1) * y / (1 - x ^ (n + 1) * y) ^ 2‖
      ≤ ‖x ^ (n + 1) * y‖ / (1 - ‖x * y‖) ^ 2 := norm_div_one_sub_sq_le hva hxy
    _ = ‖x * y‖ / (1 - ‖x * y‖) ^ 2 * ‖x‖ ^ n := by rw [hveq]; ring

/-- `∑_{m : ℤ} (w + m)⁻²` converges (absolutely) for every `w`. -/
private lemma summable_int_inv_sq (w : ℂ) : Summable fun m : ℤ ↦ ((w + m) ^ 2)⁻¹ := by
  have h := EisensteinSeries.linear_right_summable w 1 (k := 2) le_rfl
  apply h.congr
  intro m
  norm_num
  norm_cast

private lemma summable_int_inv_sq_sub (w : ℂ) : Summable fun m : ℤ ↦ ((w - m) ^ 2)⁻¹ := by
  have h := (Equiv.neg ℤ).summable_iff.mpr (summable_int_inv_sq w)
  apply h.congr
  intro m
  simp only [Function.comp_apply, Equiv.neg_apply]
  push_cast
  rw [← sub_eq_add_neg]

private lemma tsum_int_inv_sq_sub (w : ℂ) :
    ∑' m : ℤ, ((w - m) ^ 2)⁻¹ = ∑' m : ℤ, ((w + m) ^ 2)⁻¹ := by
  rw [← (Equiv.neg ℤ).tsum_eq (fun m : ℤ ↦ ((w + m) ^ 2)⁻¹)]
  apply tsum_congr
  intro m
  simp only [Equiv.neg_apply]
  push_cast
  rw [← sub_eq_add_neg]

/-- Extension of `sum_int_inv_sq` to `w` in the lower half plane, using the evenness of
`w ↦ ∑_m (w + m)⁻²` and the invariance of `v/(1-v)²` under `v ↦ v⁻¹`. -/
private lemma sum_int_inv_sq' (w : ℂ) (hw : w.im ≠ 0) :
    ∑' m : ℤ, ((w + m) ^ 2)⁻¹ = (2 * (Real.pi : ℂ) * I) ^ 2 * (e w / (1 - e w) ^ 2) := by
  rcases hw.lt_or_gt with h | h
  · have h1 : ∑' m : ℤ, ((w + m) ^ 2)⁻¹ = ∑' m : ℤ, ((-w + m) ^ 2)⁻¹ := by
      rw [← tsum_int_inv_sq_sub (-w)]
      exact tsum_congr fun m ↦ by congr 1; ring
    rw [h1, sum_int_inv_sq (-w) (by simpa using h), e_neg,
      inv_div_one_sub_inv_sq (e_ne_zero w)]
  · exact sum_int_inv_sq w h

/-- The Basel problem over `ℤ`: `∑_{m : ℤ} m⁻² = π²/3` (the `m = 0` term is junk `0`). -/
private lemma hasSum_int_inv_sq :
    HasSum (fun m : ℤ ↦ ((m : ℂ) ^ 2)⁻¹) ((Real.pi : ℂ) ^ 2 / 3) := by
  have hs : Summable fun m : ℤ ↦ ((m : ℂ) ^ 2)⁻¹ := by
    apply (summable_int_inv_sq 0).congr
    intro m
    rw [zero_add]
  have h := hs.hasSum
  rwa [← two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by norm_num) ⟨1, by norm_num⟩,
    show (((2 : ℕ) : ℂ)) = (2 : ℂ) from by norm_num, riemannZeta_two,
    show (2 : ℂ) * ((Real.pi : ℂ) ^ 2 / 6) = (Real.pi : ℂ) ^ 2 / 3 from by ring] at h

/-- Dropping a vanishing `0`th term: `∑'_{n : ℕ+} g n = ∑'_{n : ℕ} g n` when `g 0 = 0`
(true without summability hypotheses, since both sides are junk simultaneously). -/
private lemma tsum_pnat_of_zero (g : ℕ → ℂ) (hg0 : g 0 = 0) :
    ∑' n : ℕ+, g n = ∑' n : ℕ, g n := by
  rw [tsum_pnat_eq_tsum_succ]
  by_cases hg : Summable g
  · rw [hg.tsum_eq_zero_add, hg0, zero_add]
  · rw [tsum_eq_zero_of_not_summable hg, tsum_eq_zero_of_not_summable
      fun h ↦ hg ((summable_nat_add_iff 1).mp h)]

/-- The Lambert sum over `ℕ+`: `∑_{c ≥ 1} c xᶜ = x/(1 - x)²` for `‖x‖ < 1`. -/
private lemma tsum_pnat_coe_mul_geometric {x : ℂ} (hx : ‖x‖ < 1) :
    ∑' c : ℕ+, (c : ℂ) * x ^ (c : ℕ) = x / (1 - x) ^ 2 := by
  rw [tsum_pnat_of_zero (fun c : ℕ ↦ (c : ℂ) * x ^ c) (by simp),
    tsum_coe_mul_geometric_of_norm_lt_one hx]

private lemma summable_corr_nat {q : ℂ} (hq1 : ‖q‖ < 1) :
    Summable fun n : ℕ ↦ q ^ n / (1 - q ^ n) ^ 2 := by
  apply (summable_nat_add_iff 1).mp
  have h := summable_aux (x := q) (y := 1) hq1 (by simpa using hq1)
  apply h.congr
  intro n
  rw [mul_one]

/-- The Lambert-to-divisor-sum rearrangement:
`∑_{n ≥ 0} qⁿ/(1 - qⁿ)² = ∑_{N ≥ 1} σ₁(N)qᴺ` (the `n = 0` term is junk `0`). -/
private lemma tsum_V_nat {q : ℂ} (hq1 : ‖q‖ < 1) :
    ∑' n : ℕ, q ^ n / (1 - q ^ n) ^ 2 = sAn 1 q := by
  rw [← tsum_pnat_of_zero (fun n : ℕ ↦ q ^ n / (1 - q ^ n) ^ 2) (by simp)]
  have h1 : ∀ d : ℕ+, q ^ (d : ℕ) / (1 - q ^ (d : ℕ)) ^ 2
      = ∑' c : ℕ+, (c : ℂ) ^ 1 * q ^ ((d : ℕ) * (c : ℕ)) := by
    intro d
    have hqd : ‖q ^ (d : ℕ)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq1 d.pos.ne'
    rw [← tsum_pnat_coe_mul_geometric hqd]
    apply tsum_congr
    intro c
    rw [pow_one, ← pow_mul]
  rw [tsum_congr h1, tsum_prod_pow_eq_tsum_sigma 1 hq1, sAn,
    tsum_pnat_of_zero (fun n : ℕ ↦ ((σ 1 n : ℕ) : ℂ) * q ^ n) (by simp)]

private lemma summable_corr_int {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    Summable fun n : ℤ ↦ q ^ n / (1 - q ^ n) ^ 2 := by
  have hpos : Summable fun n : ℕ ↦ q ^ (n : ℤ) / (1 - q ^ (n : ℤ)) ^ 2 := by
    apply (summable_corr_nat hq1).congr
    intro n
    rw [zpow_natCast]
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨hpos, hpos.congr fun n ↦ ?_⟩
  rw [zpow_neg, inv_div_one_sub_inv_sq (zpow_ne_zero _ hq0)]

/-- The corrector sum over `ℤ`: `∑_{n : ℤ} qⁿ/(1 - qⁿ)² = 2∑_{N ≥ 1} σ₁(N)qᴺ`
(the `n = 0` term is junk `0`, and `n ↔ -n` are equal). -/
private lemma tsum_corr_int {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    ∑' n : ℤ, q ^ n / (1 - q ^ n) ^ 2 = 2 * sAn 1 q := by
  have hpos : Summable fun n : ℕ ↦ q ^ (n : ℤ) / (1 - q ^ (n : ℤ)) ^ 2 := by
    apply (summable_corr_nat hq1).congr
    intro n
    rw [zpow_natCast]
  have hterm : ∀ n : ℕ, q ^ (-((n : ℤ) + 1)) / (1 - q ^ (-((n : ℤ) + 1))) ^ 2
      = q ^ (n + 1) / (1 - q ^ (n + 1)) ^ 2 := by
    intro n
    rw [zpow_neg, inv_div_one_sub_inv_sq (zpow_ne_zero _ hq0),
      show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hneg : Summable fun n : ℕ ↦ q ^ (-((n : ℤ) + 1)) / (1 - q ^ (-((n : ℤ) + 1))) ^ 2 := by
    apply Summable.congr _ fun n ↦ (hterm n).symm
    apply (summable_nat_add_iff 1).mpr (summable_corr_nat hq1)
  rw [tsum_of_nat_of_neg_add_one (f := fun n : ℤ ↦ q ^ n / (1 - q ^ n) ^ 2) hpos hneg,
    tsum_congr hterm]
  have h1 : ∑' n : ℕ, q ^ ((n : ℤ)) / (1 - q ^ ((n : ℤ))) ^ 2 = sAn 1 q := by
    rw [show (fun n : ℕ ↦ q ^ ((n : ℤ)) / (1 - q ^ ((n : ℤ))) ^ 2)
        = fun n : ℕ ↦ q ^ n / (1 - q ^ n) ^ 2 from funext fun n ↦ by rw [zpow_natCast],
      tsum_V_nat hq1]
  have h2 : ∑' n : ℕ, q ^ (n + 1) / (1 - q ^ (n + 1)) ^ 2 = sAn 1 q := by
    rw [← tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ q ^ n / (1 - q ^ n) ^ 2),
      tsum_pnat_of_zero (fun n : ℕ ↦ q ^ n / (1 - q ^ n) ^ 2) (by simp), tsum_V_nat hq1]
  rw [h1, h2]
  ring

/-- Summability of the series defining `XAn`, for `0 < ‖q‖ < ‖u‖ < 1`. -/
private lemma summable_V {u q : ℂ} (hq0 : q ≠ 0) (hqu : ‖q‖ < ‖u‖) (hu1 : ‖u‖ < 1) :
    Summable fun n : ℤ ↦ q ^ n * u / (1 - q ^ n * u) ^ 2 := by
  have hu0 : u ≠ 0 := norm_pos_iff.mp ((norm_nonneg q).trans_lt hqu)
  have hq1 : ‖q‖ < 1 := hqu.trans hu1
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · -- the terms `n ≥ 0`
    apply (summable_nat_add_iff 1).mp
    have h := summable_aux (x := q) (y := u) hq1
      (by rw [norm_mul]; nlinarith [norm_nonneg q, norm_nonneg u])
    apply h.congr
    intro n
    rw [zpow_natCast]
  · -- the terms `n ≤ 0`, after `v/(1-v)² = v⁻¹/(1-v⁻¹)²`
    have hterm : ∀ n : ℕ, q ^ n * u⁻¹ / (1 - q ^ n * u⁻¹) ^ 2
        = q ^ (-(n : ℤ)) * u / (1 - q ^ (-(n : ℤ)) * u) ^ 2 := by
      intro n
      rw [← inv_div_one_sub_inv_sq (v := q ^ (-(n : ℤ)) * u)
        (mul_ne_zero (zpow_ne_zero _ hq0) hu0), mul_inv, zpow_neg, inv_inv, zpow_natCast]
    apply Summable.congr _ hterm
    apply (summable_nat_add_iff 1).mp
    have h := summable_aux (x := q) (y := u⁻¹) hq1
      (by rw [norm_mul, norm_inv, ← div_eq_mul_inv]
          exact (div_lt_one (norm_pos_iff.mpr hu0)).mpr hqu)
    exact h

/-- For `0 < im z < im τ`, every row `z - nτ` avoids the real axis. -/
private lemma im_sub_int_mul_ne_zero {τ z : ℂ} (hτ : 0 < τ.im) (hz : 0 < z.im)
    (hzτ : z.im < τ.im) (n : ℤ) : (z - n * τ).im ≠ 0 := by
  have h1 : (z - n * τ).im = z.im - n * τ.im := by
    simp [Complex.sub_im, Complex.mul_im]
  rw [h1]
  rcases le_or_gt n 0 with h | h
  · have h2 : (n : ℝ) ≤ 0 := by exact_mod_cast h
    have h3 : 0 < z.im - n * τ.im := by nlinarith
    exact h3.ne'
  · have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have h3 : z.im - n * τ.im < 0 := by nlinarith
    exact h3.ne

private lemma periodPair_latticeEquiv_coe (τ : ℂ) (hτ : τ.im ≠ 0) (p : ℤ × ℤ) :
    (((periodPair τ hτ).latticeEquivProd.symm p : (periodPair τ hτ).lattice) : ℂ)
      = p.1 * τ + p.2 := by
  rw [PeriodPair.latticeEquiv_symm_apply, periodPair_ω₁, periodPair_ω₂, mul_one]

/-- The `q`-expansion of the Weierstrass `℘`-function (Silverman, *Advanced topics*,
Theorem I.6.2): for `τ` in the upper half plane and `0 < im z < im τ` (which forces
`z ∉ Λ_τ`),

`℘(z; Λ_τ) = (2πi)² (1/12 + Xₐ(e z, e τ))`.

Proof: group the absolutely convergent sum defining `℘` into rows `ω = nτ + m`,
`n : ℤ` (Fubini). The condition `0 < im z < im τ` guarantees `im (z - nτ) ≠ 0` for
every `n`, so each row evaluates via `sum_int_inv_sq'`: the row `n` contributes
`(2πi)² V(e(z - nτ)) - ∑_m (nτ + m)⁻²` where `V v = v/(1-v)²`, the corrector being
`2ζ(2) = π²/3` for `n = 0` (Basel) and `(2πi)² V(qⁿ)` for `n ≠ 0`. Summing over `n`,
the first parts give `(2πi)²(Xₐ + 2s₁(q))`, the correctors give
`(2πi)² ⬝ 2s₁(q) + π²/3` (Lambert/divisor-sum rearrangement, `tsum_corr_int`), and
`-π²/3 = (2πi)²/12`. -/
theorem weierstrassP_q_expansion (τ : ℂ) (hτ : 0 < τ.im) (z : ℂ) (hz : 0 < z.im)
    (hzτ : z.im < τ.im) :
    ℘[periodPair τ hτ.ne'] z =
      (2 * (Real.pi : ℂ) * I) ^ 2 * (1 / 12 + XAn (e z) (e τ)) := by
  have hq0 : e τ ≠ 0 := e_ne_zero τ
  have hu0 : e z ≠ 0 := e_ne_zero z
  have hu1 : ‖e z‖ < 1 := norm_e_lt_one hz
  have hqu : ‖e τ‖ < ‖e z‖ := norm_e_lt_norm_e hzτ
  have hq1 : ‖e τ‖ < 1 := hqu.trans hu1
  -- every row has nonreal `z - nτ`
  have him : ∀ n : ℤ, (z - n * τ).im ≠ 0 := im_sub_int_mul_ne_zero hτ hz hzτ
  -- Step 1: reindex the lattice sum by `ℤ × ℤ`
  have hcoe := periodPair_latticeEquiv_coe τ hτ.ne'
  have h0 : HasSum (fun p : ℤ × ℤ ↦
      ((z - (p.1 * τ + p.2)) ^ 2)⁻¹ - (((p.1 * τ + p.2 : ℂ)) ^ 2)⁻¹)
      (℘[periodPair τ hτ.ne'] z) := by
    have h2 := ((periodPair τ hτ.ne').latticeEquivProd.symm.toEquiv.hasSum_iff).mpr
      ((periodPair τ hτ.ne').hasSum_weierstrassP z)
    have hfun : ((fun l : (periodPair τ hτ.ne').lattice ↦ 1 / (z - l) ^ 2 - 1 / (l : ℂ) ^ 2)
        ∘ (periodPair τ hτ.ne').latticeEquivProd.symm.toEquiv)
        = fun p : ℤ × ℤ ↦ ((z - (p.1 * τ + p.2)) ^ 2)⁻¹ - (((p.1 * τ + p.2 : ℂ)) ^ 2)⁻¹ := by
      funext p
      simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, hcoe p, one_div]
    rw [hfun] at h2
    exact h2
  -- Step 2: summability of rows and Fubini
  have hrowsummA : ∀ n : ℤ, Summable fun m : ℤ ↦ ((z - (n * τ + m)) ^ 2)⁻¹ := by
    intro n
    apply (summable_int_inv_sq_sub (z - n * τ)).congr
    intro m
    congr 1
    ring
  have hrowsummB : ∀ n : ℤ, Summable fun m : ℤ ↦ (((n * τ + m : ℂ)) ^ 2)⁻¹ :=
    fun n ↦ summable_int_inv_sq (n * τ)
  have h2 : ℘[periodPair τ hτ.ne'] z
      = ∑' n : ℤ, ∑' m : ℤ, (((z - (n * τ + m)) ^ 2)⁻¹ - (((n * τ + m : ℂ)) ^ 2)⁻¹) := by
    rw [← h0.tsum_eq]
    exact h0.summable.tsum_prod' fun n ↦ (hrowsummA n).sub (hrowsummB n)
  -- Step 3: evaluate each row
  have hrowval : ∀ n : ℤ,
      ∑' m : ℤ, (((z - (n * τ + m)) ^ 2)⁻¹ - (((n * τ + m : ℂ)) ^ 2)⁻¹)
      = (2 * (Real.pi : ℂ) * I) ^ 2 * (e τ ^ (-n) * e z / (1 - e τ ^ (-n) * e z) ^ 2)
        - ((2 * (Real.pi : ℂ) * I) ^ 2 * (e τ ^ n / (1 - e τ ^ n) ^ 2)
            + if n = 0 then (Real.pi : ℂ) ^ 2 / 3 else 0) := by
    intro n
    rw [Summable.tsum_sub (hrowsummA n) (hrowsummB n)]
    congr 1
    · -- the row through `z`
      have hA : ∑' m : ℤ, ((z - (n * τ + m)) ^ 2)⁻¹ = ∑' m : ℤ, (((z - n * τ) - m) ^ 2)⁻¹ :=
        tsum_congr fun m ↦ by congr 1; ring
      have he : e (z - n * τ) = e τ ^ (-n) * e z := by
        rw [sub_eq_add_neg, e_add, show -((n : ℂ) * τ) = ((-n : ℤ) : ℂ) * τ by push_cast; ring,
          e_intMul, mul_comm]
      rw [hA, tsum_int_inv_sq_sub, sum_int_inv_sq' _ (him n), he]
    · -- the corrector row
      rcases eq_or_ne n 0 with rfl | hn
      · rw [show ∑' m : ℤ, (((((0 : ℤ) : ℂ)) * τ + m) ^ 2)⁻¹ = ∑' m : ℤ, ((m : ℂ) ^ 2)⁻¹ from
          tsum_congr fun m ↦ by norm_num, hasSum_int_inv_sq.tsum_eq]
        simp
      · have him2 : ((n : ℂ) * τ).im ≠ 0 := by
          have h3 : ((n : ℂ) * τ).im = n * τ.im := by simp [Complex.mul_im]
          rw [h3]
          exact mul_ne_zero (by exact_mod_cast hn) hτ.ne'
        rw [sum_int_inv_sq' _ him2, e_intMul, if_neg hn, add_zero]
  -- Step 4: sum the rows
  have hT1 : Summable fun n : ℤ ↦
      (2 * (Real.pi : ℂ) * I) ^ 2 * (e τ ^ (-n) * e z / (1 - e τ ^ (-n) * e z) ^ 2) := by
    apply Summable.mul_left
    have h := (Equiv.neg ℤ).summable_iff.mpr (summable_V hq0 hqu hu1)
    apply h.congr
    intro n
    simp only [Function.comp_apply, Equiv.neg_apply]
  have hT2 : Summable fun n : ℤ ↦
      (2 * (Real.pi : ℂ) * I) ^ 2 * (e τ ^ n / (1 - e τ ^ n) ^ 2) :=
    Summable.mul_left _ (summable_corr_int hq0 hq1)
  have hT3 : Summable fun n : ℤ ↦ (if n = 0 then (Real.pi : ℂ) ^ 2 / 3 else 0) :=
    (hasSum_ite_eq (0 : ℤ) ((Real.pi : ℂ) ^ 2 / 3)).summable
  rw [h2, tsum_congr hrowval, Summable.tsum_sub hT1 (hT2.add hT3),
    Summable.tsum_add hT2 hT3, tsum_mul_left, tsum_mul_left, tsum_ite_eq]
  -- Step 5: identify the two series and conclude
  have hS : ∑' n : ℤ, e τ ^ (-n) * e z / (1 - e τ ^ (-n) * e z) ^ 2
      = XAn (e z) (e τ) + 2 * sAn 1 (e τ) := by
    have h := (Equiv.neg ℤ).tsum_eq (fun n : ℤ ↦ e τ ^ n * e z / (1 - e τ ^ n * e z) ^ 2)
    have h3 : ∑' n : ℤ, e τ ^ (-n) * e z / (1 - e τ ^ (-n) * e z) ^ 2
        = ∑' n : ℤ, e τ ^ n * e z / (1 - e τ ^ n * e z) ^ 2 := by
      rw [← h]
      exact tsum_congr fun n ↦ by simp only [Equiv.neg_apply]
    rw [h3, XAn]
    ring
  rw [hS, tsum_corr_int hq0 hq1]
  have hI2 : (2 * (Real.pi : ℂ) * I) ^ 2 = -4 * (Real.pi : ℂ) ^ 2 := by
    rw [mul_pow, mul_pow, Complex.I_sq]
    ring
  rw [hI2]
  ring

/-- Norm bound for `vʲ/(1 - v)ᵏ` when `‖v‖ ≤ a < 1`. -/
private lemma norm_pow_div_one_sub_pow_le {v : ℂ} {a : ℝ} (hva : ‖v‖ ≤ a) (ha : a < 1)
    (j k : ℕ) : ‖v ^ j / (1 - v) ^ k‖ ≤ ‖v‖ ^ j / (1 - a) ^ k := by
  have h0 : (0 : ℝ) < 1 - a := by linarith
  have h1 : 1 - a ≤ ‖1 - v‖ := by
    have h2 := norm_sub_norm_le (1 : ℂ) v
    rw [norm_one] at h2
    linarith
  have h2 : (1 - a) ^ k ≤ ‖1 - v‖ ^ k := pow_le_pow_left₀ h0.le h1 k
  have h3 : (0 : ℝ) < ‖1 - v‖ ^ k := lt_of_lt_of_le (pow_pos h0 k) h2
  rw [norm_div, norm_pow, norm_pow, div_le_div_iff₀ h3 (pow_pos h0 k)]
  exact mul_le_mul_of_nonneg_left h2 (pow_nonneg (norm_nonneg v) j)

/-- Generalisation of `summable_aux` to the terms `(xⁿy)ʲ/(1 - xⁿy)ᵏ`, `j ≥ 1`. -/
private lemma summable_aux' {x y : ℂ} (hx : ‖x‖ < 1) (hxy : ‖x * y‖ < 1) {j k : ℕ}
    (hj : 1 ≤ j) :
    Summable fun n : ℕ ↦ (x ^ (n + 1) * y) ^ j / (1 - x ^ (n + 1) * y) ^ k := by
  apply Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left (‖x * y‖ / (1 - ‖x * y‖) ^ k))
  intro n
  have hveq : ‖x ^ (n + 1) * y‖ = ‖x‖ ^ n * ‖x * y‖ := by
    rw [pow_succ, mul_assoc, norm_mul, norm_pow]
  have hva : ‖x ^ (n + 1) * y‖ ≤ ‖x * y‖ := by
    rw [hveq]
    calc ‖x‖ ^ n * ‖x * y‖ ≤ 1 * ‖x * y‖ :=
          mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg x) hx.le) (norm_nonneg _)
      _ = ‖x * y‖ := one_mul _
  have hvj : ‖x ^ (n + 1) * y‖ ^ j ≤ ‖x ^ (n + 1) * y‖ := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    calc ‖x ^ (n + 1) * y‖ ^ (i + 1) = ‖x ^ (n + 1) * y‖ ^ i * ‖x ^ (n + 1) * y‖ :=
          pow_succ _ _
      _ ≤ 1 * ‖x ^ (n + 1) * y‖ :=
          mul_le_mul_of_nonneg_right
            (pow_le_one₀ (norm_nonneg _) (hva.trans hxy.le)) (norm_nonneg _)
      _ = ‖x ^ (n + 1) * y‖ := one_mul _
  have h1 : (0 : ℝ) < 1 - ‖x * y‖ := by linarith
  calc ‖(x ^ (n + 1) * y) ^ j / (1 - x ^ (n + 1) * y) ^ k‖
      ≤ ‖x ^ (n + 1) * y‖ ^ j / (1 - ‖x * y‖) ^ k := norm_pow_div_one_sub_pow_le hva hxy j k
    _ ≤ ‖x ^ (n + 1) * y‖ / (1 - ‖x * y‖) ^ k := by
        rw [div_le_div_iff₀ (pow_pos h1 k) (pow_pos h1 k)]
        exact mul_le_mul_of_nonneg_right hvj (pow_pos h1 k).le
    _ = ‖x * y‖ / (1 - ‖x * y‖) ^ k * ‖x‖ ^ n := by rw [hveq]; ring

/-- The rational-function identity `(v⁻¹)²/(1 - v⁻¹)³ = -(v/(1 - v)³)` for `v ≠ 0`. -/
private lemma inv_sq_div_one_sub_inv_cube {v : ℂ} (hv : v ≠ 0) :
    (v⁻¹) ^ 2 / (1 - v⁻¹) ^ 3 = -(v / (1 - v) ^ 3) := by
  rcases eq_or_ne v 1 with rfl | hv1
  · norm_num
  · have h1 : 1 - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
    have h2 : 1 - v⁻¹ ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h ↦ hv1 (inv_eq_one.mp h.symm)
    field_simp
    ring

/-- The rational-function identity `v⁻¹(1 + v⁻¹)/(1 - v⁻¹)³ = -(v(1 + v)/(1 - v)³)`
for `v ≠ 0`: the function on the right-hand side of `sum_int_inv_cube` is odd under
`v ↦ v⁻¹`. -/
private lemma inv_mul_one_add_inv_div_one_sub_inv_cube {v : ℂ} (hv : v ≠ 0) :
    v⁻¹ * (1 + v⁻¹) / (1 - v⁻¹) ^ 3 = -(v * (1 + v) / (1 - v) ^ 3) := by
  rcases eq_or_ne v 1 with rfl | hv1
  · norm_num
  · have h1 : 1 - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
    have h2 : 1 - v⁻¹ ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h ↦ hv1 (inv_eq_one.mp h.symm)
    field_simp
    ring

/-- The rational-function identity `v/(1-v)² + 2v²/(1-v)³ = v(1+v)/(1-v)³` recombining
the `XAn` and `YAn` summands into the `℘'` row sums (also true at the junk value
`v = 1`, where all terms are `0`). -/
private lemma div_sq_add_two_mul_div_cube (v : ℂ) :
    v / (1 - v) ^ 2 + 2 * (v ^ 2 / (1 - v) ^ 3) = v * (1 + v) / (1 - v) ^ 3 := by
  rcases eq_or_ne v 1 with rfl | hv1
  · norm_num
  · have h1 : 1 - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
    field_simp
    ring

private lemma summable_int_inv_cube (w : ℂ) : Summable fun m : ℤ ↦ ((w + m) ^ 3)⁻¹ := by
  have h := EisensteinSeries.linear_right_summable w 1 (k := 3) (by norm_num)
  apply h.congr
  intro m
  norm_num
  norm_cast

private lemma summable_int_inv_cube_sub (w : ℂ) :
    Summable fun m : ℤ ↦ ((w - m) ^ 3)⁻¹ := by
  have h := (Equiv.neg ℤ).summable_iff.mpr (summable_int_inv_cube w)
  apply h.congr
  intro m
  simp only [Function.comp_apply, Equiv.neg_apply]
  push_cast
  rw [← sub_eq_add_neg]

private lemma tsum_int_inv_cube_sub (w : ℂ) :
    ∑' m : ℤ, ((w - m) ^ 3)⁻¹ = ∑' m : ℤ, ((w + m) ^ 3)⁻¹ := by
  rw [← (Equiv.neg ℤ).tsum_eq (fun m : ℤ ↦ ((w + m) ^ 3)⁻¹)]
  apply tsum_congr
  intro m
  simp only [Equiv.neg_apply]
  push_cast
  rw [← sub_eq_add_neg]

/-- Extension of `sum_int_inv_cube` to `w` in the lower half plane. In contrast to the
square case, the row sum is *odd* under `w ↦ -w`, matching the oddness of
`v(1+v)/(1-v)³` under `v ↦ v⁻¹`. -/
private lemma sum_int_inv_cube' (w : ℂ) (hw : w.im ≠ 0) :
    ∑' m : ℤ, ((w + m) ^ 3)⁻¹ =
      -(2 * (Real.pi : ℂ) * I) ^ 3 / 2 * (e w * (1 + e w) / (1 - e w) ^ 3) := by
  rcases hw.lt_or_gt with h | h
  · have h1 : ∑' m : ℤ, ((w + m) ^ 3)⁻¹ = -∑' m : ℤ, ((-w + m) ^ 3)⁻¹ := by
      rw [← tsum_neg, ← (Equiv.neg ℤ).tsum_eq (fun m : ℤ ↦ -((-w + m) ^ 3)⁻¹)]
      apply tsum_congr
      intro m
      simp only [Equiv.neg_apply]
      push_cast
      rw [show -w + -(m : ℂ) = -(w + m) from by ring,
        Odd.neg_pow (⟨1, by norm_num⟩ : Odd 3), inv_neg, neg_neg]
    rw [h1, sum_int_inv_cube (-w) (by simpa using h), e_neg,
      inv_mul_one_add_inv_div_one_sub_inv_cube (e_ne_zero w)]
    ring
  · exact sum_int_inv_cube w h

/-- Summability of the series defining `YAn`, for `0 < ‖q‖ < ‖u‖ < 1`. -/
private lemma summable_V₂ {u q : ℂ} (hq0 : q ≠ 0) (hqu : ‖q‖ < ‖u‖) (hu1 : ‖u‖ < 1) :
    Summable fun n : ℤ ↦ (q ^ n * u) ^ 2 / (1 - q ^ n * u) ^ 3 := by
  have hu0 : u ≠ 0 := norm_pos_iff.mp ((norm_nonneg q).trans_lt hqu)
  have hq1 : ‖q‖ < 1 := hqu.trans hu1
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · apply (summable_nat_add_iff 1).mp
    have h := summable_aux' (x := q) (y := u) hq1
      (by rw [norm_mul]; nlinarith [norm_nonneg q, norm_nonneg u]) (j := 2) (k := 3)
      one_le_two
    apply h.congr
    intro n
    rw [zpow_natCast]
  · have hterm : ∀ n : ℕ, -((q ^ n * u⁻¹) ^ 1 / (1 - q ^ n * u⁻¹) ^ 3)
        = (q ^ (-(n : ℤ)) * u) ^ 2 / (1 - q ^ (-(n : ℤ)) * u) ^ 3 := by
      intro n
      have hv : (q ^ n * u⁻¹)⁻¹ = q ^ (-(n : ℤ)) * u := by
        rw [mul_inv, inv_inv, zpow_neg, zpow_natCast]
      have h := inv_sq_div_one_sub_inv_cube (v := q ^ n * u⁻¹)
        (mul_ne_zero (pow_ne_zero _ hq0) (inv_ne_zero hu0))
      rw [hv] at h
      rw [pow_one, ← h]
    apply Summable.congr _ hterm
    apply Summable.neg
    apply (summable_nat_add_iff 1).mp
    exact summable_aux' (x := q) (y := u⁻¹) hq1
      (by rw [norm_mul, norm_inv, ← div_eq_mul_inv]
          exact (div_lt_one (norm_pos_iff.mpr hu0)).mpr hqu) (j := 1) (k := 3) le_rfl

/-- The `q`-expansion of `℘'` (Silverman, *Advanced topics*, Theorem I.6.2): under the
hypotheses of `weierstrassP_q_expansion`,

`℘'(z; Λ_τ) = (2πi)³ (Xₐ(e z, e τ) + 2Yₐ(e z, e τ))`.

Proof: as for `weierstrassP_q_expansion`, but simpler: group the absolutely convergent
sum `℘'(z) = -2∑_ω (z - ω)⁻³` into rows `ω = nτ + m` (no regularising terms are needed
here) and apply `sum_int_inv_cube'` to each row. The identity
`v/(1-v)² + 2v²/(1-v)³ = v(1+v)/(1-v)³` recombines the result into `Xₐ + 2Yₐ`. -/
theorem derivWeierstrassP_q_expansion (τ : ℂ) (hτ : 0 < τ.im) (z : ℂ) (hz : 0 < z.im)
    (hzτ : z.im < τ.im) :
    ℘'[periodPair τ hτ.ne'] z =
      (2 * (Real.pi : ℂ) * I) ^ 3 * (XAn (e z) (e τ) + 2 * YAn (e z) (e τ)) := by
  have hq0 : e τ ≠ 0 := e_ne_zero τ
  have hu0 : e z ≠ 0 := e_ne_zero z
  have hu1 : ‖e z‖ < 1 := norm_e_lt_one hz
  have hqu : ‖e τ‖ < ‖e z‖ := norm_e_lt_norm_e hzτ
  have hq1 : ‖e τ‖ < 1 := hqu.trans hu1
  have him : ∀ n : ℤ, (z - n * τ).im ≠ 0 := im_sub_int_mul_ne_zero hτ hz hzτ
  -- Step 1: reindex the lattice sum by `ℤ × ℤ`
  have hcoe := periodPair_latticeEquiv_coe τ hτ.ne'
  have h0 : HasSum (fun p : ℤ × ℤ ↦ -2 / (z - (p.1 * τ + p.2)) ^ 3)
      (℘'[periodPair τ hτ.ne'] z) := by
    have h2 := ((periodPair τ hτ.ne').latticeEquivProd.symm.toEquiv.hasSum_iff).mpr
      ((periodPair τ hτ.ne').hasSum_derivWeierstrassP z)
    have hfun : ((fun l : (periodPair τ hτ.ne').lattice ↦ -2 / (z - l) ^ 3)
        ∘ (periodPair τ hτ.ne').latticeEquivProd.symm.toEquiv)
        = fun p : ℤ × ℤ ↦ -2 / (z - (p.1 * τ + p.2)) ^ 3 := by
      funext p
      simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, hcoe p]
    rw [hfun] at h2
    exact h2
  -- Step 2: summability of rows and Fubini
  have hrowsumm : ∀ n : ℤ, Summable fun m : ℤ ↦ -2 / (z - (n * τ + m)) ^ 3 := by
    intro n
    apply ((summable_int_inv_cube_sub (z - n * τ)).mul_left (-2)).congr
    intro m
    rw [div_eq_mul_inv, show z - (n * τ + m) = z - n * τ - m from by ring]
  have h2 : ℘'[periodPair τ hτ.ne'] z
      = ∑' n : ℤ, ∑' m : ℤ, -2 / (z - (n * τ + m)) ^ 3 := by
    rw [← h0.tsum_eq]
    exact h0.summable.tsum_prod' fun n ↦ hrowsumm n
  -- Step 3: evaluate each row
  have hrowval : ∀ n : ℤ,
      ∑' m : ℤ, -2 / (z - (n * τ + m)) ^ 3
      = (2 * (Real.pi : ℂ) * I) ^ 3 *
          (e τ ^ (-n) * e z * (1 + e τ ^ (-n) * e z) / (1 - e τ ^ (-n) * e z) ^ 3) := by
    intro n
    have hA : ∑' m : ℤ, -2 / (z - (n * τ + m)) ^ 3
        = -2 * ∑' m : ℤ, (((z - n * τ) - m) ^ 3)⁻¹ := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      rw [div_eq_mul_inv, show z - (n * τ + m) = z - n * τ - m from by ring]
    have he : e (z - n * τ) = e τ ^ (-n) * e z := by
      rw [sub_eq_add_neg, e_add,
        show -((n : ℂ) * τ) = ((-n : ℤ) : ℂ) * τ from by push_cast; ring, e_intMul, mul_comm]
    rw [hA, tsum_int_inv_cube_sub, sum_int_inv_cube' _ (him n), he]
    ring
  -- Step 4: sum the rows and recombine into `XAn + 2YAn`
  rw [h2, tsum_congr hrowval, tsum_mul_left]
  have h3 : ∑' n : ℤ, e τ ^ (-n) * e z * (1 + e τ ^ (-n) * e z) / (1 - e τ ^ (-n) * e z) ^ 3
      = ∑' n : ℤ, e τ ^ n * e z * (1 + e τ ^ n * e z) / (1 - e τ ^ n * e z) ^ 3 := by
    rw [← (Equiv.neg ℤ).tsum_eq
      (fun n : ℤ ↦ e τ ^ n * e z * (1 + e τ ^ n * e z) / (1 - e τ ^ n * e z) ^ 3)]
    exact tsum_congr fun n ↦ by simp only [Equiv.neg_apply]
  have hsplit : ∑' n : ℤ, e τ ^ n * e z * (1 + e τ ^ n * e z) / (1 - e τ ^ n * e z) ^ 3
      = XAn (e z) (e τ) + 2 * YAn (e z) (e τ) := by
    have hpt : ∀ n : ℤ, e τ ^ n * e z * (1 + e τ ^ n * e z) / (1 - e τ ^ n * e z) ^ 3
        = e τ ^ n * e z / (1 - e τ ^ n * e z) ^ 2
          + 2 * ((e τ ^ n * e z) ^ 2 / (1 - e τ ^ n * e z) ^ 3) :=
      fun n ↦ (div_sq_add_two_mul_div_cube _).symm
    rw [tsum_congr hpt,
      Summable.tsum_add (summable_V hq0 hqu hu1) ((summable_V₂ hq0 hqu hu1).mul_left 2),
      tsum_mul_left, XAn, YAn]
    ring
  rw [h3, hsplit]

private lemma summable_int_inv_fourth (w : ℂ) : Summable fun m : ℤ ↦ ((w + m) ^ 4)⁻¹ := by
  have h := EisensteinSeries.linear_right_summable w 1 (k := 4) (by norm_num)
  apply h.congr
  intro m
  norm_num
  norm_cast

/-- Evenness of the weight-`4` row sum under `w ↦ -w`. -/
private lemma tsum_int_inv_fourth_neg (w : ℂ) :
    ∑' m : ℤ, ((w + m) ^ 4)⁻¹ = ∑' m : ℤ, ((-w + m) ^ 4)⁻¹ := by
  rw [← (Equiv.neg ℤ).tsum_eq (fun m : ℤ ↦ ((-w + m) ^ 4)⁻¹)]
  apply tsum_congr
  intro m
  simp only [Equiv.neg_apply]
  push_cast
  rw [show -w + -(m : ℂ) = -(w + m) from by ring, Even.neg_pow (⟨2, by norm_num⟩ : Even 4)]

/-- Row sum, exponent `4`: for `w` in the upper half plane,
`∑_{m : ℤ} (w + m)⁻⁴ = (2πi)⁴/6 ⬝ ∑_{d ≥ 1} d³e(w)ᵈ`.
This is the case `k = 3` of `EisensteinSeries.qExpansion_identity`. -/
private lemma sum_int_inv_fourth (w : ℂ) (hw : 0 < w.im) :
    ∑' m : ℤ, ((w + m) ^ 4)⁻¹
      = (2 * (Real.pi : ℂ) * I) ^ 4 / 6 * ∑' d : ℕ, (d : ℂ) ^ 3 * e w ^ d := by
  have h := EisensteinSeries.qExpansion_identity (k := 3) (by norm_num)
    (⟨w, hw⟩ : UpperHalfPlane)
  simp only [one_div, Nat.reduceAdd] at h
  simp only [e]
  rw [h, show ((Nat.factorial 3 : ℕ) : ℂ) = 6 from by norm_num [Nat.factorial]]
  ring

/-- The Basel-type sum over `ℤ` in weight `4`: `∑_{m : ℤ} m⁻⁴ = π⁴/45`. -/
private lemma hasSum_int_inv_fourth :
    HasSum (fun m : ℤ ↦ ((m : ℂ) ^ 4)⁻¹) ((Real.pi : ℂ) ^ 4 / 45) := by
  have hs : Summable fun m : ℤ ↦ ((m : ℂ) ^ 4)⁻¹ := by
    apply (summable_int_inv_fourth 0).congr
    intro m
    rw [zero_add]
  have h := hs.hasSum
  rwa [← two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by norm_num) ⟨2, by norm_num⟩,
    show (((4 : ℕ) : ℂ)) = (4 : ℂ) from by norm_num, riemannZeta_four,
    show (2 : ℂ) * ((Real.pi : ℂ) ^ 4 / 90) = (Real.pi : ℂ) ^ 4 / 45 from by ring] at h

/-- `∑ dᵏ` diverges; used to see that the Lambert series contributes junk `0` in the
`n = 0` row. -/
private lemma not_summable_natCast_pow (k : ℕ) : ¬ Summable fun d : ℕ ↦ (d : ℂ) ^ k := by
  intro hs
  have h2 : Filter.Tendsto (fun d : ℕ ↦ ‖(d : ℂ) ^ k‖) Filter.atTop (nhds 0) := by
    simpa using hs.tendsto_atTop_zero.norm
  obtain ⟨d, hd1, hd2⟩ := ((h2.eventually_lt_const one_pos).and
    (Filter.eventually_ge_atTop 1)).exists
  rw [norm_pow, Complex.norm_natCast] at hd1
  have h3 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd2
  have h4 : (1 : ℝ) ≤ (d : ℝ) ^ k := one_le_pow₀ h3
  linarith

/-- The `q`-expansion of `g₂` (Silverman, *Advanced topics*, Theorem I.7.1):

`g₂(Λ_τ) = (2πi)⁴/12 ⬝ (1 + 240s₃(q))`.

Proof: `g₂ = 60G₄` where `G₄` is the lattice sum `∑'_{ω ∈ Λ_τ} ω⁻⁴` (the `ω = 0` term
being junk `0`), which converges by `PeriodPair.hasSum_sumInvPow`. Reindex by `ℤ × ℤ`
and evaluate the row `nτ + m` by `sum_int_inv_fourth` (evenness reduces `n < 0` to
`n > 0`, and the row `n = 0` is `2ζ(4) = π⁴/45` by `hasSum_zeta_four`): the row `n ≠ 0`
is `(2πi)⁴/6 ⬝ ∑_d d³q^{|n|d}`. Summing over `n` and rearranging by Fubini
(`tsum_prod_pow_eq_tsum_sigma`) gives `G₄ = π⁴/45 + (2πi)⁴/3 ⬝ ∑_N σ₃(N)qᴺ`, and
`60 ⬝ π⁴/45 = (2πi)⁴/12`. -/
theorem g₂_q_expansion (τ : ℂ) (hτ : 0 < τ.im) :
    (periodPair τ hτ.ne').g₂ =
      (2 * (Real.pi : ℂ) * I) ^ 4 / 12 * (1 + 240 * sAn 3 (e τ)) := by
  have hq1 : ‖e τ‖ < 1 := norm_e_lt_one hτ
  have hcoe := periodPair_latticeEquiv_coe τ hτ.ne'
  -- Step 1: the lattice sum defining `G 4`, reindexed by `ℤ × ℤ`
  have hG : HasSum (fun l : (periodPair τ hτ.ne').lattice ↦ ((l : ℂ) ^ 4)⁻¹)
      ((periodPair τ hτ.ne').G 4) := by
    have h := (periodPair τ hτ.ne').hasSum_sumInvPow 0 (by norm_num : (2 : ℕ) < 4)
    rw [PeriodPair.sumInvPow_zero] at h
    simpa using h
  have h0 : HasSum (fun p : ℤ × ℤ ↦ (((p.1 : ℂ) * τ + p.2) ^ 4)⁻¹)
      ((periodPair τ hτ.ne').G 4) := by
    have h2 := ((periodPair τ hτ.ne').latticeEquivProd.symm.toEquiv.hasSum_iff).mpr hG
    have hfun : ((fun l : (periodPair τ hτ.ne').lattice ↦ ((l : ℂ) ^ 4)⁻¹)
        ∘ (periodPair τ hτ.ne').latticeEquivProd.symm.toEquiv)
        = fun p : ℤ × ℤ ↦ (((p.1 : ℂ) * τ + p.2) ^ 4)⁻¹ := by
      funext p
      simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, hcoe p]
    rw [hfun] at h2
    exact h2
  -- Step 2: evaluate each row (the Lambert series is junk `0` in the row `n = 0`)
  have hrowval : ∀ n : ℤ,
      ∑' m : ℤ, (((n : ℂ) * τ + m) ^ 4)⁻¹
      = (2 * (Real.pi : ℂ) * I) ^ 4 / 6 * ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ n.natAbs) ^ d
        + (if n = 0 then (Real.pi : ℂ) ^ 4 / 45 else 0) := by
    intro n
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · have him' : (0 : ℝ) < (-((n : ℂ) * τ)).im := by
        have him : (-((n : ℂ) * τ)).im = -((n : ℝ) * τ.im) := by
          simp [Complex.mul_im]
        rw [him]
        have h2 : (n : ℝ) < 0 := by exact_mod_cast hn
        nlinarith
      have he : e (-((n : ℂ) * τ)) = e τ ^ n.natAbs := by
        rw [show -((n : ℂ) * τ) = (((-n : ℤ) : ℂ)) * τ from by push_cast; ring, e_intMul,
          show -n = (n.natAbs : ℤ) from by omega, zpow_natCast]
      rw [tsum_int_inv_fourth_neg, sum_int_inv_fourth _ him', he, if_neg hn.ne, add_zero]
    · have hB : ∑' m : ℤ, ((((0 : ℤ) : ℂ) * τ + m) ^ 4)⁻¹ = ∑' m : ℤ, ((m : ℂ) ^ 4)⁻¹ :=
        tsum_congr fun m ↦ by norm_num
      rw [hB, hasSum_int_inv_fourth.tsum_eq,
        show (∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ (0 : ℤ).natAbs) ^ d) = 0 from by
          simp only [Int.natAbs_zero, pow_zero, one_pow, mul_one]
          exact tsum_eq_zero_of_not_summable (not_summable_natCast_pow 3)]
      simp
    · have him' : (0 : ℝ) < ((n : ℂ) * τ).im := by
        have him : ((n : ℂ) * τ).im = (n : ℝ) * τ.im := by simp [Complex.mul_im]
        rw [him]
        have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        nlinarith
      have he : e ((n : ℂ) * τ) = e τ ^ n.natAbs := by
        rw [show ((n : ℂ)) * τ = (((n.natAbs : ℤ) : ℂ)) * τ from by
            rw [show ((n.natAbs : ℤ)) = n from by omega],
          e_intMul, zpow_natCast]
      rw [sum_int_inv_fourth _ him', he, if_neg hn.ne', add_zero]
  -- Step 3: sum the rows (Fubini, which also gives summability of the row values)
  have hrowsHS : ∀ n : ℤ, HasSum (fun m : ℤ ↦ (((n : ℂ) * τ + m) ^ 4)⁻¹)
      ((2 * (Real.pi : ℂ) * I) ^ 4 / 6 * ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ n.natAbs) ^ d
        + (if n = 0 then (Real.pi : ℂ) ^ 4 / 45 else 0)) := by
    intro n
    have h := (summable_int_inv_fourth ((n : ℂ) * τ)).hasSum
    rwa [hrowval n] at h
  have hG2 := h0.prod_fiberwise hrowsHS
  have hite : Summable fun n : ℤ ↦ (if n = 0 then (Real.pi : ℂ) ^ 4 / 45 else 0) :=
    (hasSum_ite_eq (0 : ℤ) _).summable
  have hA : Summable fun n : ℤ ↦
      (2 * (Real.pi : ℂ) * I) ^ 4 / 6 * ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ n.natAbs) ^ d := by
    have h := hG2.summable.sub hite
    apply h.congr
    intro n
    ring
  -- Step 4: the divisor-sum rearrangement of the total Lambert contribution
  have hLsum : ∑' n : ℤ, ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ n.natAbs) ^ d
      = 2 * sAn 3 (e τ) := by
    have hC : ((2 * (Real.pi : ℂ) * I) ^ 4 / 6 : ℂ) ≠ 0 :=
      div_ne_zero (pow_ne_zero _ two_pi_I_ne_zero) (by norm_num)
    have hL : Summable fun n : ℤ ↦ ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ n.natAbs) ^ d := by
      have h := hA.mul_left ((2 * (Real.pi : ℂ) * I) ^ 4 / 6)⁻¹
      apply h.congr
      intro n
      rw [← mul_assoc, inv_mul_cancel₀ hC, one_mul]
    have hpos := (summable_int_iff_summable_nat_and_neg.mp hL).1
    have hnegall := (summable_int_iff_summable_nat_and_neg.mp hL).2
    have hneg : Summable fun n : ℕ ↦
        ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ (-((n : ℤ) + 1)).natAbs) ^ d := by
      have h := (summable_nat_add_iff 1).mpr hnegall
      apply h.congr
      intro n
      rw [show ((-((n + 1 : ℕ) : ℤ)).natAbs) = ((-((n : ℤ) + 1)).natAbs) from by omega]
    have hnatplain : ∑' n : ℕ, ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ n) ^ d = sAn 3 (e τ) := by
      rw [← tsum_pnat_of_zero (fun n : ℕ ↦ ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ n) ^ d) (by
        simp only [pow_zero, one_pow, mul_one]
        exact tsum_eq_zero_of_not_summable (not_summable_natCast_pow 3))]
      have hinner : ∀ n : ℕ+, ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ (n : ℕ)) ^ d
          = ∑' d : ℕ+, (d : ℂ) ^ 3 * e τ ^ ((n : ℕ) * (d : ℕ)) := by
        intro n
        rw [← tsum_pnat_of_zero (fun d : ℕ ↦ (d : ℂ) ^ 3 * (e τ ^ (n : ℕ)) ^ d) (by simp)]
        exact tsum_congr fun d ↦ by rw [pow_mul]
      rw [tsum_congr hinner, tsum_prod_pow_eq_tsum_sigma 3 hq1, sAn,
        tsum_pnat_of_zero (fun n : ℕ ↦ ((σ 3 n : ℕ) : ℂ) * e τ ^ n) (by simp)]
    rw [tsum_of_nat_of_neg_add_one
        (f := fun n : ℤ ↦ ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ n.natAbs) ^ d) hpos hneg,
      show (fun n : ℕ ↦ ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ ((n : ℤ)).natAbs) ^ d)
        = fun n : ℕ ↦ ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ n) ^ d from funext fun n ↦ by
          rw [show ((n : ℤ)).natAbs = n from by omega],
      show (fun n : ℕ ↦ ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ (-((n : ℤ) + 1)).natAbs) ^ d)
        = fun n : ℕ ↦ ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ (n + 1)) ^ d from funext fun n ↦ by
          rw [show (-((n : ℤ) + 1)).natAbs = n + 1 from by omega],
      ← tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ n) ^ d),
      tsum_pnat_of_zero (fun n : ℕ ↦ ∑' d : ℕ, (d : ℂ) ^ 3 * (e τ ^ n) ^ d) (by
        simp only [pow_zero, one_pow, mul_one]
        exact tsum_eq_zero_of_not_summable (not_summable_natCast_pow 3)),
      hnatplain]
    ring
  -- Step 5: assemble
  rw [PeriodPair.g₂, ← hG2.tsum_eq, Summable.tsum_add hA hite, tsum_mul_left, tsum_ite_eq,
    hLsum]
  have hI4 : (2 * (Real.pi : ℂ) * I) ^ 4 = 16 * (Real.pi : ℂ) ^ 4 := by
    have h1 : I ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]
      norm_num
    rw [mul_pow, mul_pow, h1, mul_one]
    ring
  rw [hI4]
  ring

private theorem bernoulli'_five : bernoulli' 5 = 0 := by
  rw [bernoulli'_def]; norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose]

private theorem bernoulli'_six : bernoulli' 6 = 1 / 42 := by
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, bernoulli'_five]


open Real in
/-- The value `ζ(6) = π⁶/945` (companion to Mathlib's `riemannZeta_four`). -/
theorem riemannZeta_six : riemannZeta 6 = (π : ℂ) ^ 6 / 945 := by
  have h := riemannZeta_two_mul_nat (k := 3) (by norm_num)
  rw [show (2 * ((3 : ℕ) : ℂ)) = 6 by norm_num] at h
  rw [h, bernoulli_eq_bernoulli'_of_ne_one (by norm_num), bernoulli'_six]
  norm_num [Nat.factorial]
  ring

private lemma summable_int_inv_sixth (w : ℂ) : Summable fun m : ℤ ↦ ((w + m) ^ 6)⁻¹ := by
  have h := EisensteinSeries.linear_right_summable w 1 (k := 6) (by norm_num)
  apply h.congr
  intro m
  norm_num
  norm_cast

/-- Evenness of the weight-`6` row sum under `w ↦ -w`. -/
private lemma tsum_int_inv_sixth_neg (w : ℂ) :
    ∑' m : ℤ, ((w + m) ^ 6)⁻¹ = ∑' m : ℤ, ((-w + m) ^ 6)⁻¹ := by
  rw [← (Equiv.neg ℤ).tsum_eq (fun m : ℤ ↦ ((-w + m) ^ 6)⁻¹)]
  apply tsum_congr
  intro m
  simp only [Equiv.neg_apply]
  push_cast
  rw [show -w + -(m : ℂ) = -(w + m) from by ring, Even.neg_pow (⟨3, by norm_num⟩ : Even 6)]

/-- Row sum, exponent `6`: for `w` in the upper half plane,
`∑_{m : ℤ} (w + m)⁻⁶ = (2πi)⁶/120 ⬝ ∑_{d ≥ 1} d⁵e(w)ᵈ`.
This is the case `k = 5` of `EisensteinSeries.qExpansion_identity`. -/
private lemma sum_int_inv_sixth (w : ℂ) (hw : 0 < w.im) :
    ∑' m : ℤ, ((w + m) ^ 6)⁻¹
      = (2 * (Real.pi : ℂ) * I) ^ 6 / 120 * ∑' d : ℕ, (d : ℂ) ^ 5 * e w ^ d := by
  have h := EisensteinSeries.qExpansion_identity (k := 5) (by norm_num)
    (⟨w, hw⟩ : UpperHalfPlane)
  simp only [one_div, Nat.reduceAdd] at h
  simp only [e]
  rw [h, show ((Nat.factorial 5 : ℕ) : ℂ) = 120 from by norm_num [Nat.factorial]]
  ring

/-- The Basel-type sum over `ℤ` in weight `6`: `∑_{m : ℤ} m⁻⁶ = 2ζ(6) = 2π⁶/945`. -/
private lemma hasSum_int_inv_sixth :
    HasSum (fun m : ℤ ↦ ((m : ℂ) ^ 6)⁻¹) (2 * ((Real.pi : ℂ) ^ 6 / 945)) := by
  have hs : Summable fun m : ℤ ↦ ((m : ℂ) ^ 6)⁻¹ := by
    apply (summable_int_inv_sixth 0).congr
    intro m
    rw [zero_add]
  have h := hs.hasSum
  rwa [← two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (by norm_num) ⟨3, by norm_num⟩,
    show (((6 : ℕ) : ℂ)) = (6 : ℂ) from by norm_num, riemannZeta_six] at h

/-- The `q`-expansion of `g₃` (Silverman, *Advanced topics*, Theorem I.7.1):

`g₃(Λ_τ) = -(2πi)⁶/216 ⬝ (1 - 504s₅(q))`.

Proof: identical to `g₂_q_expansion`, with `g₃ = 140G₆`, the row sum identity
with `k = 5` (`sum_int_inv_sixth`), the divisor-sum rearrangement
`tsum_prod_pow_eq_tsum_sigma 5`, and `ζ(6) = π⁶/945` (`riemannZeta_six`). -/
theorem g₃_q_expansion (τ : ℂ) (hτ : 0 < τ.im) :
    (periodPair τ hτ.ne').g₃ =
      -(2 * (Real.pi : ℂ) * I) ^ 6 / 216 * (1 - 504 * sAn 5 (e τ)) := by
  have hq1 : ‖e τ‖ < 1 := norm_e_lt_one hτ
  have hcoe := periodPair_latticeEquiv_coe τ hτ.ne'
  -- Step 1: the lattice sum defining `G 6`, reindexed by `ℤ × ℤ`
  have hG : HasSum (fun l : (periodPair τ hτ.ne').lattice ↦ ((l : ℂ) ^ 6)⁻¹)
      ((periodPair τ hτ.ne').G 6) := by
    have h := (periodPair τ hτ.ne').hasSum_sumInvPow 0 (by norm_num : (2 : ℕ) < 6)
    rw [PeriodPair.sumInvPow_zero] at h
    simpa using h
  have h0 : HasSum (fun p : ℤ × ℤ ↦ (((p.1 : ℂ) * τ + p.2) ^ 6)⁻¹)
      ((periodPair τ hτ.ne').G 6) := by
    have h2 := ((periodPair τ hτ.ne').latticeEquivProd.symm.toEquiv.hasSum_iff).mpr hG
    have hfun : ((fun l : (periodPair τ hτ.ne').lattice ↦ ((l : ℂ) ^ 6)⁻¹)
        ∘ (periodPair τ hτ.ne').latticeEquivProd.symm.toEquiv)
        = fun p : ℤ × ℤ ↦ (((p.1 : ℂ) * τ + p.2) ^ 6)⁻¹ := by
      funext p
      simp only [Function.comp_apply, LinearEquiv.coe_toEquiv, hcoe p]
    rw [hfun] at h2
    exact h2
  -- Step 2: evaluate each row (the Lambert series is junk `0` in the row `n = 0`)
  have hrowval : ∀ n : ℤ,
      ∑' m : ℤ, (((n : ℂ) * τ + m) ^ 6)⁻¹
      = (2 * (Real.pi : ℂ) * I) ^ 6 / 120 * ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ n.natAbs) ^ d
        + (if n = 0 then 2 * ((Real.pi : ℂ) ^ 6 / 945) else 0) := by
    intro n
    rcases lt_trichotomy n 0 with hn | rfl | hn
    · have him' : (0 : ℝ) < (-((n : ℂ) * τ)).im := by
        have him : (-((n : ℂ) * τ)).im = -((n : ℝ) * τ.im) := by
          simp [Complex.mul_im]
        rw [him]
        have h2 : (n : ℝ) < 0 := by exact_mod_cast hn
        nlinarith
      have he : e (-((n : ℂ) * τ)) = e τ ^ n.natAbs := by
        rw [show -((n : ℂ) * τ) = (((-n : ℤ) : ℂ)) * τ from by push_cast; ring, e_intMul,
          show -n = (n.natAbs : ℤ) from by omega, zpow_natCast]
      rw [tsum_int_inv_sixth_neg, sum_int_inv_sixth _ him', he, if_neg hn.ne, add_zero]
    · have hB : ∑' m : ℤ, ((((0 : ℤ) : ℂ) * τ + m) ^ 6)⁻¹ = ∑' m : ℤ, ((m : ℂ) ^ 6)⁻¹ :=
        tsum_congr fun m ↦ by norm_num
      rw [hB, hasSum_int_inv_sixth.tsum_eq,
        show (∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ (0 : ℤ).natAbs) ^ d) = 0 from by
          simp only [Int.natAbs_zero, pow_zero, one_pow, mul_one]
          exact tsum_eq_zero_of_not_summable (not_summable_natCast_pow 5)]
      simp
    · have him' : (0 : ℝ) < ((n : ℂ) * τ).im := by
        have him : ((n : ℂ) * τ).im = (n : ℝ) * τ.im := by simp [Complex.mul_im]
        rw [him]
        have h2 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        nlinarith
      have he : e ((n : ℂ) * τ) = e τ ^ n.natAbs := by
        rw [show ((n : ℂ)) * τ = (((n.natAbs : ℤ) : ℂ)) * τ from by
            rw [show ((n.natAbs : ℤ)) = n from by omega],
          e_intMul, zpow_natCast]
      rw [sum_int_inv_sixth _ him', he, if_neg hn.ne', add_zero]
  -- Step 3: sum the rows (Fubini, which also gives summability of the row values)
  have hrowsHS : ∀ n : ℤ, HasSum (fun m : ℤ ↦ (((n : ℂ) * τ + m) ^ 6)⁻¹)
      ((2 * (Real.pi : ℂ) * I) ^ 6 / 120 * ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ n.natAbs) ^ d
        + (if n = 0 then 2 * ((Real.pi : ℂ) ^ 6 / 945) else 0)) := by
    intro n
    have h := (summable_int_inv_sixth ((n : ℂ) * τ)).hasSum
    rwa [hrowval n] at h
  have hG2 := h0.prod_fiberwise hrowsHS
  have hite : Summable fun n : ℤ ↦ (if n = 0 then 2 * ((Real.pi : ℂ) ^ 6 / 945) else 0) :=
    (hasSum_ite_eq (0 : ℤ) _).summable
  have hA : Summable fun n : ℤ ↦
      (2 * (Real.pi : ℂ) * I) ^ 6 / 120 * ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ n.natAbs) ^ d := by
    have h := hG2.summable.sub hite
    apply h.congr
    intro n
    ring
  -- Step 4: the divisor-sum rearrangement of the total Lambert contribution
  have hLsum : ∑' n : ℤ, ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ n.natAbs) ^ d
      = 2 * sAn 5 (e τ) := by
    have hC : ((2 * (Real.pi : ℂ) * I) ^ 6 / 120 : ℂ) ≠ 0 :=
      div_ne_zero (pow_ne_zero _ two_pi_I_ne_zero) (by norm_num)
    have hL : Summable fun n : ℤ ↦ ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ n.natAbs) ^ d := by
      have h := hA.mul_left ((2 * (Real.pi : ℂ) * I) ^ 6 / 120)⁻¹
      apply h.congr
      intro n
      rw [← mul_assoc, inv_mul_cancel₀ hC, one_mul]
    have hpos := (summable_int_iff_summable_nat_and_neg.mp hL).1
    have hnegall := (summable_int_iff_summable_nat_and_neg.mp hL).2
    have hneg : Summable fun n : ℕ ↦
        ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ (-((n : ℤ) + 1)).natAbs) ^ d := by
      have h := (summable_nat_add_iff 1).mpr hnegall
      apply h.congr
      intro n
      rw [show ((-((n + 1 : ℕ) : ℤ)).natAbs) = ((-((n : ℤ) + 1)).natAbs) from by omega]
    have hnatplain : ∑' n : ℕ, ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ n) ^ d = sAn 5 (e τ) := by
      rw [← tsum_pnat_of_zero (fun n : ℕ ↦ ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ n) ^ d) (by
        simp only [pow_zero, one_pow, mul_one]
        exact tsum_eq_zero_of_not_summable (not_summable_natCast_pow 5))]
      have hinner : ∀ n : ℕ+, ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ (n : ℕ)) ^ d
          = ∑' d : ℕ+, (d : ℂ) ^ 5 * e τ ^ ((n : ℕ) * (d : ℕ)) := by
        intro n
        rw [← tsum_pnat_of_zero (fun d : ℕ ↦ (d : ℂ) ^ 5 * (e τ ^ (n : ℕ)) ^ d) (by simp)]
        exact tsum_congr fun d ↦ by rw [pow_mul]
      rw [tsum_congr hinner, tsum_prod_pow_eq_tsum_sigma 5 hq1, sAn,
        tsum_pnat_of_zero (fun n : ℕ ↦ ((σ 5 n : ℕ) : ℂ) * e τ ^ n) (by simp)]
    rw [tsum_of_nat_of_neg_add_one
        (f := fun n : ℤ ↦ ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ n.natAbs) ^ d) hpos hneg,
      show (fun n : ℕ ↦ ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ ((n : ℤ)).natAbs) ^ d)
        = fun n : ℕ ↦ ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ n) ^ d from funext fun n ↦ by
          rw [show ((n : ℤ)).natAbs = n from by omega],
      show (fun n : ℕ ↦ ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ (-((n : ℤ) + 1)).natAbs) ^ d)
        = fun n : ℕ ↦ ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ (n + 1)) ^ d from funext fun n ↦ by
          rw [show (-((n : ℤ) + 1)).natAbs = n + 1 from by omega],
      ← tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ n) ^ d),
      tsum_pnat_of_zero (fun n : ℕ ↦ ∑' d : ℕ, (d : ℂ) ^ 5 * (e τ ^ n) ^ d) (by
        simp only [pow_zero, one_pow, mul_one]
        exact tsum_eq_zero_of_not_summable (not_summable_natCast_pow 5)),
      hnatplain]
    ring
  -- Step 5: assemble
  rw [PeriodPair.g₃, ← hG2.tsum_eq, Summable.tsum_add hA hite, tsum_mul_left, tsum_ite_eq,
    hLsum]
  have hI6 : (2 * (Real.pi : ℂ) * I) ^ 6 = -64 * (Real.pi : ℂ) ^ 6 := by
    have h1 : I ^ 6 = -1 := by
      rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Complex.I_sq]
      norm_num
    rw [mul_pow, mul_pow, h1]
    ring
  rw [hI6]
  ring

/-! ## The analytic Weierstrass equation -/

private theorem log_div_two_pi_I_im (w : ℂ) :
    ((Complex.log w) / (2 * (Real.pi : ℂ) * I)).im =
      -Real.log ‖w‖ / (2 * Real.pi) := by
  rw [Complex.div_im]
  simp [Complex.log_re, Complex.mul_re, Complex.mul_im, Complex.normSq]
  field_simp [Real.pi_ne_zero]

private theorem e_log_div_two_pi_I {w : ℂ} (hw : w ≠ 0) :
    e (Complex.log w / (2 * (Real.pi : ℂ) * I)) = w := by
  rw [e]
  have hmul : 2 * (Real.pi : ℂ) * I * (Complex.log w / (2 * (Real.pi : ℂ) * I)) =
      Complex.log w := by
    field_simp [two_pi_I_ne_zero]
  rw [hmul, Complex.exp_log hw]

private theorem notMem_lattice_of_im_between {τ z : ℂ}
    (hτ : 0 < τ.im) (hz0 : 0 < z.im) (hzt : z.im < τ.im) :
    z ∉ (periodPair τ hτ.ne').lattice := by
  intro hzmem
  rcases PeriodPair.mem_lattice.mp hzmem with ⟨m, n, hmn⟩
  have him : z.im = (m : ℝ) * τ.im := by
    have h := congrArg Complex.im hmn
    simp [periodPair, Complex.mul_im, Complex.add_im] at h
    linarith
  have hm_pos_real : 0 < (m : ℝ) := by
    have : 0 < (m : ℝ) * τ.im := by simpa [him] using hz0
    nlinarith
  have hm_lt_one_real : (m : ℝ) < 1 := by
    have : (m : ℝ) * τ.im < 1 * τ.im := by simpa [one_mul, him] using hzt
    nlinarith
  have hm_pos_int : 0 < m := by exact_mod_cast hm_pos_real
  have hm_lt_one_int : m < 1 := by exact_mod_cast hm_lt_one_real
  omega

private theorem analytic_weierstrass_algebra (x y s3 s5 c P D g2 g3 : ℂ) (hc : c ≠ 0)
    (hP : P = c ^ 2 * (1 / 12 + x))
    (hD : D = c ^ 3 * (x + 2 * y))
    (hg2 : g2 = c ^ 4 / 12 * (1 + 240 * s3))
    (hg3 : g3 = -c ^ 6 / 216 * (1 - 504 * s5))
    (hDE : D ^ 2 = 4 * P ^ 3 - g2 * P - g3) :
    y ^ 2 + x * y = x ^ 3 - 5 * s3 * x - (5 * s3 + 7 * s5) / 12 := by
  have hmain :
      c ^ 6 * ((x + 2 * y) ^ 2 -
        (4 * (1 / 12 + x) ^ 3 - (1 + 240 * s3) / 12 * (1 / 12 + x) +
          (1 - 504 * s5) / 216)) = 0 := by
    have h := hDE
    rw [hD, hP, hg2, hg3] at h
    ring_nf at h ⊢
    linear_combination h
  have hc6 : c ^ 6 ≠ 0 := pow_ne_zero 6 hc
  have hmain' :
      (x + 2 * y) ^ 2 =
        4 * (1 / 12 + x) ^ 3 - (1 + 240 * s3) / 12 * (1 / 12 + x) +
          (1 - 504 * s5) / 216 := by
    exact sub_eq_zero.mp (mul_eq_zero.mp hmain |>.resolve_left hc6)
  linear_combination hmain' / 4

private theorem analytic_weierstrass_of_exp {τ z u q : ℂ} (hτ : 0 < τ.im)
    (hz : 0 < z.im) (hzτ : z.im < τ.im)
    (hu : e z = u) (hq : e τ = q) :
    YAn u q ^ 2 + XAn u q * YAn u q =
      XAn u q ^ 3 - 5 * sAn 3 q * XAn u q - (5 * sAn 3 q + 7 * sAn 5 q) / 12 := by
  have hzΛ : z ∉ (periodPair τ hτ.ne').lattice := notMem_lattice_of_im_between hτ hz hzτ
  let c : ℂ := 2 * (Real.pi : ℂ) * I
  let L := periodPair τ hτ.ne'
  have hP : ℘[L] z = c ^ 2 * (1 / 12 + XAn u q) := by
    dsimp [L, c]
    simpa [hu, hq] using weierstrassP_q_expansion τ hτ z hz hzτ
  have hD : ℘'[L] z = c ^ 3 * (XAn u q + 2 * YAn u q) := by
    dsimp [L, c]
    simpa [hu, hq] using derivWeierstrassP_q_expansion τ hτ z hz hzτ
  have hg2 : L.g₂ = c ^ 4 / 12 * (1 + 240 * sAn 3 q) := by
    dsimp [L, c]
    simpa [hq] using g₂_q_expansion τ hτ
  have hg3 : L.g₃ = -c ^ 6 / 216 * (1 - 504 * sAn 5 q) := by
    dsimp [L, c]
    simpa [hq] using g₃_q_expansion τ hτ
  exact analytic_weierstrass_algebra (XAn u q) (YAn u q) (sAn 3 q) (sAn 5 q) c
    (℘[L] z) (℘'[L] z) L.g₂ L.g₃ (by simp [c]) hP hD hg2
    hg3 (PeriodPair.derivWeierstrassP_sq L z (by simpa [L] using hzΛ))

/-- The analytic form of the main theorem (Silverman, *Advanced topics*,
Theorem V.1.1(a)): for `0 < ‖q‖ < ‖u‖ < 1`,

`Yₐ² + XₐYₐ = Xₐ³ - 5s₃(q)Xₐ - (5s₃(q) + 7s₅(q))/12`.

Proof sketch: the hypotheses ensure `u ∉ qᶻ`, and we may choose `z`, `τ` with
`e z = u`, `e τ = q`, `0 < im z < im τ` (so `z ∉ Λ_τ`). By `weierstrassP_q_expansion`
and `derivWeierstrassP_q_expansion`, `℘(z) = (2πi)²(x + 1/12)` and
`℘'(z) = (2πi)³(x + 2y)` where `x = Xₐ(u, q)`, `y = Yₐ(u, q)`. Substitute these,
`g₂_q_expansion` and `g₃_q_expansion` into the differential equation
`℘'² = 4℘³ - g₂℘ - g₃` (`PeriodPair.derivWeierstrassP_sq`) and divide by `(2πi)⁶`:

`(x + 2y)² = 4(x + 1/12)³ - (1 + 240s₃)/12 ⬝ (x + 1/12) + (1 - 504s₅)/216`.

Expanding, the `x²` and `x/12` terms and the constants `4/12³ - 1/144 + 1/216 = 0`
cancel, and dividing by `4` gives the claim. -/
theorem analytic_weierstrass {u q : ℂ} (h0 : 0 < ‖q‖) (h1 : ‖q‖ < ‖u‖) (h2 : ‖u‖ < 1) :
    YAn u q ^ 2 + XAn u q * YAn u q =
      XAn u q ^ 3 - 5 * sAn 3 q * XAn u q - (5 * sAn 3 q + 7 * sAn 5 q) / 12 :=
  by
    let τ : ℂ := Complex.log q / (2 * (Real.pi : ℂ) * I)
    let z : ℂ := Complex.log u / (2 * (Real.pi : ℂ) * I)
    have hq_ne : q ≠ 0 := norm_pos_iff.mp h0
    have hu_pos : 0 < ‖u‖ := lt_trans h0 h1
    have hu_ne : u ≠ 0 := norm_pos_iff.mp hu_pos
    have hτ : 0 < τ.im := by
      dsimp [τ]
      rw [log_div_two_pi_I_im]
      have hq_lt_one : ‖q‖ < 1 := lt_trans h1 h2
      have hlogq : Real.log ‖q‖ < 0 := (Real.log_neg_iff h0).2 hq_lt_one
      exact div_pos (neg_pos.2 hlogq) (mul_pos (by norm_num) Real.pi_pos)
    have hz : 0 < z.im := by
      dsimp [z]
      rw [log_div_two_pi_I_im]
      have hlogu : Real.log ‖u‖ < 0 := (Real.log_neg_iff hu_pos).2 h2
      exact div_pos (neg_pos.2 hlogu) (mul_pos (by norm_num) Real.pi_pos)
    have hzt : z.im < τ.im := by
      dsimp [z, τ]
      rw [log_div_two_pi_I_im, log_div_two_pi_I_im]
      have hlog : Real.log ‖q‖ < Real.log ‖u‖ := Real.log_lt_log h0 h1
      have hneg : -Real.log ‖u‖ < -Real.log ‖q‖ := neg_lt_neg hlog
      exact div_lt_div_of_pos_right hneg (mul_pos (by norm_num) Real.pi_pos)
    have hu : e z = u := by
      dsimp [z]
      exact e_log_div_two_pi_I hu_ne
    have hq : e τ = q := by
      dsimp [τ]
      exact e_log_div_two_pi_I hq_ne
    exact analytic_weierstrass_of_exp hτ hz hzt hu hq

/-! ## Rearrangement: the analytic functions are the sums of the formal series

We now connect the analytic functions `Xₐ`, `Yₐ` with the formal power series
`TateCurve.X`, `TateCurve.Y`: evaluating the coefficients of the latter at `u` and
summing against powers of `q` recovers the former. -/

/-- Evaluation of a rational function in `ℚ(u)` at a complex number, with junk value `0`
at the (finitely many) poles. -/
def evalAt (u : ℂ) (r : RatFunc ℚ) : ℂ := r.eval (algebraMap ℚ ℂ) u

/-- For transcendental `u`, evaluation at `u` is a ring homomorphism
`ℚ(u) →+* ℂ` (there are no poles to produce junk values). -/
private noncomputable def evalAtHom (u : ℂ) (hu : Transcendental ℚ u) : RatFunc ℚ →+* ℂ where
  toFun r := (RatFunc.algEquivOfTranscendental u hu r : ℂ)
  map_one' := by simp
  map_mul' := by intro x y; simp
  map_zero' := by simp
  map_add' := by intro x y; simp

private theorem evalAtHom_apply (u : ℂ) (hu : Transcendental ℚ u) (r : RatFunc ℚ) :
    evalAtHom u hu r = evalAt u r := by
  change (RatFunc.algEquivOfTranscendental u hu r : ℂ) = evalAt u r
  rw [RatFunc.algEquivOfTranscendental_apply]
  simp [evalAt, RatFunc.eval, Polynomial.aeval_def]

private theorem evalAtHom_ratFuncX (u : ℂ) (hu : Transcendental ℚ u) :
    evalAtHom u hu RatFunc.X = u := by
  rw [evalAtHom_apply]
  unfold evalAt
  exact RatFunc.eval_X (K := ℚ) (f := algebraMap ℚ ℂ) (a := u)

/-! ### Transfer of `HasSum` between `ℕ` and `ℕ+`, and decomposition of `ℤ`-sums -/

private lemma hasSum_pnat_of_nat {f : ℕ → ℂ} {a : ℂ} (h : HasSum f a) (h0 : f 0 = 0) :
    HasSum (fun N : ℕ+ ↦ f (N : ℕ)) a := by
  have hs : Summable fun N : ℕ+ ↦ f (N : ℕ) :=
    h.summable.comp_injective PNat.coe_injective
  have h2 := hs.hasSum
  rwa [tsum_pnat_of_zero f h0, h.tsum_eq] at h2

private lemma hasSum_nat_of_pnat_add {f : ℕ → ℂ} {a : ℂ}
    (h : HasSum (fun N : ℕ+ ↦ f (N : ℕ)) a) : HasSum f (a + f 0) := by
  have hinj : Function.Injective Nat.succPNat := fun a b hab ↦ by
    simpa using congrArg PNat.natPred hab
  have hs1 : HasSum (fun n : ℕ ↦ f (n + 1)) a := by
    have h2 := (hinj.hasSum_iff (f := fun N : ℕ+ ↦ f (N : ℕ))
      (fun x hx ↦ absurd (Set.mem_range.mpr ⟨x.natPred, PNat.succPNat_natPred x⟩) hx)).mpr h
    apply h2.congr_fun
    intro n
    simp [Nat.succPNat_coe, Nat.succ_eq_add_one]
  have h3 := (hasSum_nat_add_iff (f := f) 1).mp hs1
  simpa using h3

/-- Splitting a summable `ℤ`-indexed sum into the term at `0` and the two tails. -/
private lemma tsum_int_decomp {f : ℤ → ℂ} (hf : Summable f) :
    ∑' n : ℤ, f n
      = f 0 + ∑' n : ℕ+, f ((n : ℕ) : ℤ) + ∑' n : ℕ+, f (-((n : ℕ) : ℤ)) := by
  have h1 : Summable fun n : ℕ ↦ f n := hf.comp_injective Nat.cast_injective
  have h2 : Summable fun n : ℕ ↦ f (-((n : ℤ) + 1)) := by
    have h3 := hf.comp_injective (fun a b hab ↦ (Int.negSucc.inj hab : a = b))
    apply h3.congr
    intro n
    simp only [Function.comp_apply, Int.negSucc_eq]
  rw [tsum_of_nat_of_neg_add_one h1 h2, ← tsum_zero_pnat_eq_tsum_nat h1,
    show (∑' n : ℕ, f (-((n : ℤ) + 1))) = ∑' n : ℕ+, f (-((n : ℕ) : ℤ)) from by
      rw [tsum_pnat_eq_tsum_succ (f := fun k : ℕ ↦ f (-(k : ℤ)))]
      apply tsum_congr
      intro n
      congr 1]
  norm_num

/-! ### Lambert series over `ℕ+` -/

private lemma hasSum_pnat_lambert₁ {v : ℂ} (hv : ‖v‖ < 1) :
    HasSum (fun m : ℕ+ ↦ ((m : ℕ) : ℂ) * v ^ (m : ℕ)) (v / (1 - v) ^ 2) :=
  hasSum_pnat_of_nat (hasSum_coe_mul_geometric_of_norm_lt_one hv) (by simp)

private lemma hasSum_pnat_lambert₂ {v : ℂ} (hv : ‖v‖ < 1) :
    HasSum (fun m : ℕ+ ↦ (((m : ℕ).choose 2 : ℕ) : ℂ) * v ^ (m : ℕ))
      (v ^ 2 / (1 - v) ^ 3) := by
  have h := hasSum_pnat_of_nat (hasSum_choose_two_mul_geometric hv) (by simp)
  rwa [show v ^ 2 * ((1 - v) ^ 3)⁻¹ = v ^ 2 / (1 - v) ^ 3 from by rw [div_eq_mul_inv]] at h

private lemma hasSum_pnat_lambert₂' {v : ℂ} (hv0 : v ≠ 0) (hv : ‖v‖ < 1) :
    HasSum (fun m : ℕ+ ↦ ((((m : ℕ) + 1).choose 2 : ℕ) : ℂ) * v ^ (m : ℕ))
      (v / (1 - v) ^ 3) := by
  have h1 : HasSum (fun m : ℕ ↦ ((((m + 1).choose 2 : ℕ)) : ℂ) * v ^ (m + 1))
      (v ^ 2 * ((1 - v) ^ 3)⁻¹) := by
    apply (hasSum_nat_add_iff (f := fun m : ℕ ↦ ((m.choose 2 : ℕ) : ℂ) * v ^ m) 1).mpr
    simpa using hasSum_choose_two_mul_geometric hv
  have h2 := h1.mul_left v⁻¹
  have heq : (fun m : ℕ ↦ v⁻¹ * (((((m + 1).choose 2 : ℕ)) : ℂ) * v ^ (m + 1))) =
      fun m : ℕ ↦ ((((m + 1).choose 2 : ℕ)) : ℂ) * v ^ m := by
    funext m
    calc v⁻¹ * (((((m + 1).choose 2 : ℕ)) : ℂ) * v ^ (m + 1))
        = ((((m + 1).choose 2 : ℕ)) : ℂ) * v ^ m * (v⁻¹ * v) := by
          rw [pow_succ]
          ring
      _ = ((((m + 1).choose 2 : ℕ)) : ℂ) * v ^ m := by
          rw [inv_mul_cancel₀ hv0, mul_one]
  rw [heq] at h2
  have h3 := hasSum_pnat_of_nat h2 (by simp)
  have hval : v⁻¹ * (v ^ 2 * ((1 - v) ^ 3)⁻¹) = v / (1 - v) ^ 3 := by
    rw [div_eq_mul_inv]
    calc v⁻¹ * (v ^ 2 * ((1 - v) ^ 3)⁻¹) = (v⁻¹ * v) * (v * ((1 - v) ^ 3)⁻¹) := by ring
      _ = v * ((1 - v) ^ 3)⁻¹ := by rw [inv_mul_cancel₀ hv0, one_mul]
  rwa [hval] at h3

/-- If `‖q‖ < 1` and `‖q * y‖ < 1` then `‖qⁿy‖ < 1` for every `n ≥ 1`. -/
private lemma norm_pow_mul_lt_one {q y : ℂ} (hq1 : ‖q‖ < 1) (hqy : ‖q * y‖ < 1) (n : ℕ+) :
    ‖q ^ (n : ℕ) * y‖ < 1 := by
  obtain ⟨k, hk⟩ : ∃ k, (n : ℕ) = k + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
  rw [hk, pow_succ, mul_assoc, norm_mul, norm_pow]
  calc ‖q‖ ^ k * ‖q * y‖ ≤ 1 * ‖q * y‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg q) hq1.le) (norm_nonneg _)
    _ = ‖q * y‖ := one_mul _
    _ < 1 := hqy

/-! ### Summability, Fubini, and divisor collection for the double series -/

private lemma cast_le_sq (m : ℕ+) : ‖((m : ℕ) : ℂ)‖ ≤ (((m : ℕ)) : ℝ) ^ 2 := by
  rw [Complex.norm_natCast]
  have h1 : (1 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.one_le_cast.mpr m.pos
  nlinarith

private lemma choose_two_le_sq (m : ℕ+) :
    ‖(((m : ℕ).choose 2 : ℕ) : ℂ)‖ ≤ (((m : ℕ)) : ℝ) ^ 2 := by
  rw [Complex.norm_natCast]
  exact_mod_cast Nat.choose_le_pow (m : ℕ) 2

private lemma choose_add_one_two_le_sq (m : ℕ+) :
    ‖((((m : ℕ) + 1).choose 2 : ℕ) : ℂ)‖ ≤ (((m : ℕ)) : ℝ) ^ 2 := by
  rw [Complex.norm_natCast]
  have hm : 1 ≤ (m : ℕ) := m.pos
  have h1 : ((m : ℕ) + 1).choose 2 ≤ (m : ℕ) ^ 2 := by
    have h2 : ((m : ℕ) + 1).choose 2 = ((m : ℕ) + 1) * (m : ℕ) / 2 := by
      rw [Nat.choose_two_right]
      simp
    rw [h2]
    have h3 : ((m : ℕ) + 1) * (m : ℕ) ≤ 2 * (m : ℕ) ^ 2 := by nlinarith
    omega
  exact_mod_cast h1

/-- Geometric-decay summability of the double series `∑ a(m)yᵐq^{nm}`, for any
coefficients of at most quadratic growth. -/
private lemma summable_coeff_prod {a : ℕ → ℂ} {x y : ℂ}
    (ha : ∀ m : ℕ+, ‖a (m : ℕ)‖ ≤ (((m : ℕ)) : ℝ) ^ 2) (hx : ‖x‖ < 1) (hxy : ‖x * y‖ < 1) :
    Summable fun p : ℕ+ × ℕ+ ↦ a (p.2 : ℕ) * y ^ (p.2 : ℕ) * x ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
  have hρ1 : max ‖x‖ ‖x * y‖ < 1 := max_lt hx hxy
  have hρ0 : (0 : ℝ) ≤ max ‖x‖ ‖x * y‖ := le_trans (norm_nonneg x) (le_max_left _ _)
  have hcomp : Summable fun p : ℕ+ × ℕ+ ↦
      (((p.2 : ℕ)) : ℝ) ^ 2 * (max ‖x‖ ‖x * y‖) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
    have h := summable_prod_mul_pow (𝕜 := ℝ) 2 (r := max ‖x‖ ‖x * y‖)
      (by rwa [Real.norm_of_nonneg hρ0])
    exact h
  apply Summable.of_norm_bounded hcomp
  intro p
  have hkey : ‖y‖ ^ (p.2 : ℕ) * ‖x‖ ^ ((p.1 : ℕ) * (p.2 : ℕ))
      ≤ (max ‖x‖ ‖x * y‖) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
    rcases le_or_gt ‖y‖ 1 with hy | hy
    · calc ‖y‖ ^ (p.2 : ℕ) * ‖x‖ ^ ((p.1 : ℕ) * (p.2 : ℕ))
          ≤ 1 * ‖x‖ ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg y) hy) (by positivity)
        _ = ‖x‖ ^ ((p.1 : ℕ) * (p.2 : ℕ)) := one_mul _
        _ ≤ (max ‖x‖ ‖x * y‖) ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
            pow_le_pow_left₀ (norm_nonneg x) (le_max_left _ _) _
    · have hym : ‖y‖ ^ (p.2 : ℕ) ≤ ‖y‖ ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
        pow_le_pow_right₀ hy.le (Nat.le_mul_of_pos_left _ p.1.pos)
      calc ‖y‖ ^ (p.2 : ℕ) * ‖x‖ ^ ((p.1 : ℕ) * (p.2 : ℕ))
          ≤ ‖y‖ ^ ((p.1 : ℕ) * (p.2 : ℕ)) * ‖x‖ ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
            mul_le_mul_of_nonneg_right hym (by positivity)
        _ = ‖x * y‖ ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
            rw [← mul_pow, mul_comm ‖y‖ ‖x‖, ← norm_mul]
        _ ≤ (max ‖x‖ ‖x * y‖) ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
            pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
  calc ‖a (p.2 : ℕ) * y ^ (p.2 : ℕ) * x ^ ((p.1 : ℕ) * (p.2 : ℕ))‖
      = ‖a (p.2 : ℕ)‖ * (‖y‖ ^ (p.2 : ℕ) * ‖x‖ ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
        rw [norm_mul, norm_mul, norm_pow, norm_pow, mul_assoc]
    _ ≤ (((p.2 : ℕ)) : ℝ) ^ 2 * (max ‖x‖ ‖x * y‖) ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
        mul_le_mul (ha p.2) hkey (by positivity) (by positivity)

/-- A summable double series over `ℕ+ × ℕ+` has sum the iterated sum of its rows. -/
private lemma hasSum_prod_pnat {T : ℕ+ × ℕ+ → ℂ} {F : ℕ+ → ℂ}
    (hsum : Summable T) (hfib : ∀ n : ℕ+, HasSum (fun m : ℕ+ ↦ T (n, m)) (F n)) :
    HasSum T (∑' n : ℕ+, F n) := by
  have h := hsum.hasSum
  rwa [hsum.tsum_prod' (fun n ↦ (hfib n).summable),
    tsum_congr fun n ↦ (hfib n).tsum_eq] at h

/-- Collecting a double series `∑_{n,m} g(m)x^{nm}` by powers of `x`: the coefficient
of `x^N` is the divisor sum `∑_{d ∣ N} g d`. -/
private lemma hasSum_divisor_collect (g : ℕ → ℂ) {x : ℂ} {S : ℂ}
    (hT : HasSum (fun p : ℕ+ × ℕ+ ↦ g (p.2 : ℕ) * x ^ ((p.1 : ℕ) * (p.2 : ℕ))) S) :
    HasSum (fun N : ℕ+ ↦ (∑ d ∈ (N : ℕ).divisors, g d) * x ^ (N : ℕ)) S := by
  have h1 := (sigmaAntidiagonalEquivProd.hasSum_iff).mpr hT
  apply h1.sigma
  intro N
  have h2 := hasSum_fintype (fun c : ((N : ℕ).divisorsAntidiagonal) ↦
    (g c.1.2 * x ^ (c.1.1 * c.1.2) : ℂ))
  have hval : (∑ c : ((N : ℕ).divisorsAntidiagonal), (g c.1.2 * x ^ (c.1.1 * c.1.2) : ℂ))
      = (∑ d ∈ (N : ℕ).divisors, g d) * x ^ (N : ℕ) := by
    rw [Finset.univ_eq_attach,
      Finset.sum_attach ((N : ℕ).divisorsAntidiagonal)
        (fun p ↦ (g p.2 * x ^ (p.1 * p.2) : ℂ)),
      show (∑ p ∈ (N : ℕ).divisorsAntidiagonal, (g p.2 * x ^ (p.1 * p.2) : ℂ))
          = ∑ p ∈ (N : ℕ).divisorsAntidiagonal, (g p.2 * x ^ (N : ℕ) : ℂ) from
        Finset.sum_congr rfl fun p hp ↦ by rw [(Nat.mem_divisorsAntidiagonal.mp hp).1],
      ← Finset.sum_mul, Nat.sum_divisorsAntidiagonal' (f := fun _ d ↦ (g d : ℂ))]
  rw [hval] at h2
  apply h2.congr_fun
  intro c
  simp only [Function.comp_apply, sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk,
    divisorsAntidiagonalFactors, PNat.mk_coe]

/-- The `y = 1` double series, with the divisor sums already recognised as `s₁`. -/
private lemma hasSum_prodC {q : ℂ} (hq1 : ‖q‖ < 1) :
    HasSum (fun p : ℕ+ × ℕ+ ↦
        ((p.2 : ℕ) : ℂ) * (1 : ℂ) ^ (p.2 : ℕ) * q ^ ((p.1 : ℕ) * (p.2 : ℕ)))
      (sAn 1 q) := by
  have hq1' : ‖q * 1‖ < 1 := by simpa using hq1
  have hfib : ∀ n : ℕ+, HasSum
      (fun m : ℕ+ ↦ ((m : ℕ) : ℂ) * (1 : ℂ) ^ (m : ℕ) * q ^ ((n : ℕ) * (m : ℕ)))
      (q ^ (n : ℕ) / (1 - q ^ (n : ℕ)) ^ 2) := by
    intro n
    have hv : ‖q ^ (n : ℕ)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg q) hq1 n.pos.ne'
    apply (hasSum_pnat_lambert₁ hv).congr_fun
    intro m
    rw [one_pow, mul_one, pow_mul]
  have h := hasSum_prod_pnat (summable_coeff_prod cast_le_sq hq1 hq1') hfib
  rwa [show (∑' n : ℕ+, q ^ (n : ℕ) / (1 - q ^ (n : ℕ)) ^ 2) = sAn 1 q from by
    rw [tsum_pnat_of_zero (fun k : ℕ ↦ q ^ k / (1 - q ^ k) ^ 2) (by simp),
      tsum_V_nat hq1]] at h

/-! ### The coefficients of `X` and `Y`, evaluated at a transcendental point -/

private theorem coeff_X_zero :
    (PowerSeries.coeff 0) X = RatFunc.X / (1 - RatFunc.X) ^ 2 := by
  simp [X]

private theorem coeff_X_of_ne {N : ℕ} (hN : N ≠ 0) :
    (PowerSeries.coeff N) X
      = ∑ d ∈ N.divisors, (d : RatFunc ℚ) * (RatFunc.X ^ d + RatFunc.X⁻¹ ^ d - 2) := by
  simp [X, PowerSeries.coeff_C, hN]

private theorem evalAt_coeff_X_zero {u : ℂ} (hu : Transcendental ℚ u) :
    evalAt u ((PowerSeries.coeff 0) X) = u / (1 - u) ^ 2 := by
  rw [← evalAtHom_apply u hu, coeff_X_zero]
  simp only [map_div₀, map_pow, map_sub, map_one, evalAtHom_ratFuncX u hu]

private theorem evalAt_coeff_X {u : ℂ} (hu : Transcendental ℚ u) {N : ℕ} (hN : N ≠ 0) :
    evalAt u ((PowerSeries.coeff N) X)
      = ∑ d ∈ N.divisors, (d : ℂ) * (u ^ d + u⁻¹ ^ d - 2) := by
  rw [← evalAtHom_apply u hu, coeff_X_of_ne hN, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [map_mul, map_natCast, map_sub, map_add, map_pow, map_inv₀, map_ofNat,
    evalAtHom_ratFuncX u hu]

private theorem coeff_Y_zero :
    (PowerSeries.coeff 0) Y = RatFunc.X ^ 2 / (1 - RatFunc.X) ^ 3 := by
  simp [Y]

private theorem coeff_Y_of_ne {N : ℕ} (hN : N ≠ 0) :
    (PowerSeries.coeff N) Y
      = ∑ d ∈ N.divisors, ((d.choose 2 : RatFunc ℚ) * RatFunc.X ^ d
          - ((d + 1).choose 2 : RatFunc ℚ) * RatFunc.X⁻¹ ^ d + (d : RatFunc ℚ)) := by
  simp [Y, PowerSeries.coeff_C, hN]

private theorem evalAt_coeff_Y_zero {u : ℂ} (hu : Transcendental ℚ u) :
    evalAt u ((PowerSeries.coeff 0) Y) = u ^ 2 / (1 - u) ^ 3 := by
  rw [← evalAtHom_apply u hu, coeff_Y_zero]
  simp only [map_div₀, map_pow, map_sub, map_one, evalAtHom_ratFuncX u hu]

private theorem evalAt_coeff_Y {u : ℂ} (hu : Transcendental ℚ u) {N : ℕ} (hN : N ≠ 0) :
    evalAt u ((PowerSeries.coeff N) Y)
      = ∑ d ∈ N.divisors, (((d.choose 2 : ℕ) : ℂ) * u ^ d
          - (((d + 1).choose 2 : ℕ) : ℂ) * u⁻¹ ^ d + (d : ℂ)) := by
  rw [← evalAtHom_apply u hu, coeff_Y_of_ne hN, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [map_add, map_sub, map_mul, map_natCast, map_pow, map_inv₀,
    evalAtHom_ratFuncX u hu]

/-- Rearrangement for `X` (extracted from Silverman's proof of *Advanced topics*,
Theorem V.3.1(c)): for `0 < ‖q‖ < ‖u‖ < 1` with `u` transcendental (so that evaluation
of coefficients at `u` is a ring homomorphism), the coefficients of the formal series
`TateCurve.X` evaluated at `u` sum to `Xₐ(u, q)`.

Proof: expand each term of `Xₐ`: for `n ≥ 1`,
`qⁿu/(1 - qⁿu)² = ∑_{m ≥ 1} m qⁿᵐuᵐ` (geometric series, `‖qⁿu‖ < 1`); for `n ≤ -1`
with `N = -n`, the rational-function identity `v/(1-v)² = v⁻¹/(1-v⁻¹)²` gives
`qⁿu/(1 - qⁿu)² = ∑_{m ≥ 1} m qᴺᵐu⁻ᵐ` (`‖qᴺu⁻¹‖ < 1`); and
`-2s₁(q) = -2∑_N (∑_{d ∣ N} d) qᴺ`. All double series converge absolutely
(`summable_coeff_prod`), so they may be collected by powers of `q`
(`hasSum_divisor_collect`), and the coefficient of `qᴺ` is exactly
`∑_{d ∣ N} d(uᵈ + u⁻ᵈ - 2)`. -/
theorem hasSum_X_eval {u q : ℂ} (hu : Transcendental ℚ u) (h0 : 0 < ‖q‖)
    (h1 : ‖q‖ < ‖u‖) (h2 : ‖u‖ < 1) :
    HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) X) * q ^ n) (XAn u q) := by
  have hu0 : u ≠ 0 := norm_pos_iff.mp (h0.trans h1)
  have hq0 : q ≠ 0 := norm_pos_iff.mp h0
  have hq1 : ‖q‖ < 1 := h1.trans h2
  have hqu : ‖q * u‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg q, norm_nonneg u]
  have hqui : ‖q * u⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    exact (div_lt_one (norm_pos_iff.mpr hu0)).mpr h1
  -- the two `u`-dependent Lambert double series
  have hA : HasSum
      (fun p : ℕ+ × ℕ+ ↦ ((p.2 : ℕ) : ℂ) * u ^ (p.2 : ℕ) * q ^ ((p.1 : ℕ) * (p.2 : ℕ)))
      (∑' n : ℕ+, q ^ (n : ℕ) * u / (1 - q ^ (n : ℕ) * u) ^ 2) := by
    apply hasSum_prod_pnat (summable_coeff_prod
      (a := fun m : ℕ ↦ ((m : ℕ) : ℂ)) (x := q) (y := u) cast_le_sq hq1 hqu)
    intro n
    apply (hasSum_pnat_lambert₁ (norm_pow_mul_lt_one hq1 hqu n)).congr_fun
    intro m
    ring
  have hB : HasSum
      (fun p : ℕ+ × ℕ+ ↦ ((p.2 : ℕ) : ℂ) * u⁻¹ ^ (p.2 : ℕ) * q ^ ((p.1 : ℕ) * (p.2 : ℕ)))
      (∑' n : ℕ+, q ^ (n : ℕ) * u⁻¹ / (1 - q ^ (n : ℕ) * u⁻¹) ^ 2) := by
    apply hasSum_prod_pnat (summable_coeff_prod
      (a := fun m : ℕ ↦ ((m : ℕ) : ℂ)) (x := q) (y := u⁻¹) cast_le_sq hq1 hqui)
    intro n
    apply (hasSum_pnat_lambert₁ (norm_pow_mul_lt_one hq1 hqui n)).congr_fun
    intro m
    ring
  have hC := hasSum_prodC hq1
  -- combine and collect by divisors
  have hcomb : HasSum
      (fun p : ℕ+ × ℕ+ ↦
        ((p.2 : ℕ) : ℂ) * (u ^ (p.2 : ℕ) + u⁻¹ ^ (p.2 : ℕ) - 2)
          * q ^ ((p.1 : ℕ) * (p.2 : ℕ)))
      ((∑' n : ℕ+, q ^ (n : ℕ) * u / (1 - q ^ (n : ℕ) * u) ^ 2)
        + (∑' n : ℕ+, q ^ (n : ℕ) * u⁻¹ / (1 - q ^ (n : ℕ) * u⁻¹) ^ 2)
        - 2 * sAn 1 q) := by
    apply ((hA.add hB).sub (hC.mul_left 2)).congr_fun
    intro p
    ring
  have hdiv := hasSum_divisor_collect (fun d : ℕ ↦ (d : ℂ) * (u ^ d + u⁻¹ ^ d - 2)) hcomb
  have htarget : HasSum
      (fun N : ℕ+ ↦ evalAt u ((PowerSeries.coeff ((N : ℕ))) X) * q ^ (N : ℕ))
      ((∑' n : ℕ+, q ^ (n : ℕ) * u / (1 - q ^ (n : ℕ) * u) ^ 2)
        + (∑' n : ℕ+, q ^ (n : ℕ) * u⁻¹ / (1 - q ^ (n : ℕ) * u⁻¹) ^ 2)
        - 2 * sAn 1 q) := by
    apply hdiv.congr_fun
    intro N
    rw [evalAt_coeff_X hu N.pos.ne']
  have hfull := hasSum_nat_of_pnat_add
    (f := fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) X) * q ^ n) htarget
  -- identify the value with `XAn u q`
  have hposEq : ∀ n : ℕ+,
      q ^ (((n : ℕ) : ℤ)) * u / (1 - q ^ (((n : ℕ) : ℤ)) * u) ^ 2
        = q ^ (n : ℕ) * u / (1 - q ^ (n : ℕ) * u) ^ 2 := by
    intro n
    rw [zpow_natCast]
  have hnegEq : ∀ n : ℕ+,
      q ^ (-((n : ℕ) : ℤ)) * u / (1 - q ^ (-((n : ℕ) : ℤ)) * u) ^ 2
        = q ^ (n : ℕ) * u⁻¹ / (1 - q ^ (n : ℕ) * u⁻¹) ^ 2 := by
    intro n
    have hv : (q ^ (n : ℕ) * u⁻¹)⁻¹ = q ^ (-((n : ℕ) : ℤ)) * u := by
      rw [mul_inv, inv_inv, zpow_neg, zpow_natCast]
    rw [← inv_div_one_sub_inv_sq
      (mul_ne_zero (pow_ne_zero _ hq0) (inv_ne_zero hu0)), hv]
  convert hfull using 1
  rw [XAn, tsum_int_decomp (summable_V hq0 h1 h2),
    show q ^ (0 : ℤ) * u / (1 - q ^ (0 : ℤ) * u) ^ 2 = u / (1 - u) ^ 2 from by
      rw [zpow_zero, one_mul],
    tsum_congr hposEq, tsum_congr hnegEq, evalAt_coeff_X_zero hu, pow_zero, mul_one]
  ring

/-- Rearrangement for `Y`: for `0 < ‖q‖ < ‖u‖ < 1` with `u` transcendental, the
coefficients of the formal series `TateCurve.Y` evaluated at `u` sum to `Yₐ(u, q)`.

Proof: as for `hasSum_X_eval`, using `v²/(1-v)³ = ∑_{m ≥ 1} (m choose 2) vᵐ` for
the rows `n ≥ 1`, the rational-function identity `v²/(1-v)³ = -v⁻¹/(1-v⁻¹)³` together
with `v/(1-v)³ = ∑_{m ≥ 1} ((m+1) choose 2) vᵐ` for the rows `n ≤ -1`, and
`s₁(q) = ∑_N (∑_{d ∣ N} d) qᴺ` for the correction term. -/
theorem hasSum_Y_eval {u q : ℂ} (hu : Transcendental ℚ u) (h0 : 0 < ‖q‖)
    (h1 : ‖q‖ < ‖u‖) (h2 : ‖u‖ < 1) :
    HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) Y) * q ^ n) (YAn u q) := by
  have hu0 : u ≠ 0 := norm_pos_iff.mp (h0.trans h1)
  have hq0 : q ≠ 0 := norm_pos_iff.mp h0
  have hq1 : ‖q‖ < 1 := h1.trans h2
  have hqu : ‖q * u‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg q, norm_nonneg u]
  have hqui : ‖q * u⁻¹‖ < 1 := by
    rw [norm_mul, norm_inv, ← div_eq_mul_inv]
    exact (div_lt_one (norm_pos_iff.mpr hu0)).mpr h1
  have hA : HasSum
      (fun p : ℕ+ × ℕ+ ↦ (((p.2 : ℕ).choose 2 : ℕ) : ℂ) * u ^ (p.2 : ℕ)
        * q ^ ((p.1 : ℕ) * (p.2 : ℕ)))
      (∑' n : ℕ+, (q ^ (n : ℕ) * u) ^ 2 / (1 - q ^ (n : ℕ) * u) ^ 3) := by
    apply hasSum_prod_pnat (summable_coeff_prod
      (a := fun m : ℕ ↦ ((m.choose 2 : ℕ) : ℂ)) (x := q) (y := u) choose_two_le_sq hq1 hqu)
    intro n
    apply (hasSum_pnat_lambert₂ (norm_pow_mul_lt_one hq1 hqu n)).congr_fun
    intro m
    ring
  have hB : HasSum
      (fun p : ℕ+ × ℕ+ ↦ ((((p.2 : ℕ) + 1).choose 2 : ℕ) : ℂ) * u⁻¹ ^ (p.2 : ℕ)
        * q ^ ((p.1 : ℕ) * (p.2 : ℕ)))
      (∑' n : ℕ+, q ^ (n : ℕ) * u⁻¹ / (1 - q ^ (n : ℕ) * u⁻¹) ^ 3) := by
    apply hasSum_prod_pnat (summable_coeff_prod
      (a := fun m : ℕ ↦ (((m + 1).choose 2 : ℕ) : ℂ)) (x := q) (y := u⁻¹)
      choose_add_one_two_le_sq hq1 hqui)
    intro n
    apply (hasSum_pnat_lambert₂'
      (mul_ne_zero (pow_ne_zero _ hq0) (inv_ne_zero hu0))
      (norm_pow_mul_lt_one hq1 hqui n)).congr_fun
    intro m
    ring
  have hC := hasSum_prodC hq1
  have hcomb : HasSum
      (fun p : ℕ+ × ℕ+ ↦
        ((((p.2 : ℕ).choose 2 : ℕ) : ℂ) * u ^ (p.2 : ℕ)
          - ((((p.2 : ℕ) + 1).choose 2 : ℕ) : ℂ) * u⁻¹ ^ (p.2 : ℕ) + ((p.2 : ℕ) : ℂ))
          * q ^ ((p.1 : ℕ) * (p.2 : ℕ)))
      ((∑' n : ℕ+, (q ^ (n : ℕ) * u) ^ 2 / (1 - q ^ (n : ℕ) * u) ^ 3)
        - (∑' n : ℕ+, q ^ (n : ℕ) * u⁻¹ / (1 - q ^ (n : ℕ) * u⁻¹) ^ 3)
        + sAn 1 q) := by
    apply ((hA.sub hB).add hC).congr_fun
    intro p
    ring
  have hdiv := hasSum_divisor_collect
    (fun d : ℕ ↦ ((d.choose 2 : ℕ) : ℂ) * u ^ d
      - (((d + 1).choose 2 : ℕ) : ℂ) * u⁻¹ ^ d + (d : ℂ)) hcomb
  have htarget : HasSum
      (fun N : ℕ+ ↦ evalAt u ((PowerSeries.coeff ((N : ℕ))) Y) * q ^ (N : ℕ))
      ((∑' n : ℕ+, (q ^ (n : ℕ) * u) ^ 2 / (1 - q ^ (n : ℕ) * u) ^ 3)
        - (∑' n : ℕ+, q ^ (n : ℕ) * u⁻¹ / (1 - q ^ (n : ℕ) * u⁻¹) ^ 3)
        + sAn 1 q) := by
    apply hdiv.congr_fun
    intro N
    rw [evalAt_coeff_Y hu N.pos.ne']
  have hfull := hasSum_nat_of_pnat_add
    (f := fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) Y) * q ^ n) htarget
  have hposEq : ∀ n : ℕ+,
      (q ^ (((n : ℕ) : ℤ)) * u) ^ 2 / (1 - q ^ (((n : ℕ) : ℤ)) * u) ^ 3
        = (q ^ (n : ℕ) * u) ^ 2 / (1 - q ^ (n : ℕ) * u) ^ 3 := by
    intro n
    rw [zpow_natCast]
  have hnegEq : ∀ n : ℕ+,
      (q ^ (-((n : ℕ) : ℤ)) * u) ^ 2 / (1 - q ^ (-((n : ℕ) : ℤ)) * u) ^ 3
        = -(q ^ (n : ℕ) * u⁻¹ / (1 - q ^ (n : ℕ) * u⁻¹) ^ 3) := by
    intro n
    have hv : (q ^ (n : ℕ) * u⁻¹)⁻¹ = q ^ (-((n : ℕ) : ℤ)) * u := by
      rw [mul_inv, inv_inv, zpow_neg, zpow_natCast]
    have h := inv_sq_div_one_sub_inv_cube (v := q ^ (n : ℕ) * u⁻¹)
      (mul_ne_zero (pow_ne_zero _ hq0) (inv_ne_zero hu0))
    rw [hv] at h
    exact h
  convert hfull using 1
  rw [YAn, tsum_int_decomp (summable_V₂ hq0 h1 h2),
    show (q ^ (0 : ℤ) * u) ^ 2 / (1 - q ^ (0 : ℤ) * u) ^ 3 = u ^ 2 / (1 - u) ^ 3 from by
      rw [zpow_zero, one_mul],
    tsum_congr hposEq, tsum_congr hnegEq, tsum_neg, evalAt_coeff_Y_zero hu, pow_zero,
    mul_one]
  ring

private theorem evalAt_ratCast (u : ℂ) (r : ℚ) : evalAt u (r : RatFunc ℚ) = (r : ℂ) := by
  simpa [evalAt] using
    (RatFunc.eval_algebraMap (K := ℚ) (L := ℂ) (f := algebraMap ℚ ℂ) (a := u) (S := ℚ) r)

private theorem summable_sAn_terms (k : ℕ) {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun n : ℕ ↦ (σ k n : ℂ) * q ^ n) := by
  refine Summable.of_norm_bounded (summable_norm_pow_mul_geometric_of_norm_lt_one (k + 1) hq) ?_
  intro n
  calc
    ‖(σ k n : ℂ) * q ^ n‖ = (σ k n : ℝ) * ‖q ^ n‖ := by simp
    _ ≤ (n ^ (k + 1) : ℝ) * ‖q ^ n‖ := by
      gcongr
      exact_mod_cast ArithmeticFunction.sigma_le_pow_succ k n
    _ = ‖(n : ℂ) ^ (k + 1) * q ^ n‖ := by simp

private theorem ofNat_powerSeries_eq_C (m : ℕ) [m.AtLeastTwo] :
    (OfNat.ofNat m : (RatFunc ℚ)⟦X⟧) = PowerSeries.C (OfNat.ofNat m : RatFunc ℚ) := by
  rw [PowerSeries.C_eq_algebraMap]
  exact (map_ofNat (algebraMap (RatFunc ℚ) ((RatFunc ℚ)⟦X⟧)) m).symm

private theorem coeff_a₆ (n : ℕ) :
    ((PowerSeries.coeff n) a₆) =
      (-(5 * (σ 3 n : ℚ) + 7 * (σ 5 n : ℚ)) / 12 : RatFunc ℚ) := by
  have h7 : (7 : (RatFunc ℚ)⟦X⟧) = PowerSeries.C (7 : RatFunc ℚ) :=
    ofNat_powerSeries_eq_C 7
  have h5 : (5 : (RatFunc ℚ)⟦X⟧) = PowerSeries.C (5 : RatFunc ℚ) :=
    ofNat_powerSeries_eq_C 5
  simp only [a₆, s, h7, h5, PowerSeries.coeff_smul, PowerSeries.coeff_mk,
    PowerSeries.coeff_C_mul, map_neg, map_add]
  norm_num
  ring_nf

private theorem evalAt_coeff_a₆ (u : ℂ) (n : ℕ) :
    evalAt u ((PowerSeries.coeff n) a₆) =
      (-(5 * (σ 3 n : ℂ) + 7 * (σ 5 n : ℂ)) / 12) := by
  rw [coeff_a₆]
  simpa using evalAt_ratCast u (-(5 * (σ 3 n : ℚ) + 7 * (σ 5 n : ℚ)) / 12)

private theorem coeff_a₄ (n : ℕ) :
    ((PowerSeries.coeff n) a₄) = (-5 * (σ 3 n : ℚ) : RatFunc ℚ) := by
  have hneg5 : (-5 : (RatFunc ℚ)⟦X⟧) = PowerSeries.C (-5 : RatFunc ℚ) := by
    rw [PowerSeries.C_eq_algebraMap]
    exact (map_intCast (algebraMap (RatFunc ℚ) ((RatFunc ℚ)⟦X⟧)) (-5)).symm
  simp only [a₄, s, hneg5, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  norm_num

private theorem evalAt_coeff_a₄ (u : ℂ) (n : ℕ) :
    evalAt u ((PowerSeries.coeff n) a₄) = -5 * (σ 3 n : ℂ) := by
  rw [coeff_a₄]
  simpa using evalAt_ratCast u (-5 * (σ 3 n : ℚ))

/-- The coefficients of the formal series `a₄` evaluated at any `u` sum to `-5s₃(q)`
for `‖q‖ < 1`. (The coefficients are constants, so this is just the convergence of
`∑ σ₃(n)qⁿ`.) -/
theorem hasSum_a₄_eval (u : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) a₄) * q ^ n) (-5 * sAn 3 q) :=
  by
    have h3 : HasSum (fun n : ℕ ↦ (σ 3 n : ℂ) * q ^ n) (sAn 3 q) :=
      (summable_sAn_terms 3 hq).hasSum
    have hlin : HasSum (fun n : ℕ ↦ -5 * ((σ 3 n : ℂ) * q ^ n)) (-5 * sAn 3 q) :=
      h3.mul_left (-5)
    refine HasSum.congr_fun hlin ?_
    intro n
    rw [evalAt_coeff_a₄]
    ring_nf

/-- The coefficients of the formal series `a₆` evaluated at any `u` sum to
`-(5s₃(q) + 7s₅(q))/12` for `‖q‖ < 1`. -/
theorem hasSum_a₆_eval (u : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) a₆) * q ^ n)
      (-(5 * sAn 3 q + 7 * sAn 5 q) / 12) :=
  by
    have h3 : HasSum (fun n : ℕ ↦ (σ 3 n : ℂ) * q ^ n) (sAn 3 q) :=
      (summable_sAn_terms 3 hq).hasSum
    have h5 : HasSum (fun n : ℕ ↦ (σ 5 n : ℂ) * q ^ n) (sAn 5 q) :=
      (summable_sAn_terms 5 hq).hasSum
    have hlin : HasSum
        (fun n : ℕ ↦ (-(5 * ((σ 3 n : ℂ) * q ^ n) + 7 * ((σ 5 n : ℂ) * q ^ n))) / 12)
        (-(5 * sAn 3 q + 7 * sAn 5 q) / 12) := by
      have h3' : HasSum (fun n : ℕ ↦ 5 * ((σ 3 n : ℂ) * q ^ n)) (5 * sAn 3 q) :=
        h3.mul_left 5
      have h5' : HasSum (fun n : ℕ ↦ 7 * ((σ 5 n : ℂ) * q ^ n)) (7 * sAn 5 q) :=
        h5.mul_left 7
      simpa using ((h3'.add h5').neg.div_const (12 : ℂ))
    refine HasSum.congr_fun hlin ?_
    intro n
    rw [evalAt_coeff_a₆]
    ring

/-! ## Descent to the formal power series ring -/

private theorem coeffs_eq_zero_of_hasSum_punctured (c : ℕ → ℂ) (r : ℝ) (hr : 0 < r)
    (h : ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < r → HasSum (fun n : ℕ ↦ c n * q ^ n) 0) :
    c = 0 := by
  let f : ℂ → ℂ := fun z ↦ if z = 0 then c 0 else 0
  let p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ c
  have hp : HasFPowerSeriesAt f p 0 := by
    rw [hasFPowerSeriesAt_iff]
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    by_cases hz0 : z = 0
    · simpa [f, p, hz0, FormalMultilinearSeries.coeff_ofScalars] using
        (HasSum.hasSum_at_zero (𝕜 := ℂ) c)
    · have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
      have hzlt : ‖z‖ < r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      simpa [f, p, hz0, FormalMultilinearSeries.coeff_ofScalars, mul_comm] using
        h z hzpos hzlt
  have han : AnalyticAt ℂ f 0 := ⟨p, hp⟩
  haveI : Filter.NeBot (𝓝[≠] (0 : ℂ)) := PerfectSpace.not_isolated (0 : ℂ)
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0 := by
    exact (eventually_nhdsWithin_of_forall (s := ({0}ᶜ : Set ℂ)) (a := (0 : ℂ)) (by
      intro z hz
      have hz0 : z ≠ 0 := by simpa using hz
      simp [f, hz0])).frequently
  have hev : f =ᶠ[𝓝 (0 : ℂ)] 0 := by
    simpa [Filter.EventuallyEq] using han.frequently_zero_iff_eventually_zero.mp hfreq
  have hpzero : p = 0 := hp.eq_zero_of_eventually hev
  have hc_zero : FormalMultilinearSeries.ofScalars ℂ c = 0 := by
    simpa [p] using hpzero
  exact (FormalMultilinearSeries.ofScalars_series_eq_zero (E := ℂ) (c := c)).mp hc_zero

private theorem ratFunc_eq_zero_of_evalAt_eq_zero_on_infinite (r : RatFunc ℚ) (S : Set ℂ)
    (hS : S.Infinite) (h : ∀ u ∈ S, evalAt u r = 0) :
    r = 0 := by
  classical
  let D : Set ℂ := {u | Polynomial.eval₂ (algebraMap ℚ ℂ) u (RatFunc.denom r) = 0}
  have hDfin : D.Finite := by
    have hden_map : (RatFunc.denom r).map (algebraMap ℚ ℂ) ≠ 0 := by
      exact (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective ℚ ℂ)).mpr
        (RatFunc.denom_ne_zero r)
    simpa [D, Polynomial.IsRoot, Polynomial.eval_map] using
      (Polynomial.finite_setOf_isRoot
        (p := (RatFunc.denom r).map (algebraMap ℚ ℂ)) hden_map)
  have hSdiff : (S \ D).Infinite := hS.sdiff hDfin
  let N : Set ℂ := {u | Polynomial.eval₂ (algebraMap ℚ ℂ) u (RatFunc.num r) = 0}
  have hSdiff_subset : S \ D ⊆ N := by
    intro u hu
    have huS : u ∈ S := hu.1
    have huD : u ∉ D := hu.2
    have hden : Polynomial.eval₂ (algebraMap ℚ ℂ) u (RatFunc.denom r) ≠ 0 := by
      simpa [D] using huD
    have heval : Polynomial.eval₂ (algebraMap ℚ ℂ) u (RatFunc.num r) /
        Polynomial.eval₂ (algebraMap ℚ ℂ) u (RatFunc.denom r) = 0 := by
      simpa [evalAt, RatFunc.eval] using h u huS
    exact (div_eq_zero_iff.mp heval).resolve_right hden
  have hNinf : N.Infinite := hSdiff.mono hSdiff_subset
  have hroots_inf :
      ({u : ℂ | Polynomial.IsRoot ((RatFunc.num r).map (algebraMap ℚ ℂ)) u}).Infinite := by
    simpa [N, Polynomial.IsRoot, Polynomial.eval_map] using hNinf
  have hnum_map_zero : (RatFunc.num r).map (algebraMap ℚ ℂ) = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot _ hroots_inf
  have hnum_zero : RatFunc.num r = 0 := by
    exact (Polynomial.map_eq_zero_iff (FaithfulSMul.algebraMap_injective ℚ ℂ)).mp
      hnum_map_zero
  exact RatFunc.num_eq_zero_iff.mp hnum_zero

/-- The descent lemma: a formal power series `F ∈ ℚ(u)⟦q⟧` vanishes provided that, for
infinitely many `u₀ : ℂ`, the evaluated series `∑ₙ Fₙ(u₀)q₀ⁿ` converges with sum `0`
for all sufficiently small nonzero `q₀`.

Proof sketch: fix `u₀`. The function `q₀ ↦ ∑ₙ Fₙ(u₀)q₀ⁿ` is analytic on `‖q₀‖ < r`
(a power series converging pointwise on a disc is analytic there) and vanishes on the
punctured disc, hence at `0` by continuity; by uniqueness of power series coefficients,
`Fₙ(u₀) = 0` for all `n`. So for each `n` the rational function `Fₙ` vanishes at
infinitely many points of `ℂ` (junk values at the finitely many poles of `Fₙ` do not
matter, as removing them leaves an infinite set), hence its numerator has infinitely
many roots and `Fₙ = 0` (`Polynomial.eq_zero_of_infinite_isRoot`). -/
theorem eq_zero_of_forall_hasSum_zero (F : (RatFunc ℚ)⟦X⟧) (S : Set ℂ) (hS : S.Infinite)
    (h : ∀ u ∈ S, ∃ r > 0, ∀ q : ℂ, 0 < ‖q‖ → ‖q‖ < r →
      HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) F) * q ^ n) 0) :
    F = 0 :=
  by
    ext n
    apply ratFunc_eq_zero_of_evalAt_eq_zero_on_infinite _ S hS
    intro u hu
    rcases h u hu with ⟨r, hr, hsum⟩
    have hc := coeffs_eq_zero_of_hasSum_punctured
      (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) F)) r hr hsum
    simpa using congrFun hc n

private theorem hasSum_evalAt_add {u q : ℂ} (hu : Transcendental ℚ u)
    {φ ψ : (RatFunc ℚ)⟦X⟧} {A B : ℂ}
    (hφ : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) φ) * q ^ n) A)
    (hψ : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) ψ) * q ^ n) B) :
    HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) (φ + ψ)) * q ^ n) (A + B) := by
  let E := evalAtHom u hu
  have hφE : HasSum (fun n : ℕ ↦ E ((PowerSeries.coeff n) φ) * q ^ n) A := by
    simpa [E, evalAtHom_apply] using hφ
  have hψE : HasSum (fun n : ℕ ↦ E ((PowerSeries.coeff n) ψ) * q ^ n) B := by
    simpa [E, evalAtHom_apply] using hψ
  refine HasSum.congr_fun (hφE.add hψE) ?_
  intro n
  rw [← evalAtHom_apply u hu ((PowerSeries.coeff n) (φ + ψ))]
  simp [E, map_add, add_mul]

private theorem hasSum_evalAt_neg {u q : ℂ} (hu : Transcendental ℚ u)
    {φ : (RatFunc ℚ)⟦X⟧} {A : ℂ}
    (hφ : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) φ) * q ^ n) A) :
    HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) (-φ)) * q ^ n) (-A) := by
  let E := evalAtHom u hu
  have hφE : HasSum (fun n : ℕ ↦ E ((PowerSeries.coeff n) φ) * q ^ n) A := by
    simpa [E, evalAtHom_apply] using hφ
  refine HasSum.congr_fun hφE.neg ?_
  intro n
  rw [← evalAtHom_apply u hu ((PowerSeries.coeff n) (-φ))]
  simp [E]

private theorem hasSum_evalAt_sub {u q : ℂ} (hu : Transcendental ℚ u)
    {φ ψ : (RatFunc ℚ)⟦X⟧} {A B : ℂ}
    (hφ : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) φ) * q ^ n) A)
    (hψ : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) ψ) * q ^ n) B) :
    HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) (φ - ψ)) * q ^ n) (A - B) := by
  simpa [sub_eq_add_neg] using hasSum_evalAt_add hu hφ (hasSum_evalAt_neg hu hψ)

private theorem hasSum_evalAt_mul {u q : ℂ} (hu : Transcendental ℚ u)
    {φ ψ : (RatFunc ℚ)⟦X⟧} {A B : ℂ}
    (hφ : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) φ) * q ^ n) A)
    (hψ : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) ψ) * q ^ n) B) :
    HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) (φ * ψ)) * q ^ n) (A * B) := by
  let E := evalAtHom u hu
  let f : ℕ → ℂ := fun n ↦ E ((PowerSeries.coeff n) φ) * q ^ n
  let g : ℕ → ℂ := fun n ↦ E ((PowerSeries.coeff n) ψ) * q ^ n
  have hφE : HasSum f A := by
    simpa [f, E, evalAtHom_apply] using hφ
  have hψE : HasSum g B := by
    simpa [g, E, evalAtHom_apply] using hψ
  have hprod₀ : HasSum (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1), f k * g (n - k))
      ((∑' n : ℕ, f n) * ∑' n : ℕ, g n) :=
    hasSum_sum_range_mul_of_summable_norm hφE.summable.norm hψE.summable.norm
  have hprod : HasSum (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1), f k * g (n - k))
      (A * B) :=
    by simpa [hφE.tsum_eq, hψE.tsum_eq] using hprod₀
  refine HasSum.congr_fun hprod ?_
  intro n
  symm
  rw [PowerSeries.coeff_mul]
  rw [← evalAtHom_apply u hu
    (∑ p ∈ Finset.antidiagonal n,
      ((PowerSeries.coeff p.1) φ) * ((PowerSeries.coeff p.2) ψ))]
  change ∑ k ∈ Finset.range (n + 1), f k * g (n - k) =
    E (∑ p ∈ Finset.antidiagonal n,
      ((PowerSeries.coeff p.1) φ) * ((PowerSeries.coeff p.2) ψ)) * q ^ n
  have hant :
      (∑ p ∈ Finset.antidiagonal n,
        ((PowerSeries.coeff p.1) φ) * ((PowerSeries.coeff p.2) ψ)) =
        ∑ k ∈ Finset.range (n + 1),
          ((PowerSeries.coeff k) φ) * ((PowerSeries.coeff (n - k)) ψ) := by
    simpa using
      (Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun k l ↦ ((PowerSeries.coeff k) φ) * ((PowerSeries.coeff l) ψ)) n)
  rw [hant]
  calc
    ∑ k ∈ Finset.range (n + 1), f k * g (n - k)
        = ∑ k ∈ Finset.range (n + 1),
            E (((PowerSeries.coeff k) φ) * ((PowerSeries.coeff (n - k)) ψ)) * q ^ n := by
          refine Finset.sum_congr rfl ?_
          intro k hk
          have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
          simp only [f, g]
          rw [map_mul]
          calc
            (E ((PowerSeries.coeff k) φ) * q ^ k) *
                (E ((PowerSeries.coeff (n - k)) ψ) * q ^ (n - k)) =
                E ((PowerSeries.coeff k) φ) * E ((PowerSeries.coeff (n - k)) ψ) *
                  (q ^ k * q ^ (n - k)) := by ring
            _ = E ((PowerSeries.coeff k) φ) * E ((PowerSeries.coeff (n - k)) ψ) *
                q ^ (k + (n - k)) := by
              rw [← pow_add]
            _ = E ((PowerSeries.coeff k) φ) * E ((PowerSeries.coeff (n - k)) ψ) *
                q ^ n := by
              rw [Nat.add_sub_of_le hk_le]
    _ = E (∑ k ∈ Finset.range (n + 1),
          ((PowerSeries.coeff k) φ) * ((PowerSeries.coeff (n - k)) ψ)) * q ^ n := by
          simp [map_sum, Finset.sum_mul]

private theorem transcendental_punctured_unit_disk_infinite :
    ({u : ℂ | Transcendental ℚ u ∧ 0 < ‖u‖ ∧ ‖u‖ < 1} : Set ℂ).Infinite := by
  classical
  let S : Set ℂ := {u : ℂ | Transcendental ℚ u ∧ 0 < ‖u‖ ∧ ‖u‖ < 1}
  let I : Set ℝ := Set.Ioo (0 : ℝ) 1
  let J : Set ℂ := ((fun x : ℝ ↦ (x : ℂ)) '' I)
  have hI_not_countable : ¬ I.Countable := by
    change ¬ ((Set.Ioo (0 : ℝ) 1).Countable)
    intro h
    have hc : Cardinal.continuum ≤ Cardinal.aleph0 := by
      rw [← Cardinal.mk_Ioo_real (by norm_num : (0 : ℝ) < 1)]
      exact Cardinal.le_aleph0_iff_set_countable.mpr h
    exact (not_le_of_gt Cardinal.aleph0_lt_continuum) hc
  have hJ_not_countable : ¬ J.Countable := by
    intro hJ
    have hinj : Set.InjOn (fun x : ℝ ↦ (x : ℂ)) I := by
      intro x _ y _ hxy
      exact Complex.ofReal_injective hxy
    exact hI_not_countable
      (Set.countable_of_injective_of_countable_image hinj (by simpa [J] using hJ))
  have hAlg_countable : ({u : ℂ | IsAlgebraic ℚ u} : Set ℂ).Countable := by
    haveI : Countable (AddMonoidAlgebra ℚ ℕ) := inferInstanceAs (Countable (ℕ →₀ ℚ))
    haveI : Countable (Polynomial ℚ) := Polynomial.toFinsupp_injective.countable
    have hsub : {u : ℂ | IsAlgebraic ℚ u}
        ⊆ ⋃ p : {p : Polynomial ℚ // p ≠ 0}, (p : Polynomial ℚ).rootSet ℂ := by
      intro x hx
      obtain ⟨p, hp0, hpx⟩ := hx
      exact Set.mem_iUnion.mpr ⟨⟨p, hp0⟩, (Polynomial.mem_rootSet).mpr ⟨hp0, hpx⟩⟩
    exact Set.Countable.mono hsub
      (Set.countable_iUnion fun p ↦ ((p : Polynomial ℚ).rootSet_finite ℂ).countable)
  by_contra hSfin
  have hS_countable : S.Countable := (Set.not_infinite.mp hSfin).countable
  have hJ_subset : J ⊆ S ∪ {u : ℂ | IsAlgebraic ℚ u} := by
    intro z hz
    rcases hz with ⟨x, hxI, rfl⟩
    by_cases htr : Transcendental ℚ (x : ℂ)
    · left
      have hx0 : 0 < x := hxI.1
      have hx1 : x < 1 := hxI.2
      have hnorm : ‖(x : ℂ)‖ = x := by
        exact (RCLike.norm_ofReal (K := ℂ) x).trans (abs_of_pos hx0)
      have hnorm_pos : 0 < ‖(x : ℂ)‖ := by
        rw [hnorm]
        exact hx0
      have hnorm_lt : ‖(x : ℂ)‖ < 1 := by
        rw [hnorm]
        exact hx1
      exact ⟨htr, hnorm_pos, hnorm_lt⟩
    · right
      simpa [Transcendental] using htr
  have hJ_countable : J.Countable :=
    Set.Countable.mono hJ_subset (hS_countable.union hAlg_countable)
  exact hJ_not_countable hJ_countable

/-!
## Assembly

Proof sketch for `TateCurve.weierstrass_equation` from the above: apply
`eq_zero_of_forall_hasSum_zero` to `F = Y² + XY - X³ - a₄X - a₆` with
`S = (1/2, 1) ⊆ ℝ ⊆ ℂ` and `r = u₀` for each `u₀ ∈ S`. Since evaluation of
coefficients is multiplicative on Cauchy products, and all the evaluated series
converge absolutely for `‖q‖ < u₀` (by the coefficient bounds in `hasSum_X_eval`,
`hasSum_Y_eval` and Mertens-type results on Cauchy products of absolutely convergent
series, e.g. `summable_norm_sum_mul_antidiagonal_of_summable_norm`), the sum of the
evaluated series of `F` at `q₀` with `0 < ‖q₀‖ < u₀` equals

`y² + xy - x³ + 5s₃(q₀)x + (5s₃(q₀) + 7s₅(q₀))/12`

where `x = Xₐ(u₀, q₀)`, `y = Yₐ(u₀, q₀)` (by `hasSum_X_eval`, `hasSum_Y_eval`,
`hasSum_a₄_eval`, `hasSum_a₆_eval`), and this is `0` by `analytic_weierstrass`.
Hence `F = 0`, i.e. `Y² + XY = X³ + a₄X + a₆`.
-/

end Blueprint

open Blueprint in
/-- The point `(X(u,q), Y(u,q))` satisfies the Weierstrass equation
`y² + xy = x³ + a₄x + a₆` of the Tate curve, as an identity in `ℚ(u)⟦q⟧`.
-/
theorem weierstrass_equation : Y ^ 2 + X * Y = X ^ 3 + a₄ * X + a₆ :=
  by
    let F : (RatFunc ℚ)⟦X⟧ := Y ^ 2 + X * Y - (X ^ 3 + a₄ * X + a₆)
    have hF : F = 0 := by
      refine eq_zero_of_forall_hasSum_zero F
        ({u : ℂ | Transcendental ℚ u ∧ 0 < ‖u‖ ∧ ‖u‖ < 1})
        transcendental_punctured_unit_disk_infinite ?_
      intro u hu
      refine ⟨‖u‖, hu.2.1, ?_⟩
      intro q hq0 hq_lt_u
      have hu_tr : Transcendental ℚ u := hu.1
      have hu_lt_one : ‖u‖ < 1 := hu.2.2
      have hq_lt_one : ‖q‖ < 1 := lt_trans hq_lt_u hu_lt_one
      have hX : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) X) * q ^ n)
          (XAn u q) :=
        hasSum_X_eval hu_tr hq0 hq_lt_u hu_lt_one
      have hY : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) Y) * q ^ n)
          (YAn u q) :=
        hasSum_Y_eval hu_tr hq0 hq_lt_u hu_lt_one
      have ha₄ : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) a₄) * q ^ n)
          (-5 * sAn 3 q) :=
        hasSum_a₄_eval u hq_lt_one
      have ha₆ : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) a₆) * q ^ n)
          (-(5 * sAn 3 q + 7 * sAn 5 q) / 12) :=
        hasSum_a₆_eval u hq_lt_one
      have hY2 : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) (Y ^ 2)) * q ^ n)
          (YAn u q ^ 2) := by
        simpa [pow_two] using hasSum_evalAt_mul hu_tr hY hY
      have hXY : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) (X * Y)) * q ^ n)
          (XAn u q * YAn u q) :=
        hasSum_evalAt_mul hu_tr hX hY
      have hleft : HasSum
          (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) (Y ^ 2 + X * Y)) * q ^ n)
          (YAn u q ^ 2 + XAn u q * YAn u q) :=
        hasSum_evalAt_add hu_tr hY2 hXY
      have hX2 : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) (X ^ 2)) * q ^ n)
          (XAn u q ^ 2) := by
        simpa [pow_two] using hasSum_evalAt_mul hu_tr hX hX
      have hX3 : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) (X ^ 3)) * q ^ n)
          (XAn u q ^ 3) := by
        simpa [pow_succ, pow_two, mul_assoc] using hasSum_evalAt_mul hu_tr hX2 hX
      have ha₄X : HasSum
          (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) (a₄ * X)) * q ^ n)
          ((-5 * sAn 3 q) * XAn u q) :=
        hasSum_evalAt_mul hu_tr ha₄ hX
      have hright₀ : HasSum
          (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) (X ^ 3 + a₄ * X)) * q ^ n)
          (XAn u q ^ 3 + (-5 * sAn 3 q) * XAn u q) :=
        hasSum_evalAt_add hu_tr hX3 ha₄X
      have hright : HasSum
          (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) (X ^ 3 + a₄ * X + a₆)) * q ^ n)
          (XAn u q ^ 3 + (-5 * sAn 3 q) * XAn u q +
            (-(5 * sAn 3 q + 7 * sAn 5 q) / 12)) :=
        hasSum_evalAt_add hu_tr hright₀ ha₆
      have hdiff : HasSum (fun n : ℕ ↦ evalAt u ((PowerSeries.coeff n) F) * q ^ n)
          ((YAn u q ^ 2 + XAn u q * YAn u q) -
            (XAn u q ^ 3 + (-5 * sAn 3 q) * XAn u q +
              (-(5 * sAn 3 q + 7 * sAn 5 q) / 12))) := by
        simpa [F] using hasSum_evalAt_sub hu_tr hleft hright
      convert hdiff using 1
      · rw [analytic_weierstrass hq0 hq_lt_u hu_lt_one]
        ring
    have hmain : Y ^ 2 + X * Y - (X ^ 3 + a₄ * X + a₆) = 0 := by
      simpa [F] using hF
    exact sub_eq_zero.mp hmain

end TateCurve
