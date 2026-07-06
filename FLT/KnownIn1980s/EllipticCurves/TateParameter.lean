/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Instances.Int

/-!

# The Tate parameter power series

Let `k` be a field complete with respect to a rank 1 nonarchimedean valuation. The
`j`-invariant of the Tate curve `E_q` is `j(q) = q⁻¹ + 744 + 196884q + ⋯`, and Silverman,
*Advanced topics in the arithmetic of elliptic curves*, Lemma V.5.2, states that
`q ↦ j(q)` is a bijection from `{q : 0 < |q| < 1}` onto `{j : |j| > 1}`, whose inverse is
given by a power series `q = j⁻¹ + 744j⁻² + 750420j⁻³ + ⋯ ∈ ℤ⟦j⁻¹⟧` with *integer*
coefficients. This file constructs that inverse map `WeierstrassCurve.tateParameter`,
as honest data (no appeal to choice), in three steps.

## Step 1: the formal series `1/j ∈ ℤ⟦q⟧` (`TateCurve.jInv`)

`j(q)` itself is not a power series (it has the pole `q⁻¹`), but its reciprocal is:
`1/j = Δ(q)/c₄(q)³` where `Δ(q) = q∏_{n≥1}(1 - qⁿ)²⁴` and `c₄(q) = 1 + 240∑σ₃(n)qⁿ`,
both in `ℤ⟦q⟧`. The infinite product is a `tprod` in the `X`-adic topology on `ℤ⟦X⟧`
(each coefficient is a finite computation, `PowerSeries.WithPiTopology`), and `c₄³` has
constant coefficient `1`, so it is invertible over `ℤ` (`PowerSeries.invOfUnit` — no
denominators appear). The result is `jInv = q - 744q² + 356652q³ - ⋯`, with
`jInv(0) = 0` and linear coefficient `1`.

## Step 2: formal compositional inversion (`TateCurve.jInvReverse`)

A power series `f = u·X + a₂X² + ⋯` with zero constant term and invertible linear
coefficient has a unique compositional inverse `g` with `g(f) = f(g) = X`, with
coefficients in the same ring. Mathlib provides this as `PowerSeries.substInv` (with the
composition identities `subst_substInv_right` and `subst_substInv_left`), constructed by
the coefficient recursion `bₙ₊₁ = -⅟u·[Xⁿ⁺¹](f ∘ (∑_{i ≤ n} bᵢXⁱ))`. Note that the only
division ever performed is by the linear coefficient `u` — which for `jInv` is `1` — and
*not* by `n`, as the closed Lagrange inversion formula `bₙ = (1/n)·[Xⁿ⁻¹](X/f)ⁿ` would
require; division by `n` would be illegal in the intended targets of the coefficients
(`k` may be `𝔽_q((t))`, where `char k ∣ n` happens). Integrality of the coefficients of
the inverse `j`-series — which Silverman remarks on in V.5.2 — is thereby true *by
construction*.

`TateCurve.jInvReverse := substInv jInv = X + 744X² + 750420X³ + ⋯` is the series we are
after.

## Step 3: evaluation (`WeierstrassCurve.tateParameter`)

Finally `tateParameter j := ∑_{n≥1} bₙ (j⁻¹)ⁿ`, a `tsum` in `k`. For `|j| > 1` the terms
have norm at most `|j⁻¹|ⁿ → 0` (nonarchimedean bound: the coefficients are integers!), so
the series converges by completeness of `k`; for `|j| ≤ 1` the `tsum` takes junk values,
consistently with the other series in Tate's theory (`tateA₄`, `tateX`, …). Only a field
and a topology are needed to *state* the definition, so it applies verbatim in the rank 1
generality (`ℂ_p`, completed maximal unramified extensions, …).

The characterising properties — `tateJ (tateParameter j) = j` for `|j| > 1` and
`tateParameter (tateJ q) = q` for `0 < |q| < 1` (the two halves of Silverman V.5.2) — are
stated in `FLT.KnownIn1980s.EllipticCurves.TateCurve`, where `tateJ` lives. Their proofs
will combine the formal identity `subst_jInvReverse` of Step 2 with the usual
formal-to-convergent bridge (evaluation of a formal `subst` identity at a point where all
series converge, as in `TateCurve.weierstrass_equation` and its analytic counterparts).

Because the coefficients are universal integers, `tateParameter` commutes with every
continuous morphism of topological fields; this is what makes the Tate parameter functorial
(`WeierstrassCurve.q_baseChange`) with no uniqueness argument at the level of `k`.
-/

@[expose] public section

open scoped ArithmeticFunction.sigma -- `σ k n` notation for the sum of the `k`th powers
                                     -- of the divisors of `n`
open scoped PowerSeries.WithPiTopology -- the `X`-adic (coefficientwise) topology on
                                       -- `ℤ⟦X⟧`, giving meaning to `∏'`
open scoped Topology -- `𝓝` notation for neighbourhood filters

namespace TateCurve

open PowerSeries

/-! ### Step 1: the formal series `1/j ∈ ℤ⟦q⟧` -/

/-- The formal series `sₖ(q) = ∑_{n≥1} σₖ(n)qⁿ ∈ ℤ⟦q⟧` (integer-coefficient version of
`TateCurve.s`; recall `σₖ(0) = 0`). -/
noncomputable def sInt (k : ℕ) : ℤ⟦X⟧ :=
  .mk fun n ↦ (σ k n : ℤ)

/-- The formal `c₄`-series `c₄(q) = 1 + 240s₃(q) = 1 + 240q + 2160q² + ⋯ ∈ ℤ⟦q⟧` of the
Tate curve: the `q`-expansion of the Eisenstein series `E₄`. -/
noncomputable def c₄Formal : ℤ⟦X⟧ :=
  1 + 240 * sInt 3

/-- The formal discriminant `Δ(q) = q∏_{n≥1}(1 - qⁿ)²⁴ ∈ ℤ⟦q⟧` of the Tate curve: the
`q`-expansion of the modular discriminant, `∑ τ(n)qⁿ` with `τ` Ramanujan's tau. The
product is a `tprod` in the `X`-adic topology, multipliable by
`PowerSeries.WithPiTopology.multipliable_one_sub_X_pow`. -/
noncomputable def ΔFormal : ℤ⟦X⟧ :=
  X * (∏' n : ℕ, (1 - X ^ (n + 1))) ^ 24

/-- The formal series `1/j = Δ(q)/c₄(q)³ = q - 744q² + 356652q³ - ⋯ ∈ ℤ⟦q⟧`: the
reciprocal of the `j`-invariant of the Tate curve. Since `c₄³` has constant coefficient
`1` its inverse `PowerSeries.invOfUnit (c₄Formal ^ 3) 1` has integer coefficients: no
denominators are introduced. -/
noncomputable def jInv : ℤ⟦X⟧ :=
  ΔFormal * invOfUnit (c₄Formal ^ 3) 1

@[simp]
theorem constantCoeff_jInv : constantCoeff jInv = 0 := by
  simp [jInv, ΔFormal]

theorem coeff_one_jInv : coeff 1 jInv = 1 := by
  -- the constant coefficient of the product `∏(1 - qⁿ)²⁴` is `1`: `constantCoeff` is a
  -- continuous ring homomorphism for the `X`-adic topology, so commutes with `∏'`
  have h : constantCoeff (∏' n : ℕ, ((1 : ℤ⟦X⟧) - X ^ (n + 1))) = 1 := by
    rw [(WithPiTopology.multipliable_one_sub_X_pow ℤ).map_tprod _
      (WithPiTopology.continuous_constantCoeff ℤ)]
    simp
  -- `jInv = X * (unit of ℤ⟦X⟧)`, so its linear coefficient is the constant coefficient
  -- of that unit
  have key : coeff 1 jInv =
      constantCoeff ((∏' n : ℕ, ((1 : ℤ⟦X⟧) - X ^ (n + 1))) ^ 24 *
        invOfUnit (c₄Formal ^ 3) 1) := by
    simp only [jInv, ΔFormal, mul_assoc]
    exact (coeff_succ_X_mul 0 _).trans (coeff_zero_eq_constantCoeff_apply _)
  rw [key, map_mul, map_pow, h, constantCoeff_invOfUnit]
  simp

/-! ### Step 2: formal compositional inversion -/

/-- The linear coefficient of `jInv` is (invertibly) `1`: the hypothesis under which
mathlib's compositional inversion `PowerSeries.substInv` applies. -/
noncomputable instance : Invertible (coeff 1 jInv) :=
  invertibleOne.copy _ coeff_one_jInv

/-- The formal inverse `j`-series
`ψ = X + 744X² + 750420X³ + 872769632X⁴ + ⋯ ∈ ℤ⟦X⟧`: the compositional inverse
`PowerSeries.substInv` of `jInv`, so that formally `q = ψ(1/j)` (Silverman, ATAEC
V.5.2 — the integrality of the coefficients is by construction, see the module
docstring). -/
noncomputable def jInvReverse : ℤ⟦X⟧ :=
  substInv jInv

/-- The defining property of `jInvReverse`: `ψ(jInv(q)) = q` as formal power series. This
is the identity from which both halves of Silverman V.5.2 follow by evaluation. -/
theorem subst_jInvReverse : PowerSeries.subst jInv jInvReverse = X :=
  subst_substInv_left jInv constantCoeff_jInv

/-- The composition in the other order: `jInv(ψ(w)) = w` as formal power series. -/
theorem jInv_subst_jInvReverse : PowerSeries.subst jInvReverse jInv = X :=
  subst_substInv_right jInv constantCoeff_jInv

/-! ### The formal Weierstrass coefficients and the discriminant identity

Not needed for `tateParameter` itself, but housed here with the other formal series: the
`a₄`- and `a₆`-series of the Tate curve over `ℤ`, and Jacobi's discriminant formula
(Silverman, ATAEC V.1.1(b)) saying that the Weierstrass discriminant of
`y² + xy = x³ + a₄(q)x + a₆(q)` is `ΔFormal = q∏(1-qⁿ)²⁴`. This formal identity is the
hard input to `WeierstrassCurve.tateΔ_eq_prod`; it is equivalent to
`E₄³ - E₆² = 1728·η²⁴`.
-/

/-- The formal `a₄`-series `a₄(q) = -5s₃(q) ∈ ℤ⟦q⟧` of the Tate curve: the integral
version of `WeierstrassCurve.tateA₄`. -/
noncomputable def a₄Formal : ℤ⟦X⟧ :=
  -5 * sInt 3

/-- The formal `a₆`-series `a₆(q) = -(5s₃(q) + 7s₅(q))/12 ∈ ℤ⟦q⟧` of the Tate curve: the
integral version of `WeierstrassCurve.tateA₆`. The division is exact, since
`12 ∣ 5d³ + 7d⁵` for every `d`. -/
noncomputable def a₆Formal : ℤ⟦X⟧ :=
  .mk fun n ↦ -((5 * σ 3 n + 7 * σ 5 n : ℤ) / 12)

@[simp]
theorem coeff_a₄Formal (n : ℕ) : coeff n a₄Formal = -5 * σ 3 n := by
  simp only [a₄Formal, sInt, neg_mul, map_neg,
    show ((5 : ℤ⟦X⟧)) = C (5 : ℤ) from (map_ofNat (C : ℤ →+* ℤ⟦X⟧) 5).symm,
    coeff_C_mul, coeff_mk]

@[simp]
theorem coeff_a₆Formal (n : ℕ) :
    coeff n a₆Formal = -((5 * σ 3 n + 7 * σ 5 n : ℤ) / 12) := by
  simp only [a₆Formal, coeff_mk]

/-- Jacobi's discriminant formula (the formal heart of Silverman, ATAEC V.1.1(b)): the
Weierstrass discriminant `a₄² - a₆ - 64a₄³ + 72a₄a₆ - 432a₆²` of the Tate curve
`y² + xy = x³ + a₄(q)x + a₆(q)` equals `q∏_{n≥1}(1 - qⁿ)²⁴`, as an identity in `ℤ⟦q⟧`.
This is equivalent to the classical `E₄³ - E₆² = 1728Δ` together with the `η²⁴` product
expansion of `Δ`. Provable from mathlib's `discriminant_eq_q_prod` (the analytic identity
on the upper half-plane) by descending to formal power series coefficientwise, following
the same blueprint as `TateCurve.weierstrass_equation`. -/
theorem ΔFormal_eq :
    ΔFormal = a₄Formal ^ 2 - a₆Formal - C 64 * a₄Formal ^ 3 +
      C 72 * (a₄Formal * a₆Formal) - C 432 * a₆Formal ^ 2 :=
  sorry

/-! ### Coefficients of the formal `η`-product

The formal infinite product `∏(1 - Xⁿ⁺¹)` is determined coefficientwise by its finite
partial products: the `m`-th coefficient is already computed by the partial product over
`Finset.range (m + 1)`, since every further factor is `≡ 1 mod X^(m+1)`. These lemmas
feed the evaluation of `ΔFormal` on the open unit disc of a nonarchimedean local field
(`TateCurve.evalInt_ΔFormal`).
-/

/-- A finite product of factors `1 - X^(n+1)` with all indices `n ≥ m` is
`1 + O(X^(m+1))`. -/
theorem exists_prod_one_sub_X_pow_eq_one_add {m : ℕ} :
    ∀ {u : Finset ℕ}, (∀ n ∈ u, m ≤ n) →
      ∃ B : ℤ⟦X⟧, ∏ n ∈ u, ((1 : ℤ⟦X⟧) - X ^ (n + 1)) = 1 + X ^ (m + 1) * B := by
  intro u
  induction u using Finset.cons_induction with
  | empty => exact fun _ ↦ ⟨0, by simp⟩
  | cons a u ha ih =>
    intro hu
    obtain ⟨B, hB⟩ := ih fun n hn ↦ hu n (Finset.mem_cons.mpr (Or.inr hn))
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (hu a (Finset.mem_cons_self ..))
    exact ⟨B - X ^ d * (1 + X ^ (m + 1) * B), by rw [Finset.prod_cons, hB]; ring⟩

/-- Enlarging a partial product of `∏(1 - Xⁿ⁺¹)` beyond `Finset.range m` does not change
the `m`-th coefficient. -/
theorem coeff_prod_one_sub_X_pow_stable {m : ℕ} {s t : Finset ℕ}
    (hs : Finset.range m ⊆ s) (hst : s ⊆ t) :
    coeff m (∏ n ∈ t, ((1 : ℤ⟦X⟧) - X ^ (n + 1))) =
      coeff m (∏ n ∈ s, ((1 : ℤ⟦X⟧) - X ^ (n + 1))) := by
  obtain ⟨B, hB⟩ := exists_prod_one_sub_X_pow_eq_one_add (m := m) (u := t \ s)
    fun n hn ↦ by
      by_contra hlt
      exact (Finset.mem_sdiff.mp hn).2 (hs (Finset.mem_range.mpr (lt_of_not_ge hlt)))
  rw [← Finset.prod_sdiff hst, hB, add_mul, one_mul, map_add,
    show X ^ (m + 1) * B * ∏ n ∈ s, ((1 : ℤ⟦X⟧) - X ^ (n + 1)) =
      (B * ∏ n ∈ s, ((1 : ℤ⟦X⟧) - X ^ (n + 1))) * X ^ (m + 1) from by ring,
    PowerSeries.coeff_mul_X_pow']
  simp

/-- The `m`-th coefficient of the formal product `∏(1 - Xⁿ⁺¹)` equals that of the finite
partial product over `Finset.range (m + 1)`: the tail factors are `≡ 1 mod X^(m+1)`. -/
theorem coeff_tprod_one_sub_X_pow (m : ℕ) :
    coeff m (∏' n : ℕ, ((1 : ℤ⟦X⟧) - X ^ (n + 1))) =
      coeff m (∏ n ∈ Finset.range (m + 1), ((1 : ℤ⟦X⟧) - X ^ (n + 1))) := by
  have h1 : Filter.Tendsto
      (fun s : Finset ℕ ↦ coeff m (∏ n ∈ s, ((1 : ℤ⟦X⟧) - X ^ (n + 1))))
      Filter.atTop (𝓝 (coeff m (∏' n : ℕ, ((1 : ℤ⟦X⟧) - X ^ (n + 1))))) := by
    have hP := (WithPiTopology.multipliable_one_sub_X_pow ℤ).hasProd
    simp only [HasProd, SummationFilter.unconditional_filter] at hP
    exact ((WithPiTopology.continuous_coeff ℤ m).tendsto _).comp hP
  have h2 : Filter.Tendsto
      (fun s : Finset ℕ ↦ coeff m (∏ n ∈ s, ((1 : ℤ⟦X⟧) - X ^ (n + 1))))
      Filter.atTop
      (𝓝 (coeff m (∏ n ∈ Finset.range (m + 1), ((1 : ℤ⟦X⟧) - X ^ (n + 1))))) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop (Finset.range (m + 1))] with s hs
    exact (coeff_prod_one_sub_X_pow_stable
      (Finset.range_subset_range.mpr (Nat.le_succ m)) hs).symm
  exact tendsto_nhds_unique h1 h2

/-- The constant coefficient of the formal product `∏(1 - Xⁿ⁺¹)` is `1`. -/
theorem constantCoeff_tprod_one_sub_X_pow :
    constantCoeff (∏' n : ℕ, ((1 : ℤ⟦X⟧) - X ^ (n + 1))) = 1 := by
  rw [(WithPiTopology.multipliable_one_sub_X_pow ℤ).map_tprod _
    (WithPiTopology.continuous_constantCoeff ℤ)]
  simp

/-! ### Evaluation of integral power series

The bridge from the formal world to a topological field `k`: `evalInt q F = ∑ₙ Fₙqⁿ`.
Over a field complete with respect to a rank 1 nonarchimedean valuation and `|q| < 1`,
every `F ∈ ℤ⟦X⟧` is evaluable (integers have norm `≤ 1`, so the terms tend to zero), and
`evalInt q` is a ring homomorphism `ℤ⟦X⟧ → k`; the additive part is proved here from
summability hypotheses (`evalInt_add`, `evalInt_sub`), while multiplicativity — a
nonarchimedean Mertens theorem — is stated where the valuation is available
(`TateCurve.evalInt_mul` in the `TateCurve` file).
-/

section Evaluation

variable {k : Type*} [Field k] [TopologicalSpace k]

/-- The evaluation `∑ₙ Fₙqⁿ ∈ k` of an integral power series `F ∈ ℤ⟦X⟧` at a point `q` of
a topological field (junk value if the series does not converge). -/
noncomputable def evalInt (q : k) (F : ℤ⟦X⟧) : k :=
  ∑' n : ℕ, ((coeff n F : ℤ) : k) * q ^ n

@[simp]
theorem evalInt_C (q : k) (m : ℤ) : evalInt q (C m) = m := by
  simp only [evalInt]
  rw [tsum_eq_single 0 fun n hn ↦ by rw [coeff_C, if_neg hn]; simp]
  rw [coeff_C]
  simp

@[simp]
theorem evalInt_one (q : k) : evalInt q (1 : ℤ⟦X⟧) = 1 := by
  rw [← map_one (C : ℤ →+* ℤ⟦X⟧), evalInt_C, Int.cast_one]

@[simp]
theorem evalInt_X (q : k) : evalInt q (X : ℤ⟦X⟧) = q := by
  simp only [evalInt]
  rw [tsum_eq_single 1 fun n hn ↦ by rw [coeff_X, if_neg hn]; simp]
  rw [coeff_X]
  simp

variable [IsTopologicalRing k] [T2Space k]

theorem evalInt_C_mul (q : k) (m : ℤ) (F : ℤ⟦X⟧) :
    evalInt q (C m * F) = m * evalInt q F := by
  simp only [evalInt, coeff_C_mul, Int.cast_mul, mul_assoc]
  exact tsum_mul_left

theorem evalInt_add {q : k} {F G : ℤ⟦X⟧}
    (hF : Summable fun n ↦ ((coeff n F : ℤ) : k) * q ^ n)
    (hG : Summable fun n ↦ ((coeff n G : ℤ) : k) * q ^ n) :
    evalInt q (F + G) = evalInt q F + evalInt q G := by
  simp only [evalInt, map_add, Int.cast_add, add_mul]
  exact hF.tsum_add hG

theorem evalInt_sub {q : k} {F G : ℤ⟦X⟧}
    (hF : Summable fun n ↦ ((coeff n F : ℤ) : k) * q ^ n)
    (hG : Summable fun n ↦ ((coeff n G : ℤ) : k) * q ^ n) :
    evalInt q (F - G) = evalInt q F - evalInt q G := by
  simp only [evalInt, map_sub, Int.cast_sub, sub_mul]
  exact hF.tsum_sub hG

end Evaluation

end TateCurve

/-! ### Step 3: evaluation in a topological field -/

variable {k : Type*} [Field k] [TopologicalSpace k]

/-- The inverse of `q ↦ j(q)` (Silverman, ATAEC V.5.2): for `|j| > 1`, the unique `q`
with `0 < |q| < 1` and `j(q) = j`, namely the evaluation
`q = j⁻¹ + 744j⁻² + 750420j⁻³ + ⋯` at `j⁻¹` of the integral power series
`TateCurve.jInvReverse`. Over a field complete with respect to a rank 1 nonarchimedean
valuation the series converges for `|j| > 1`, since its coefficients are integers, hence
of norm `≤ 1` (junk value for `|j| ≤ 1`).

Design note: unique existence cannot be turned into data in Lean without
`Classical.choose`, so instead of stating V.5.2 as an `∃!` we take the *inverse map* — an
explicit power series, hence data on its own merits — as the definition. Uniqueness is
then the round-trip identity `tateParameter_tateJ`, and no choice is involved anywhere. -/
noncomputable def WeierstrassCurve.tateParameter (j : k) : k :=
  TateCurve.evalInt j⁻¹ TateCurve.jInvReverse
