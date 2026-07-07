/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurve

import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!

# Blueprint: completing the Tate uniformisation `tateCurveEquiv`

Let `k` be a nonarchimedean local field and `q ∈ kˣ` with `|q| < 1`. The map

`φ : kˣ → E_q(k)`, `u ↦ (X(u,q), Y(u,q))` for `u ∉ qᶻ`, `qᶻ ↦ O`

(`WeierstrassCurve.tateCurvePoint`) is known to be well defined: the Weierstrass
equation for the values is proved (`tateCurve_equation`, Silverman ATAEC V.1.1(a), via
the annulus expansions, the `evalK` calculus, and the descent of the formal identity
through `ℤ[t, t⁻¹, (1-t)⁻¹]`), and `φ` descends to the quotient `kˣ/qᶻ`
(`tateCurvePoint_eq`, from the `qᶻ`-invariance of the coordinate series). What remains
of `WeierstrassCurve.tateCurveEquiv` — that `φ` is a *group isomorphism*
`kˣ/qᶻ ≃ E_q(k)` — is exactly its four sorried fields: `invFun`, `left_inv`,
`right_inv` (bijectivity) and `map_add'` (additivity).

This file blueprints the route, states the intermediate results (sorried), and proves
the two purely algebraic reductions. The plan follows Silverman ATAEC V.1.1(b)–(d) and
reuses the two pillars already in place: every analytic identity is proved once over
`ℂ`, descended to an initial coefficient ring, and evaluated in `k` via the
nonarchimedean calculus (`EvalBounded`/`evalK`); and every function of `u` is
normalised into the fundamental annulus `|q| < |u| ≤ 1` by `qᶻ`-periodicity.

## Stage 1: negation (`tateX_inv`, `tateY_inv`)

`X(u⁻¹) = X(u)` and `Y(u⁻¹) = -Y(u) - X(u)`, i.e. `φ(u⁻¹) = -φ(u)` (negation on
`y² + xy = ⋯` is `(x, y) ↦ (x, -y - x)`). These are direct series manipulations,
proved below: reindex the two-sided sums by `n ↦ -n` (`Equiv.neg ℤ`) and apply the
inversion identities `div_one_sub_sq_inv`, `sq_div_one_sub_cube_inv` termwise. The
`Y`-identity mixes the two coordinate series, so it also needs their genuine
`ℤ`-indexed convergence for every `u ∈ kˣ` (`summable_tateX_int`,
`summable_tateY_int`), which the tail lemma `summable_pow_div_tail` provides.

## Stage 2: the theta function

`θ(u, q) = ∏_{n≥0}(1 - qⁿu) · ∏_{n≥1}(1 - qⁿu⁻¹)` (`TateCurve.tateTheta`) converges
for every `u ∈ kˣ` (the factors tend to `1` nonarchimedeanly), satisfies the
functional equations

* `θ(qu) = -u⁻¹·θ(u)` (`tateTheta_mul_left`) — shift the two products by one step;
* `θ(u⁻¹) = -u⁻¹·θ(u)` (`tateTheta_inv`) — swap the two products;

and vanishes exactly on `qᶻ` (`tateTheta_eq_zero_iff`): on the fundamental annulus
every factor except `1 - u` is a unit (valuation `1`), so `θ(u) = 0` iff `u = 1`
there, and the functional equation propagates this to all of `kˣ`. The nonvanishing
statement needs a "leading term" lemma for infinite products of `1 + (small)` factors,
in the style of `valuation_evalInt_eq`.

Formally, `θ` lives in `ℤ[u, u⁻¹]⟦q⟧` (the products converge coefficientwise in the
`q`-adic topology, as for `ΔFormal`), and identities involving `θ` descend from `ℂ` to
`k` exactly as in `TateCurveDescent`: proved analytically against the Weierstrass
`σ`-function, transported to the initial localization of `ℤ[t₁, t₂, …]`, and evaluated
through `evalK`.

## Stage 3: injectivity via the difference identity

The classical `σ`-function identity `℘(z₁) - ℘(z₂) = -σ(z₁+z₂)σ(z₁-z₂)/(σ(z₁)σ(z₂))²`
becomes, on the Tate curve (`tateX_sub_tateX`, constants fixed by the `q⁰`-coefficient):

`X(u) - X(v) = -v · θ(uv)·θ(u/v) / (θ(u)²·θ(v)²)`.

If `φ(u) = φ(v)` then `X(u) = X(v)`, so `θ(uv)·θ(u/v) = 0` (the denominator is a unit
for `u, v ∉ qᶻ`), hence `v ≡ u±¹ (mod qᶻ)` by Stage 2. If `v ≡ u⁻¹` but `v ≢ u`, then
`Y(v) = -Y(u) - X(u) ≠ Y(u)` by Stage 1 — unless `2Y(u) + X(u) = 0`, which is the
`2`-torsion case `u² ∈ qᶻ`, where `u⁻¹ ≡ u` anyway. Hence `tateCurvePoint_eq_iff`.

## Stage 4: additivity via the generic addition law

For `u, v` in general position (`u, v, uv ∉ qᶻ` and `X(u) ≠ X(v)`), the chord law on
`y² + xy = x³ + a₄x + a₆` reads, with `λ = (Y(u) - Y(v))/(X(u) - X(v))`:

`X(uv) = λ² + λ - X(u) - X(v)`,  `Y(uv) = -(Y(u) + λ(X(uv) - X(u))) - X(uv)`

(`tateX_mul_of_ne`, `tateY_mul_of_ne`, matching mathlib's `Affine.addX`/`addY`). These
are again bridge identities: over `ℂ` they are the addition theorem for `℘, ℘'`; the
coefficient ring is now two-variable, `ℤ[t₁, t₂]` localized away from
`t₁t₂(1-t₁)(1-t₂)(t₁-t₂)(1-t₁t₂)`, and the evaluation calculus is unchanged (the
series in `u = t₁, v = t₂` are `EvalBounded` for the same `ρ`). The analytic input
(the `℘`-addition theorem) is the only piece not yet in the repertoire of
`TateCurveConstruction`.

The degenerate configurations (`u ≡ v`: doubling; `X(u) = X(v)` otherwise: vertical
chords) need *no* further identities: `map_mul_of_generic` (proved below) upgrades
additivity on generic pairs to all pairs, by choosing an auxiliary `w` avoiding
finitely many bad cosets — possible since `kˣ/qᶻ` is infinite — and cancelling. The
vertical case `v ≡ u⁻¹` is Stage 1.

## Stage 5: surjectivity

Given an affine point `(x, y) ∈ E_q(k)`, one needs `u` with `X(u) = x` and (after
replacing `u` by `u⁻¹`, which swaps the two roots `Y(u)`, `-Y(u)-X(u)` of the
`y`-quadratic) `Y(u) = y`; this is `exists_tateX_eq` plus field algebra. Two routes:

* **Zero counting** (Silverman): `f(u) = X(u) - x` is a theta-type function:
  `f(qu) = f(u)` and `f·θ(u)²` is given by an everywhere-convergent two-sided series.
  The kernel is a nonarchimedean Abel-type lemma: a nonzero series
  `∑_{n∈ℤ} aₙuⁿ` with `f(qu) = c·u^{-r}·f(u)` has exactly `r` zeros modulo `qᶻ`
  (counted with multiplicity, product of zeros determined by `c` and the leading
  coefficients). Existence of zeros comes from the Newton polygon of the coefficients,
  which the functional equation (`aₙ₊ᵣ = c⁻¹qⁿaₙ` up to normalisation) makes
  eventually strictly convex; a zero a priori lies in a finite extension, and Galois
  invariance of the *pair* `{u, u⁻¹} mod qᶻ` plus the `k`-rationality of `y`
  forces `u ∈ k`.
* **Formal-group fallback**: near `O`, the parameter `t = -x/y` satisfies
  `t(u) = (u - 1) + O(q, (u-1)²)`, a power series in `u - 1` with unit linear
  coefficient; `PowerSeries.substInv` (as in `TateParameter`) inverts it, giving a
  local inverse `1 + 𝔪 ≃ E₁(k)`. Surjectivity then follows from additivity plus an
  analysis of reduction (`E(k)/E₁(k)` against `kˣ/(1+𝔪)qᶻ`), but this route needs the
  reduction theory of `E_q`, which is itself on the roadmap.

## Assembly

With `tateCurvePoint_mul`, `tateCurvePoint_eq_iff` and `tateCurvePoint_surjective`,
the four sorried fields of `tateCurveEquiv` fill mechanically: `map_add'` descends
`tateCurvePoint_mul` to the quotient; `invFun` is `Function.surjInv` of surjectivity
composed with the quotient map; the inverse identities follow from
`tateCurvePoint_eq_iff` (injectivity on the quotient) and surjectivity.

-/

open scoped WeierstrassCurve.Affine

open ValuativeRel

@[expose] public section

/-! ### The generic-to-global reduction for additivity -/

/-- Upgrading a generically additive map to a globally additive one: if
`f (a * b) = f a + f b` holds off a bad set of pairs, and for every pair an auxiliary
`w` exists making the three pairs `(ab, w)`, `(a, bw)`, `(b, w)` good, then additivity
holds everywhere, by cancellation of `f w`. In the application `G = kˣ`,
`H = E_q(k)`, and the bad set consists of finitely many `qᶻ`-coset conditions per
pair, which the infinitude of `kˣ/qᶻ` lets `w` avoid. -/
theorem TateCurve.map_mul_of_generic {G H : Type*} [CommGroup G] [AddCommGroup H]
    (f : G → H) (Bad : Set (G × G))
    (hmul : ∀ a b : G, (a, b) ∉ Bad → f (a * b) = f a + f b)
    (hgen : ∀ a b : G, ∃ w : G, (a * b, w) ∉ Bad ∧ (a, b * w) ∉ Bad ∧ (b, w) ∉ Bad)
    (a b : G) : f (a * b) = f a + f b := by
  obtain ⟨w, h1, h2, h3⟩ := hgen a b
  have key : f (a * b) + f w = f a + f b + f w := by
    rw [← hmul _ _ h1, mul_assoc a b w, hmul _ _ h2, hmul _ _ h3, ← add_assoc]
  exact add_right_cancel key

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-! ### Stage 1: negation -/

/-- The tail-summability workhorse for the two-sided coordinate series: for `|q| < 1`,
`u ≠ 0` and exponents `1 ≤ i`, the series `∑ₙ (qⁿ⁺¹u)ⁱ/(1 - qⁿ⁺¹u)ʲ` converges. After
discarding the finitely many indices with `|qⁿ⁺¹u| ≥ 1` (`summable_nat_add_iff`), the
denominators are isosceles-trivial (`Valuation.map_one_sub_of_lt`) and the terms are
bounded by `C·|q|ⁿ` with `C = |u|·|q|^(N+1)`, which is the constant-carrying
summability criterion. -/
theorem TateCurve.summable_pow_div_tail (q u : k) (hq : valuation k q < 1) (hu : u ≠ 0)
    (i j : ℕ) (hi : 1 ≤ i) :
    Summable fun n : ℕ ↦ (q ^ (n + 1) * u) ^ i / (1 - q ^ (n + 1) * u) ^ j := by
  rcases eq_or_ne q 0 with rfl | hq0
  · refine summable_zero.congr fun n ↦ ?_
    rw [zero_pow (Nat.succ_ne_zero n), zero_mul, zero_pow (by omega : i ≠ 0), zero_div]
  · have hvq : valuation k q ≠ 0 := (valuation k).ne_zero_iff.mpr hq0
    have hvu : valuation k u ≠ 0 := (valuation k).ne_zero_iff.mpr hu
    obtain ⟨N, hN⟩ := exists_pow_lt hq (Units.mk0 (valuation k u)⁻¹ (inv_ne_zero hvu))
    have hδ : valuation k u * valuation k q ^ N < 1 :=
      mul_pow_lt hvu (by rw [mul_one]; exact hN)
    rw [← summable_nat_add_iff N]
    refine summable_of_valuation_le_const_mul_pow
      (C := valuation k u * valuation k q ^ (N + 1))
      (mul_ne_zero hvu (pow_ne_zero _ hvq)) hq _ fun n ↦ ?_
    have hx : valuation k (q ^ (n + N + 1) * u) =
        valuation k u * valuation k q ^ (N + 1) * valuation k q ^ n := by
      rw [map_mul, map_pow, show n + N + 1 = N + 1 + n from by omega, pow_add,
        mul_comm _ (valuation k u), ← mul_assoc]
    have hxlt : valuation k (q ^ (n + N + 1) * u) < 1 := by
      rw [hx]
      calc valuation k u * valuation k q ^ (N + 1) * valuation k q ^ n
          ≤ valuation k u * valuation k q ^ (N + 1) * 1 :=
            mul_le_mul' le_rfl (pow_le_one' hq.le n)
        _ = valuation k u * (valuation k q ^ N * valuation k q) := by
            rw [mul_one, pow_succ]
        _ = valuation k u * valuation k q ^ N * valuation k q := by rw [mul_assoc]
        _ ≤ valuation k u * valuation k q ^ N * 1 := mul_le_mul' le_rfl hq.le
        _ = valuation k u * valuation k q ^ N := mul_one _
        _ < 1 := hδ
    rw [map_div₀, map_pow, map_pow, (valuation k).map_one_sub_of_lt hxlt, one_pow,
      div_one]
    calc valuation k (q ^ (n + N + 1) * u) ^ i
        ≤ valuation k (q ^ (n + N + 1) * u) ^ 1 :=
          pow_le_pow_right_of_le_one' hxlt.le hi
      _ = valuation k (q ^ (n + N + 1) * u) := pow_one _
      _ = valuation k u * valuation k q ^ (N + 1) * valuation k q ^ n := hx

/-- The two-sided `x`-coordinate series converges for every `u ∈ kˣ` when `|q| < 1`
(including `u ∈ qᶻ`, where the singular term takes the junk value `0`): both tails are
instances of `summable_pow_div_tail`, the negative one after the inversion identity
`div_one_sub_sq_inv`. -/
theorem TateCurve.summable_tateX_int (q u : kˣ) (hq : valuation k (q : k) < 1) :
    Summable fun n : ℤ ↦ (q : k) ^ n * (u : k) / (1 - (q : k) ^ n * (u : k)) ^ 2 := by
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hcoe : ∀ n : ℕ, (q : k) ^ ((n : ℤ) + 1) = (q : k) ^ (n + 1) := fun n ↦ by
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  refine Summable.of_add_one_of_neg_add_one ?_ ?_
  · exact (summable_pow_div_tail (q : k) (u : k) hq hu0 1 2 le_rfl).congr fun n ↦ by
      rw [pow_one, hcoe n]
  · refine (summable_pow_div_tail (q : k) ((u : k)⁻¹) hq (inv_ne_zero hu0) 1 2
      le_rfl).congr fun n ↦ ?_
    rw [pow_one, zpow_neg, hcoe n,
      div_one_sub_sq_inv (v := ((q : k) ^ (n + 1))⁻¹ * (u : k))
        (mul_ne_zero (inv_ne_zero (pow_ne_zero _ (Units.ne_zero q))) hu0),
      mul_inv, inv_inv]

/-- The two-sided `y`-coordinate series converges for every `u ∈ kˣ` when `|q| < 1`;
as `summable_tateX_int`, with the negative tail entering through the antisymmetry
`sq_div_one_sub_cube_inv`. -/
theorem TateCurve.summable_tateY_int (q u : kˣ) (hq : valuation k (q : k) < 1) :
    Summable fun n : ℤ ↦
      ((q : k) ^ n * (u : k)) ^ 2 / (1 - (q : k) ^ n * (u : k)) ^ 3 := by
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hcoe : ∀ n : ℕ, (q : k) ^ ((n : ℤ) + 1) = (q : k) ^ (n + 1) := fun n ↦ by
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  refine Summable.of_add_one_of_neg_add_one ?_ ?_
  · exact (summable_pow_div_tail (q : k) (u : k) hq hu0 2 3 (by omega)).congr fun n ↦ by
      rw [hcoe n]
  · refine ((summable_pow_div_tail (q : k) ((u : k)⁻¹) hq (inv_ne_zero hu0) 1 3
      le_rfl).neg).congr fun n ↦ ?_
    rw [pow_one, zpow_neg, hcoe n,
      sq_div_one_sub_cube_inv (v := ((q : k) ^ (n + 1))⁻¹ * (u : k))
        (mul_ne_zero (inv_ne_zero (pow_ne_zero _ (Units.ne_zero q))) hu0),
      mul_inv, inv_inv]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- `X(u⁻¹, q) = X(u, q)`: the `x`-coordinate series is even. Reindex the two-sided
sum by `n ↦ -n` (which needs no summability) and apply `div_one_sub_sq_inv`
termwise. True with junk values for all `q, u`. -/
theorem WeierstrassCurve.tateX_inv (q u : k) :
    tateX u⁻¹ q = tateX u q := by
  rcases eq_or_ne u 0 with rfl | hu
  · rw [inv_zero]
  · simp only [tateX]
    congr 1
    rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ ↦ q ^ n * u⁻¹ / (1 - q ^ n * u⁻¹) ^ 2)]
    refine tsum_congr fun n ↦ ?_
    simp only [Equiv.neg_apply]
    rcases eq_or_ne (q ^ n) 0 with h | h
    · rw [zpow_neg, h, inv_zero]
      simp
    · rw [zpow_neg, ← mul_inv]
      exact (TateCurve.div_one_sub_sq_inv (mul_ne_zero h hu)).symm

/-- `Y(u⁻¹, q) = -Y(u, q) - X(u, q)`: inversion of the parameter is negation on the
curve `y² + xy = x³ + a₄x + a₆` (whose negation is `(x, y) ↦ (x, -y - x)`). Reindex
by `n ↦ -n`, apply `sq_div_one_sub_cube_inv` termwise (producing the combination
`-fY(n) - fX(n)` of the two coordinate integrands), and split the sum using the
`ℤ`-summability of both series. -/
theorem WeierstrassCurve.tateY_inv (q u : kˣ) (hq : valuation k (q : k) < 1) :
    tateY ((u : k)⁻¹) (q : k) =
      -tateY (u : k) (q : k) - tateX (u : k) (q : k) := by
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hX := TateCurve.summable_tateX_int q u hq
  have hY := TateCurve.summable_tateY_int q u hq
  have hterm : ∀ n : ℤ,
      ((q : k) ^ (-n) * (u : k)⁻¹) ^ 2 / (1 - (q : k) ^ (-n) * (u : k)⁻¹) ^ 3 =
      -(((q : k) ^ n * (u : k)) ^ 2 / (1 - (q : k) ^ n * (u : k)) ^ 3 +
        (q : k) ^ n * (u : k) / (1 - (q : k) ^ n * (u : k)) ^ 2) := by
    intro n
    have hqn : (q : k) ^ n ≠ 0 := zpow_ne_zero _ (Units.ne_zero q)
    rw [zpow_neg, ← mul_inv,
      TateCurve.sq_div_one_sub_cube_inv (v := ((q : k) ^ n * (u : k))⁻¹)
        (inv_ne_zero (mul_ne_zero hqn hu0)),
      inv_inv]
    rcases eq_or_ne (1 - (q : k) ^ n * (u : k)) 0 with h1 | h1
    · rw [h1]
      simp
    · field_simp
      ring
  simp only [tateY, tateX]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ ↦
    ((q : k) ^ n * (u : k)⁻¹) ^ 2 / (1 - (q : k) ^ n * (u : k)⁻¹) ^ 3)]
  rw [tsum_congr fun n ↦ by simpa only [Equiv.neg_apply] using hterm n]
  rw [tsum_neg, Summable.tsum_add hY hX]
  ring

/-! ### Stage 2: the theta function -/

/-- The Tate theta function
`θ(u, q) = ∏_{n ≥ 0}(1 - qⁿu) · ∏_{n ≥ 1}(1 - qⁿu⁻¹)`, convergent for all `u ∈ kˣ`
when `|q| < 1` (junk value otherwise, by the `tprod` convention). Up to a trivial
factor this is the Jacobi triple product; it is the nonarchimedean avatar of the
Weierstrass `σ`-function, and the coordinates and their difference identities are
rational expressions in `θ`. -/
noncomputable def TateCurve.tateTheta (u q : k) : k :=
  (∏' n : ℕ, (1 - q ^ n * u)) * ∏' n : ℕ, (1 - q ^ (n + 1) * u⁻¹)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- A finite product of factors `1 - xₙ` with `|xₙ| ≤ δ ≤ 1` is `1 + O(δ)`: the
ultrametric induction behind convergence and nonvanishing of theta products. -/
theorem TateCurve.valuation_prod_one_sub_sub_one_le {δ : ValueGroupWithZero k}
    (hδ : δ ≤ 1) {x : ℕ → k} (s : Finset ℕ) (hx : ∀ n ∈ s, valuation k (x n) ≤ δ) :
    valuation k ((∏ n ∈ s, (1 - x n)) - 1) ≤ δ := by
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.prod_empty, sub_self, map_zero]
      exact zero_le
  | cons a s ha ih =>
      have hP : valuation k ((∏ n ∈ s, (1 - x n)) - 1) ≤ δ :=
        ih fun n hn ↦ hx n (Finset.mem_cons.mpr (Or.inr hn))
      have hP1 : valuation k (∏ n ∈ s, (1 - x n)) ≤ 1 := by
        have h := (valuation k).map_add 1 ((∏ n ∈ s, (1 - x n)) - 1)
        rw [show (1 : k) + ((∏ n ∈ s, (1 - x n)) - 1) = ∏ n ∈ s, (1 - x n) from by ring,
          map_one] at h
        exact h.trans (max_le le_rfl (hP.trans hδ))
      rw [Finset.prod_cons,
        show (1 - x a) * (∏ n ∈ s, (1 - x n)) - 1 =
          ((∏ n ∈ s, (1 - x n)) - 1) - x a * (∏ n ∈ s, (1 - x n)) from by ring]
      refine le_trans ((valuation k).map_sub _ _) (max_le hP ?_)
      rw [map_mul]
      calc valuation k (x a) * valuation k (∏ n ∈ s, (1 - x n))
          ≤ δ * 1 := mul_le_mul' (hx a (Finset.mem_cons_self a s)) hP1
        _ = δ := mul_one δ

/-- Partial products of theta factors are uniformly bounded in valuation: only the
finitely many factors with `|qⁿu| > 1` can exceed valuation `1`. -/
theorem TateCurve.exists_valuation_prod_one_sub_le (q u : k) (hq : valuation k q < 1)
    (hu : u ≠ 0) :
    ∃ B : ValueGroupWithZero k, B ≠ 0 ∧ ∀ s : Finset ℕ,
      valuation k (∏ n ∈ s, (1 - q ^ n * u)) ≤ B := by
  have hvu : valuation k u ≠ 0 := (valuation k).ne_zero_iff.mpr hu
  obtain ⟨N, hN⟩ := exists_pow_lt hq (Units.mk0 (valuation k u)⁻¹ (inv_ne_zero hvu))
  have htail : ∀ n, N ≤ n → valuation k (1 - q ^ n * u) ≤ 1 := by
    intro n hn
    refine le_trans ((valuation k).map_sub _ _) (max_le (by rw [map_one]) ?_)
    rw [map_mul, map_pow]
    refine le_trans (mul_le_mul' (pow_le_pow_right_of_le_one' hq.le hn) le_rfl) ?_
    have h := mul_pow_lt (C := valuation k u) hvu (γ := 1) (by rw [mul_one]; exact hN)
    rw [mul_comm] at h
    exact h.le
  refine ⟨∏ n ∈ Finset.range N, max 1 (valuation k (1 - q ^ n * u)), ?_, fun s ↦ ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    exact fun n _ ↦ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).ne'
  · rw [map_prod]
    calc (∏ n ∈ s, valuation k (1 - q ^ n * u))
        ≤ ∏ n ∈ s, (if n < N then max 1 (valuation k (1 - q ^ n * u)) else 1) := by
          refine Finset.prod_le_prod' fun n _ ↦ ?_
          rcases lt_or_ge n N with h | h
          · rw [if_pos h]
            exact le_max_right _ _
          · rw [if_neg (not_lt.mpr h)]
            exact htail n h
      _ ≤ ∏ n ∈ s ∪ Finset.range N,
            (if n < N then max 1 (valuation k (1 - q ^ n * u)) else 1) := by
          refine Finset.prod_le_prod_of_subset_of_one_le' Finset.subset_union_left
            fun n _ _ ↦ ?_
          rcases lt_or_ge n N with h | h
          · rw [if_pos h]
            exact le_max_left _ _
          · rw [if_neg (not_lt.mpr h)]
      _ = ∏ n ∈ Finset.range N,
            (if n < N then max 1 (valuation k (1 - q ^ n * u)) else 1) := by
          refine (Finset.prod_subset Finset.subset_union_right fun n _ hn ↦ ?_).symm
          rw [if_neg fun hlt ↦ hn (Finset.mem_range.mpr hlt)]
      _ = ∏ n ∈ Finset.range N, max 1 (valuation k (1 - q ^ n * u)) :=
          Finset.prod_congr rfl fun n hn ↦ if_pos (Finset.mem_range.mp hn)

/-- A product with a vanishing factor vanishes (witnessed by `HasProd`, so no
multipliability hypothesis is needed). -/
theorem TateCurve.tprod_eq_zero {f : ℕ → k} (n₀ : ℕ) (h : f n₀ = 0) :
    ∏' n : ℕ, f n = 0 := by
  have h0 : HasProd f 0 := by
    simp only [HasProd, SummationFilter.unconditional_filter]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop {n₀}] with s hs
    exact (Finset.prod_eq_zero (hs (Finset.mem_singleton_self n₀)) h).symm
  exact h0.tprod_eq

/-- An infinite product of factors `1 - xₙ` with `|xₙ| ≤ δ < 1` has valuation `1` (in
particular it is nonzero): some partial product is close to the limit, and all partial
products are `1 + O(δ)`. -/
theorem TateCurve.valuation_tprod_one_sub_eq_one {x : ℕ → k}
    {δ : ValueGroupWithZero k} (hδ : δ < 1) (hx : ∀ n, valuation k (x n) ≤ δ)
    (hmul : Multipliable fun n : ℕ ↦ 1 - x n) :
    valuation k (∏' n : ℕ, (1 - x n)) = 1 := by
  obtain ⟨P, hP⟩ := hmul
  rw [hP.tprod_eq]
  have hP' := hP
  simp only [HasProd, SummationFilter.unconditional_filter] at hP'
  rw [(IsValuativeTopology.hasBasis_nhds P).tendsto_right_iff] at hP'
  obtain ⟨s₀, hs₀⟩ := (hP' 1 trivial).exists
  simp only [Set.mem_setOf_eq] at hs₀
  have h1 : valuation k ((∏ n ∈ s₀, (1 - x n)) - 1) ≤ δ :=
    valuation_prod_one_sub_sub_one_le hδ.le s₀ fun n _ ↦ hx n
  have hP1 : valuation k (P - 1) < 1 := by
    rw [← sub_add_sub_cancel P (∏ n ∈ s₀, (1 - x n)) 1]
    refine lt_of_le_of_lt ((valuation k).map_add _ _)
      (max_lt ?_ (lt_of_le_of_lt h1 hδ))
    rw [(valuation k).map_sub_swap]
    exact hs₀
  rw [show P = 1 + (P - 1) from by ring,
    (valuation k).map_add_eq_of_lt_left (by rwa [map_one]), map_one]

/-- Theta-type products converge on a nonarchimedean local field: for `|q| < 1` the
factors `1 - qⁿu` tend to `1`, so the partial products along `Finset.range` form a
Cauchy sequence (using the uniform bound above), and completeness plus the ultrametric
perturbation lemma upgrade the sequential limit to unconditional convergence. (Mathlib's
nonarchimedean criterion is for groups, so it does not apply to products in `k`.) -/
theorem TateCurve.multipliable_tateTheta (q : k) (hq : valuation k q < 1) (u : k) :
    Multipliable fun n : ℕ ↦ 1 - q ^ n * u := by
  rcases eq_or_ne u 0 with rfl | hu
  · exact multipliable_one.congr fun n ↦ by rw [mul_zero, sub_zero]
  have hvu : valuation k u ≠ 0 := (valuation k).ne_zero_iff.mpr hu
  obtain ⟨B, hB0, hB⟩ := exists_valuation_prod_one_sub_le q u hq hu
  letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  haveI : NonarchimedeanRing k := by
    convert! ValuativeRel.nonarchimedeanRing k
    exact Valuation.toTopologicalSpace_eq _
  have hcauchy : CauchySeq fun N : ℕ ↦ ∏ n ∈ Finset.range N, (1 - q ^ n * u) := by
    refine NonarchimedeanAddGroup.cauchySeq_of_tendsto_sub_nhds_zero ?_
    rw [(IsValuativeTopology.hasBasis_nhds (0 : k)).tendsto_right_iff]
    intro γ _
    obtain ⟨M, hM⟩ := exists_pow_lt hq (Units.mk0
      ((B * valuation k u)⁻¹ * (γ : ValueGroupWithZero k))
      (mul_ne_zero (inv_ne_zero (mul_ne_zero hB0 hvu)) γ.ne_zero))
    filter_upwards [Filter.eventually_ge_atTop M] with N hN
    simp only [sub_zero]
    rw [Finset.prod_range_succ,
      show (∏ n ∈ Finset.range N, (1 - q ^ n * u)) * (1 - q ^ N * u) -
          ∏ n ∈ Finset.range N, (1 - q ^ n * u) =
        -((∏ n ∈ Finset.range N, (1 - q ^ n * u)) * (q ^ N * u)) from by ring,
      (valuation k).map_neg, map_mul, map_mul, map_pow]
    calc valuation k (∏ n ∈ Finset.range N, (1 - q ^ n * u)) *
          (valuation k q ^ N * valuation k u)
        ≤ B * (valuation k q ^ N * valuation k u) := mul_le_mul' (hB _) le_rfl
      _ = B * valuation k u * valuation k q ^ N := by
          rw [mul_comm (valuation k q ^ N) _, ← mul_assoc]
      _ ≤ B * valuation k u * valuation k q ^ M :=
          mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' hq.le hN)
      _ < γ := mul_pow_lt (mul_ne_zero hB0 hvu) hM
  obtain ⟨P, hP⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨P, ?_⟩
  simp only [HasProd, SummationFilter.unconditional_filter]
  rw [(IsValuativeTopology.hasBasis_nhds P).tendsto_right_iff]
  intro γ _
  obtain ⟨M₁, hM₁⟩ := exists_pow_lt hq (Units.mk0
    ((B * valuation k u)⁻¹ * (γ : ValueGroupWithZero k))
    (mul_ne_zero (inv_ne_zero (mul_ne_zero hB0 hvu)) γ.ne_zero))
  obtain ⟨M₂, hM₂⟩ := exists_pow_lt hq (Units.mk0 (valuation k u)⁻¹ (inv_ne_zero hvu))
  rw [(IsValuativeTopology.hasBasis_nhds P).tendsto_right_iff] at hP
  obtain ⟨M₃, hM₃⟩ := Filter.eventually_atTop.mp (hP γ trivial)
  set M := max (max M₁ M₂) M₃ with hMdef
  have hM₁M : M₁ ≤ M := le_trans (le_max_left M₁ M₂) (le_max_left _ M₃)
  have hM₂M : M₂ ≤ M := le_trans (le_max_right M₁ M₂) (le_max_left _ M₃)
  filter_upwards [Filter.eventually_ge_atTop (Finset.range M)] with s hs
  have hδ1 : valuation k q ^ M * valuation k u < 1 := by
    refine lt_of_le_of_lt
      (mul_le_mul' (pow_le_pow_right_of_le_one' hq.le hM₂M) le_rfl) ?_
    have h := mul_pow_lt (C := valuation k u) hvu (γ := 1)
      (by rw [mul_one]; exact hM₂)
    rwa [mul_comm] at h
  have hAtail : valuation k ((∏ n ∈ s \ Finset.range M, (1 - q ^ n * u)) - 1) ≤
      valuation k q ^ M * valuation k u := by
    refine valuation_prod_one_sub_sub_one_le hδ1.le _ fun n hn ↦ ?_
    have hMn : M ≤ n := by
      have h := (Finset.mem_sdiff.mp hn).2
      rw [Finset.mem_range] at h
      omega
    rw [map_mul, map_pow]
    exact mul_le_mul' (pow_le_pow_right_of_le_one' hq.le hMn) le_rfl
  have h1 : valuation k ((∏ n ∈ s, (1 - q ^ n * u)) -
      ∏ n ∈ Finset.range M, (1 - q ^ n * u)) < γ := by
    rw [← Finset.prod_sdiff hs,
      show (∏ n ∈ s \ Finset.range M, (1 - q ^ n * u)) *
          (∏ n ∈ Finset.range M, (1 - q ^ n * u)) -
          ∏ n ∈ Finset.range M, (1 - q ^ n * u) =
        (∏ n ∈ Finset.range M, (1 - q ^ n * u)) *
          ((∏ n ∈ s \ Finset.range M, (1 - q ^ n * u)) - 1) from by ring,
      map_mul]
    calc valuation k (∏ n ∈ Finset.range M, (1 - q ^ n * u)) *
          valuation k ((∏ n ∈ s \ Finset.range M, (1 - q ^ n * u)) - 1)
        ≤ B * (valuation k q ^ M * valuation k u) := mul_le_mul' (hB _) hAtail
      _ = B * valuation k u * valuation k q ^ M := by
          rw [mul_comm (valuation k q ^ M) _, ← mul_assoc]
      _ ≤ B * valuation k u * valuation k q ^ M₁ :=
          mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' hq.le hM₁M)
      _ < γ := mul_pow_lt (mul_ne_zero hB0 hvu) hM₁
  have h2 := hM₃ M (le_max_right _ _)
  simp only [Set.mem_setOf_eq] at h2 ⊢
  rw [← sub_add_sub_cancel (∏ n ∈ s, (1 - q ^ n * u))
    (∏ n ∈ Finset.range M, (1 - q ^ n * u)) P]
  exact lt_of_le_of_lt ((valuation k).map_add _ _) (max_lt h1 h2)

/-- The functional equation `θ(qu) = -u⁻¹·θ(u)`: shifting `u` by `q` shifts the two
products by one step in opposite directions, exchanging the factor `1 - u` for
`1 - u⁻¹ = -u⁻¹(1 - u)`. This makes `θ` a "theta function of degree 1 for `qᶻ`". -/
theorem TateCurve.tateTheta_mul_left (q : kˣ) (hq : valuation k (q : k) < 1) (u : kˣ) :
    tateTheta ((q : k) * u) (q : k) = -(u : k)⁻¹ * tateTheta (u : k) (q : k) := by
  have hq0 : (q : k) ≠ 0 := Units.ne_zero q
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hAqu : (∏' n : ℕ, (1 - (q : k) ^ n * ((q : k) * u))) =
      ∏' n : ℕ, (1 - (q : k) ^ (n + 1) * u) :=
    tprod_congr fun n ↦ by rw [pow_succ]; ring_nf
  have hBqu : (∏' n : ℕ, (1 - (q : k) ^ (n + 1) * ((q : k) * (u : k))⁻¹)) =
      ∏' n : ℕ, (1 - (q : k) ^ n * (u : k)⁻¹) :=
    tprod_congr fun n ↦ by
      rw [mul_inv, ← mul_assoc, pow_succ, mul_assoc ((q : k) ^ n) _ _,
        mul_inv_cancel₀ hq0, mul_one]
  have htailA : Multipliable fun n : ℕ ↦ 1 - (q : k) ^ (n + 1) * (u : k) :=
    (multipliable_tateTheta (q : k) hq ((q : k) * u)).congr fun n ↦ by ring
  have htailB : Multipliable fun n : ℕ ↦ 1 - (q : k) ^ (n + 1) * (u : k)⁻¹ :=
    (multipliable_tateTheta (q : k) hq ((q : k) * (u : k)⁻¹)).congr fun n ↦ by ring
  have hsplitA : (∏' n : ℕ, (1 - (q : k) ^ n * u)) =
      (1 - (u : k)) * ∏' n : ℕ, (1 - (q : k) ^ (n + 1) * u) := by
    simpa using tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 - (q : k) ^ n * (u : k)) htailA
  have hsplitB : (∏' n : ℕ, (1 - (q : k) ^ n * (u : k)⁻¹)) =
      (1 - (u : k)⁻¹) * ∏' n : ℕ, (1 - (q : k) ^ (n + 1) * (u : k)⁻¹) := by
    simpa using tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 - (q : k) ^ n * (u : k)⁻¹) htailB
  have hscal : (1 : k) - (u : k)⁻¹ = -(u : k)⁻¹ * (1 - (u : k)) := by
    field_simp
    ring
  simp only [tateTheta]
  rw [hAqu, hBqu, hsplitB, hsplitA, hscal]
  generalize (∏' n : ℕ, (1 - (q : k) ^ (n + 1) * (u : k))) = T₁
  generalize (∏' n : ℕ, (1 - (q : k) ^ (n + 1) * (u : k)⁻¹)) = T₂
  ring

/-- The inversion symmetry `θ(u⁻¹) = -u⁻¹·θ(u)`: swapping the two products exchanges
`1 - u` for `1 - u⁻¹`. -/
theorem TateCurve.tateTheta_inv (q : kˣ) (hq : valuation k (q : k) < 1) (u : kˣ) :
    tateTheta ((u : k)⁻¹) (q : k) = -(u : k)⁻¹ * tateTheta (u : k) (q : k) := by
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hBinv : (∏' n : ℕ, (1 - (q : k) ^ (n + 1) * ((u : k)⁻¹)⁻¹)) =
      ∏' n : ℕ, (1 - (q : k) ^ (n + 1) * u) :=
    tprod_congr fun n ↦ by rw [inv_inv]
  have hq0 : (q : k) ≠ 0 := Units.ne_zero q
  have htailA : Multipliable fun n : ℕ ↦ 1 - (q : k) ^ (n + 1) * (u : k) :=
    (multipliable_tateTheta (q : k) hq ((q : k) * u)).congr fun n ↦ by ring
  have htailB : Multipliable fun n : ℕ ↦ 1 - (q : k) ^ (n + 1) * (u : k)⁻¹ :=
    (multipliable_tateTheta (q : k) hq ((q : k) * (u : k)⁻¹)).congr fun n ↦ by ring
  have hsplitA : (∏' n : ℕ, (1 - (q : k) ^ n * u)) =
      (1 - (u : k)) * ∏' n : ℕ, (1 - (q : k) ^ (n + 1) * u) := by
    simpa using tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 - (q : k) ^ n * (u : k)) htailA
  have hsplitB : (∏' n : ℕ, (1 - (q : k) ^ n * (u : k)⁻¹)) =
      (1 - (u : k)⁻¹) * ∏' n : ℕ, (1 - (q : k) ^ (n + 1) * (u : k)⁻¹) := by
    simpa using tprod_eq_zero_mul' (f := fun n : ℕ ↦ 1 - (q : k) ^ n * (u : k)⁻¹) htailB
  have hscal : (1 : k) - (u : k)⁻¹ = -(u : k)⁻¹ * (1 - (u : k)) := by
    field_simp
    ring
  simp only [tateTheta]
  rw [hBinv, hsplitB, hsplitA, hscal]
  generalize (∏' n : ℕ, (1 - (q : k) ^ (n + 1) * (u : k))) = T₁
  generalize (∏' n : ℕ, (1 - (q : k) ^ (n + 1) * (u : k)⁻¹)) = T₂
  ring

/-- The zero set of `θ(·, q)` on `kˣ` is exactly `qᶻ`. On the fundamental annulus
`|q| < |u| ≤ 1` every factor other than `1 - u` has valuation `1` and the product of
these units is a unit (a leading-term argument as in `valuation_evalInt_eq`), so the
only zero is `u = 1`; the functional equation `tateTheta_mul_left` transports this to
every annulus `|q|ⁿ⁺¹ < |u| ≤ |q|ⁿ`. -/
theorem TateCurve.tateTheta_eq_zero_iff (q : kˣ) (hq : valuation k (q : k) < 1)
    (u : kˣ) :
    tateTheta (u : k) (q : k) = 0 ↔ u ∈ Subgroup.zpowers q := by
  have hq0 : (q : k) ≠ 0 := Units.ne_zero q
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hvq : valuation k (q : k) ≠ 0 := (valuation k).ne_zero_iff.mpr hq0
  have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr hu0
  constructor
  · intro h0
    by_contra hmem
    -- the first product is nonzero: finitely many honest factors, unit tail
    have hAmul : Multipliable fun n : ℕ ↦ 1 - (q : k) ^ n * u :=
      multipliable_tateTheta (q : k) hq (u : k)
    obtain ⟨N, hN⟩ := exists_pow_lt hq (Units.mk0 (valuation k (u : k))⁻¹
      (inv_ne_zero hvu))
    have hδ : valuation k (q : k) ^ N * valuation k (u : k) < 1 := by
      have h := mul_pow_lt (C := valuation k (u : k)) hvu (γ := 1)
        (by rw [mul_one]; exact hN)
      rwa [mul_comm] at h
    have htailAmul : Multipliable fun n : ℕ ↦ 1 - (q : k) ^ (n + N) * (u : k) :=
      (multipliable_tateTheta (q : k) hq ((q : k) ^ N * u)).congr fun n ↦ by ring
    have htailv : valuation k (∏' n : ℕ, (1 - (q : k) ^ (n + N) * u)) = 1 := by
      refine valuation_tprod_one_sub_eq_one hδ (fun n ↦ ?_) htailAmul
      rw [map_mul, map_pow]
      exact mul_le_mul' (pow_le_pow_right_of_le_one' hq.le (by omega)) le_rfl
    have hA : (∏' n : ℕ, (1 - (q : k) ^ n * u)) ≠ 0 := by
      rw [← Multipliable.prod_mul_tprod_nat_mul'
        (f := fun n : ℕ ↦ 1 - (q : k) ^ n * (u : k)) (k := N) htailAmul]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun n _ h ↦ ?_)
        ((valuation k).ne_zero_iff.mp (by rw [htailv]; exact one_ne_zero))
      refine hmem ⟨-(n : ℤ), Units.ext ?_⟩
      rw [Units.val_zpow_eq_zpow_val, zpow_neg, zpow_natCast]
      exact (eq_inv_of_mul_eq_one_right ((sub_eq_zero.mp h).symm)).symm
    -- the second product is nonzero
    obtain ⟨N', hN'⟩ := exists_pow_lt hq (Units.mk0 (valuation k (u : k)) hvu)
    have hδ' : valuation k (q : k) ^ N' * (valuation k (u : k))⁻¹ < 1 := by
      have h := mul_pow_lt (C := (valuation k (u : k))⁻¹) (inv_ne_zero hvu) (γ := 1)
        (by rw [inv_inv, mul_one]; exact hN')
      rwa [mul_comm] at h
    have htailBmul : Multipliable fun n : ℕ ↦ 1 - (q : k) ^ (n + N' + 1) * (u : k)⁻¹ :=
      (multipliable_tateTheta (q : k) hq ((q : k) ^ (N' + 1) * (u : k)⁻¹)).congr
        fun n ↦ by ring
    have htailv' : valuation k (∏' n : ℕ, (1 - (q : k) ^ (n + N' + 1) * (u : k)⁻¹))
        = 1 := by
      refine valuation_tprod_one_sub_eq_one hδ' (fun n ↦ ?_) htailBmul
      rw [map_mul, map_pow, map_inv₀]
      exact mul_le_mul' (pow_le_pow_right_of_le_one' hq.le (by omega)) le_rfl
    have hB : (∏' n : ℕ, (1 - (q : k) ^ (n + 1) * (u : k)⁻¹)) ≠ 0 := by
      rw [← Multipliable.prod_mul_tprod_nat_mul'
        (f := fun n : ℕ ↦ 1 - (q : k) ^ (n + 1) * (u : k)⁻¹) (k := N') htailBmul]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun n _ h ↦ ?_) ?_
      · refine hmem ⟨((n : ℤ) + 1), Units.ext ?_⟩
        rw [Units.val_zpow_eq_zpow_val,
          show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
        have h2 := eq_inv_of_mul_eq_one_right ((sub_eq_zero.mp h).symm)
        rw [← inv_inj]
        exact h2.symm
      · exact (valuation k).ne_zero_iff.mp (by rw [htailv']; exact one_ne_zero)
    simp only [tateTheta] at h0
    exact mul_ne_zero hA hB h0
  · rintro ⟨m, rfl⟩
    simp only [tateTheta]
    rcases le_or_gt m 0 with hm | hm
    · have hn : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (neg_nonneg.mpr hm)
      have hfac : 1 - (q : k) ^ ((-m).toNat) * ((q ^ m : kˣ) : k) = 0 := by
        rw [Units.val_zpow_eq_zpow_val, ← zpow_natCast (q : k) ((-m).toNat), hn,
          ← zpow_add₀ hq0, neg_add_cancel, zpow_zero, sub_self]
      rw [tprod_eq_zero _ hfac, zero_mul]
    · have hn : ((m - 1).toNat : ℤ) = m - 1 := Int.toNat_of_nonneg (by omega)
      have hfac : 1 - (q : k) ^ ((m - 1).toNat + 1) * (((q ^ m : kˣ) : k))⁻¹ = 0 := by
        rw [Units.val_zpow_eq_zpow_val, ← zpow_natCast (q : k) ((m - 1).toNat + 1),
          show ((((m - 1).toNat + 1 : ℕ)) : ℤ) = m from by push_cast [hn]; ring,
          ← zpow_neg, ← zpow_add₀ hq0, add_neg_cancel, zpow_zero, sub_self]
      rw [tprod_eq_zero (f := fun n : ℕ ↦ 1 - (q : k) ^ (n + 1) * (((q ^ m : kˣ) : k))⁻¹)
        ((m - 1).toNat) hfac, mul_zero]

/-! ### Stage 3: the difference identity and injectivity -/

/-- The difference of `x`-coordinates as a theta quotient:
`X(u) - X(v) = -v·θ(uv)·θ(u/v) / (θ(u)²·θ(v)²)`. This is the Tate-curve form of the
classical `σ`-function identity `℘(z₁) - ℘(z₂) = -σ(z₁+z₂)σ(z₁-z₂)/(σ(z₁)²σ(z₂)²)`;
the normalising factor `-v` is fixed by the `q⁰`-coefficient, where both sides reduce
to `(u - v)(1 - uv)/((1-u)²(1-v)²)`. The proof is a bridge identity in the two-variable
coefficient ring `ℤ[t₁±, t₂±, (1-t₁)⁻¹, (1-t₂)⁻¹]`, descended as in
`TateCurveDescent` and evaluated by the `evalK` calculus. -/
theorem WeierstrassCurve.tateX_sub_tateX (q : kˣ) (hq : valuation k (q : k) < 1)
    (u v : kˣ) (hu : u ∉ Subgroup.zpowers q) (hv : v ∉ Subgroup.zpowers q) :
    tateX (u : k) (q : k) - tateX (v : k) (q : k) =
      -(v : k) * (TateCurve.tateTheta ((u : k) * (v : k)) (q : k) *
          TateCurve.tateTheta ((u : k) * (v : k)⁻¹) (q : k)) /
        (TateCurve.tateTheta (u : k) (q : k) ^ 2 *
          TateCurve.tateTheta (v : k) (q : k) ^ 2) :=
  sorry

/-- Injectivity of the Tate uniformisation, in `iff` form (the `←` direction is
`tateCurvePoint_eq`, already proved). For `→`: equal points have equal
`x`-coordinates, so `θ(uv)θ(u/v) = 0` by `tateX_sub_tateX` (the denominator is
nonzero by `tateTheta_eq_zero_iff`), hence `v ≡ u^{±1} (mod qᶻ)`; the case
`v ≡ u⁻¹ ≢ u` is excluded by comparing `y`-coordinates via `tateY_inv`, except at
`2`-torsion (`u² ∈ qᶻ`) where the two cases coincide. -/
theorem WeierstrassCurve.tateCurvePoint_eq_iff (q : kˣ) (hq : valuation k (q : k) < 1)
    (u v : kˣ) :
    tateCurvePoint q hq u = tateCurvePoint q hq v ↔ u⁻¹ * v ∈ Subgroup.zpowers q :=
  sorry

/-! ### Stage 4: the addition law -/

/-- The generic addition law for the `x`-coordinate: for `u, v, uv ∉ qᶻ` with
`X(u) ≠ X(v)`, the chord construction on `y² + xy = x³ + a₄x + a₆` gives
`X(uv) = λ² + λ - X(u) - X(v)` with `λ` the chord slope (this matches
`WeierstrassCurve.Affine.addX` with `a₁ = 1`, `a₂ = 0`). A bridge identity in the
two-variable coefficient ring, whose analytic input over `ℂ` is the addition theorem
for the Weierstrass `℘`-function. -/
theorem WeierstrassCurve.tateX_mul_of_ne (q : kˣ) (hq : valuation k (q : k) < 1)
    (u v : kˣ) (hu : u ∉ Subgroup.zpowers q) (hv : v ∉ Subgroup.zpowers q)
    (huv : u * v ∉ Subgroup.zpowers q)
    (hX : tateX (u : k) (q : k) ≠ tateX (v : k) (q : k)) :
    tateX ((u : k) * (v : k)) (q : k) =
      ((tateY (u : k) (q : k) - tateY (v : k) (q : k)) /
          (tateX (u : k) (q : k) - tateX (v : k) (q : k))) ^ 2 +
        (tateY (u : k) (q : k) - tateY (v : k) (q : k)) /
          (tateX (u : k) (q : k) - tateX (v : k) (q : k)) -
        tateX (u : k) (q : k) - tateX (v : k) (q : k) :=
  sorry

/-- The generic addition law for the `y`-coordinate: with `λ` the chord slope,
`Y(uv) = -(Y(u) + λ(X(uv) - X(u))) - X(uv)` (the chord's third intersection point,
negated; matches `WeierstrassCurve.Affine.addY`). -/
theorem WeierstrassCurve.tateY_mul_of_ne (q : kˣ) (hq : valuation k (q : k) < 1)
    (u v : kˣ) (hu : u ∉ Subgroup.zpowers q) (hv : v ∉ Subgroup.zpowers q)
    (huv : u * v ∉ Subgroup.zpowers q)
    (hX : tateX (u : k) (q : k) ≠ tateX (v : k) (q : k)) :
    tateY ((u : k) * (v : k)) (q : k) =
      -(tateY (u : k) (q : k) +
          (tateY (u : k) (q : k) - tateY (v : k) (q : k)) /
            (tateX (u : k) (q : k) - tateX (v : k) (q : k)) *
            (tateX ((u : k) * (v : k)) (q : k) - tateX (u : k) (q : k))) -
        tateX ((u : k) * (v : k)) (q : k) :=
  sorry

open scoped Classical in
/-- Full additivity of the Tate uniformisation on representatives. Derivation: on
generic pairs, `tateX_mul_of_ne` and `tateY_mul_of_ne` say precisely that
`φ(uv) = φ(u) + φ(v)` for mathlib's group law on `E_q(k)` (`Affine.Point.add` in the
`x₁ ≠ x₂` case); the vertical case is Stage 1; the remaining degenerate pairs follow
by `TateCurve.map_mul_of_generic`, choosing `w` outside the finitely many excluded
`qᶻ`-cosets (`kˣ/qᶻ` is infinite). -/
theorem WeierstrassCurve.tateCurvePoint_mul (q : kˣ) (hq : valuation k (q : k) < 1)
    (u v : kˣ) :
    tateCurvePoint q hq (u * v) = tateCurvePoint q hq u + tateCurvePoint q hq v :=
  sorry

/-! ### Stage 5: surjectivity -/

/-- Existence of a parameter for every attained `x`-coordinate: the surjectivity
kernel. For `(x, y) ∈ E_q(k)`, the theta-type function `f(u) = X(u) - x` satisfies
`f(qu) = f(u)` and has "degree 2", so a nonarchimedean Abel-type zero count (Newton
polygon of the two-sided coefficient sequence, made eventually strictly convex by the
functional equation) produces a zero `u` in a finite extension; Galois stability of
`{u, u⁻¹} mod qᶻ` and `y ∈ k` then force `u ∈ k` for one of the pair. -/
theorem WeierstrassCurve.exists_tateCurvePoint_eq (q : kˣ)
    (hq : valuation k (q : k) < 1) (P : ((tateCurve (q : k))⁄k).Point) :
    ∃ u : kˣ, tateCurvePoint q hq u = P :=
  sorry

end
