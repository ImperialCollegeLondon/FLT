import Mathlib

/-!

# The power series identity underlying the construction of the Tate curve

If `k` is a nonarchimedean local field and `q ∈ kˣ` has `|q| < 1`, then Tate showed
that `kˣ/qᶻ` is the group of `k`-points of an elliptic curve `E_q/k` with Weierstrass
equation `y² + xy = x³ + a₄(q)x + a₆(q)`, for certain explicit power series `a₄` and
`a₆` in `q` with integer coefficients; the map `kˣ → E_q(k)` is given by explicit
power series `X(u,q)` and `Y(u,q)` in `q` whose coefficients are Laurent polynomials
in `u`.

The purely algebraic input to this construction is the identity
`Y² + XY = X³ + a₄X + a₆` in `ℚ(u)⟦q⟧`, which this file states. The identity can be
extracted from Theorem V.1.1 of [Silverman, *Advanced topics in the arithmetic of
elliptic curves*], where it is deduced from the complex-analytic theory of the
Weierstrass ℘-function. See
https://mathoverflow.net/questions/469021/low-level-proof-of-identity-related-to-weierstrass-p-function

## Implementation notes

We work in `(RatFunc ℚ)⟦X⟧`, formal power series over the field `ℚ(u)` of rational
functions. Beware of the clash of notation: the power series variable (written `q`
above and in the references) is `PowerSeries.X`, whereas the rational function
variable `u` is `RatFunc.X`, and neither has anything to do with the coordinate `X`
on the curve, which is the power series `TateCurve.X` defined below.

-/

open scoped PowerSeries -- `R⟦X⟧` notation for `PowerSeries R`

open scoped ArithmeticFunction.sigma -- `σ k n` notation for the sum of the `k`th
                                     -- powers of the positive divisors of `n`

noncomputable section

namespace TateCurve

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

/-- The point `(X(u,q), Y(u,q))` satisfies the Weierstrass equation
`y² + xy = x³ + a₄x + a₆` of the Tate curve, as an identity in `ℚ(u)⟦q⟧`.
-/
theorem weierstrass_equation : Y ^ 2 + X * Y = X ^ 3 + a₄ * X + a₆ :=
  sorry

/-
This is a straightforward calculation using Theorem V.1.1(a) of
[Silverman, *Advanced topics in the arithmetic of elliptic curves*].
(see also the proof of V.3.1(c), and in particular the comment
"In other words, we want to verify that this identity holds in
the ring ℚ(u)[[q]]".

Note that this identity in ℚ(u)[[X]] is checked modulo X^3 in
the file `TateCurveConstructionExperiment.lean`, which can be deleted
when this theorem is proved. This gives us confidence
that there is no typo here.
-/

end TateCurve
