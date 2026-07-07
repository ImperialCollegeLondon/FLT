/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Mathlib.Topology.Instances.Int
public import FLT.Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import FLT.Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

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
consistently with the other series in Tate's theory (`tateA₄`, `tateA₆`, …). Only a field
and a topology are needed to *state* the definition, so it applies verbatim in the rank 1
generality (`ℂ_p`, completed maximal unramified extensions, …).

The interaction with the valuation — for `|j| > 1` the series converges with valuation
exactly `|j|⁻¹`, so `tateParameter j` lies in the punctured open unit disc — is proved in
`FLT.KnownIn1980s.EllipticCurves.TateCurve` (`WeierstrassCurve.valuation_tateParameter_eq`),
where the Tate parameter `WeierstrassCurve.q` of an elliptic curve is defined. The
characterising properties — `j(tateParameter j) = j` for `|j| > 1` and
`tateParameter (j(q)) = q` for `0 < |q| < 1` (the two halves of Silverman V.5.2) — are
future work there: their proofs will combine the formal identity `subst_jInvReverse` of
Step 2 with the usual formal-to-convergent bridge (evaluation of a formal `subst` identity
at a point where all the series converge).

Because the coefficients are universal integers, `tateParameter` commutes with every
continuous morphism of topological fields; this is what makes the Tate parameter functorial
(`WeierstrassCurve.q_baseChange`) with no uniqueness argument at the level of `k`.
-/

@[expose] public section

open scoped ArithmeticFunction.sigma -- `σ k n` notation for the sum of the `k`th powers
                                     -- of the divisors of `n`
open scoped PowerSeries.WithPiTopology -- the `X`-adic (coefficientwise) topology on
                                       -- `ℤ⟦X⟧`, giving meaning to `∏'`
open ValuativeRel -- `𝒪[k]` notation for the ring of integers of `k`, and `valuation`

namespace TateCurve

open PowerSeries

/-! ### Step 1: the formal series `1/j ∈ ℤ⟦q⟧` -/

/-- The formal series `sₖ(q) = ∑_{n≥1} σₖ(n)qⁿ ∈ ℤ⟦q⟧` (integer-coefficient version of
`TateCurve.s`; recall `σₖ(0) = 0`). -/
noncomputable def sInt (k : ℕ) : ℤ⟦X⟧ := .mk fun n ↦ (σ k n : ℤ)

/-- The formal `c₄`-series `c₄(q) = 1 + 240s₃(q) = 1 + 240q + 2160q² + ⋯ ∈ ℤ⟦q⟧` of the
Tate curve: the `q`-expansion of the Eisenstein series `E₄`. -/
noncomputable def c₄Formal : ℤ⟦X⟧ := 1 + 240 * sInt 3

/-- The formal discriminant `Δ(q) = q∏_{n≥1}(1 - qⁿ)²⁴ ∈ ℤ⟦q⟧` of the Tate curve: the
`q`-expansion of the modular discriminant, `∑ τ(n)qⁿ` with `τ` Ramanujan's tau. The
product is a `tprod` in the `X`-adic topology, multipliable by
`PowerSeries.WithPiTopology.multipliable_one_sub_X_pow`. -/
noncomputable def ΔFormal : ℤ⟦X⟧ := X * (∏' n : ℕ, (1 - X ^ (n + 1))) ^ 24

/-- The formal series `1/j = Δ(q)/c₄(q)³ = q - 744q² + 356652q³ - ⋯ ∈ ℤ⟦q⟧`: the
reciprocal of the `j`-invariant of the Tate curve. Since `c₄³` has constant coefficient
`1` its inverse `PowerSeries.invOfUnit (c₄Formal ^ 3) 1` has integer coefficients: no
denominators are introduced. -/
noncomputable def jInv : ℤ⟦X⟧ := ΔFormal * invOfUnit (c₄Formal ^ 3) 1

@[simp]
theorem constantCoeff_jInv : constantCoeff jInv = 0 := by
  simp [jInv, ΔFormal]

theorem coeff_one_jInv : coeff 1 jInv = 1 := by
  simp [jInv, ΔFormal, mul_assoc, map_mul, map_pow,
    (WithPiTopology.multipliable_one_sub_X_pow ℤ).map_tprod _
    (WithPiTopology.continuous_constantCoeff ℤ), constantCoeff_invOfUnit]

/-! ### Step 2: formal compositional inversion -/

/-- The linear coefficient of `jInv` is (invertibly) `1`: the hypothesis under which
mathlib's compositional inversion `PowerSeries.substInv` applies. -/
noncomputable instance : Invertible (coeff 1 jInv) := invertibleOne.copy _ coeff_one_jInv

/-- The formal inverse `j`-series
`ψ = X + 744X² + 750420X³ + 872769632X⁴ + ⋯ ∈ ℤ⟦X⟧`: the compositional inverse
`PowerSeries.substInv` of `jInv`, so that formally `q = ψ(1/j)` (Silverman, ATAEC
V.5.2 — the integrality of the coefficients is by construction, see the module
docstring). -/
noncomputable def jInvReverse : ℤ⟦X⟧ := substInv jInv

/-- The defining property of `jInvReverse`: `ψ(jInv(q)) = q` as formal power series. This
is the identity from which both halves of Silverman V.5.2 follow by evaluation. -/
theorem subst_jInvReverse : PowerSeries.subst jInv jInvReverse = X :=
  subst_substInv_left jInv constantCoeff_jInv

/-- The composition in the other order: `jInv(ψ(w)) = w` as formal power series. -/
theorem jInv_subst_jInvReverse : PowerSeries.subst jInvReverse jInv = X :=
  subst_substInv_right jInv constantCoeff_jInv

@[simp]
theorem constantCoeff_jInvReverse : constantCoeff jInvReverse = 0 := constantCoeff_substInv jInv

@[simp]
theorem coeff_one_jInvReverse : coeff 1 jInvReverse = 1 := by
  simpa [jInvReverse, coeff_one_substInv] using invOf_eq_right_inv (by rw [coeff_one_jInv, mul_one])

/-! ### Evaluation of integral power series

The bridge from the formal world to a topological field `k`: `evalInt q F = ∑ₙ Fₙqⁿ`.
Only a field and a topology are needed for the definition and its formal properties;
over a nonarchimedean local field and `|q| < 1`, every `F ∈ ℤ⟦X⟧` is evaluable
(integers have norm `≤ 1`, so the terms tend to zero — `summable_evalInt` below), and
the evaluation obeys the ultrametric estimates `valuation_evalInt_le_pow` and
`valuation_evalInt_eq`.
-/

section Evaluation

variable {k : Type*} [Field k] [TopologicalSpace k]

/-- The evaluation `∑ₙ Fₙqⁿ ∈ k` of an integral power series `F ∈ ℤ⟦X⟧` at a point `q` of
a topological field (junk value if the series does not converge). -/
noncomputable def evalInt (q : k) (F : ℤ⟦X⟧) : k := ∑' n : ℕ, ((coeff n F : ℤ) : k) * q ^ n

@[simp]
theorem evalInt_X (q : k) : evalInt q (X : ℤ⟦X⟧) = q := by
  simp [evalInt, coeff_X]

section

variable [IsTopologicalRing k] [T2Space k]

theorem evalInt_add {q : k} {F G : ℤ⟦X⟧} (hF : Summable fun n ↦ ((coeff n F : ℤ) : k) * q ^ n)
    (hG : Summable fun n ↦ ((coeff n G : ℤ) : k) * q ^ n) :
    evalInt q (F + G) = evalInt q F + evalInt q G := by
  simpa [evalInt, map_add, Int.cast_add, add_mul] using hF.tsum_add hG

end

-- now let k be a nonarchimedean local field
variable [ValuativeRel k] [IsNonarchimedeanLocalField k]

/-- Every integral power series is evaluable on the open unit disc of a nonarchimedean
local field: integers have valuation at most `1`, so the terms have valuation at most
`|q|ⁿ → 0`, and a series whose terms tend to zero converges, by completeness and the
nonarchimedean property (no absolute convergence is needed — contrast the archimedean
case). -/
theorem summable_evalInt (q : k) (hq : valuation k q < 1) (F : ℤ⟦X⟧) :
    Summable fun n ↦ ((PowerSeries.coeff n F : ℤ) : k) * q ^ n := by
  -- `Summable` only sees the topology, but the completeness criterion below is stated for
  -- uniform spaces: equip `k` with its canonical uniformity
  letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  haveI : NonarchimedeanRing k := by
    convert! ValuativeRel.nonarchimedeanRing k
    exact Valuation.toTopologicalSpace_eq _
  -- in a complete nonarchimedean group, it suffices that the terms tend to zero
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, (IsValuativeTopology.hasBasis_nhds (0 : k)).tendsto_right_iff]
  intro γ _
  obtain ⟨N, hN⟩ := exists_pow_valuation_lt q hq γ
  -- from `n ≥ N` on, the terms have valuation `≤ |q|ⁿ ≤ |q|^N < γ`
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  simp only [sub_zero, map_mul, map_pow]
  calc valuation k ((PowerSeries.coeff n F : ℤ) : k) * valuation k q ^ n
      ≤ 1 * valuation k q ^ n := mul_le_mul_left (valuation_intCast_le_one _) _
    _ = valuation k q ^ n := one_mul _
    _ ≤ valuation k q ^ N := pow_le_pow_right_of_le_one' hq.le hn
    _ < γ := hN

/-- If the first `M` coefficients of `F` vanish, its evaluation at a point of the open
unit disc has valuation at most `|q|^M`: the partial sums satisfy the bound by the
nonarchimedean triangle inequality, and it passes to the limit by the ultrametric
isosceles principle (if `v(σ - T) < v(T)` and `v(σ) < v(T)` then
`v(T) ≤ max(v(σ), v(σ - T)) < v(T)`, absurd). -/
theorem valuation_evalInt_le_pow (q : k) (hq : valuation k q < 1) {F : ℤ⟦X⟧}
    {M : ℕ} (hF : ∀ m < M, PowerSeries.coeff m F = 0) :
    valuation k (evalInt q F) ≤ valuation k q ^ M := by
  by_contra hlt
  rw [not_le] at hlt
  -- the partial sums satisfy the bound
  have hpart : ∀ s : Finset ℕ,
      valuation k (∑ n ∈ s, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n) ≤
        valuation k q ^ M := by
    intro s
    refine Valuation.map_sum_le _ fun n _ ↦ ?_
    rcases lt_or_ge n M with h | h
    · simp [hF n h]
    · rw [map_mul, map_pow]
      calc valuation k ((PowerSeries.coeff n F : ℤ) : k) * valuation k q ^ n
          ≤ 1 * valuation k q ^ n := mul_le_mul_left (valuation_intCast_le_one _) _
        _ = valuation k q ^ n := one_mul _
        _ ≤ valuation k q ^ M := pow_le_pow_right_of_le_one' hq.le h
  -- some partial sum is closer to the limit than `v(evalInt q F)`
  have hS : HasSum (fun n : ℕ ↦ ((PowerSeries.coeff n F : ℤ) : k) * q ^ n) (evalInt q F) :=
    (summable_evalInt q hq F).hasSum
  simp only [HasSum, SummationFilter.unconditional_filter,
    (IsValuativeTopology.hasBasis_nhds (evalInt q F)).tendsto_right_iff] at hS
  obtain ⟨s, hs⟩ :=
    (hS (Units.mk0 _ (ne_of_gt (lt_of_le_of_lt zero_le hlt))) trivial).exists
  simp only [Set.mem_setOf_eq] at hs
  refine absurd ?_ (lt_irrefl (valuation k (evalInt q F)))
  calc valuation k (evalInt q F)
      = valuation k ((∑ n ∈ s, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n) -
          ((∑ n ∈ s, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n) - evalInt q F)) := by
        rw [sub_sub_cancel]
    _ ≤ max (valuation k (∑ n ∈ s, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n))
          (valuation k ((∑ n ∈ s, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n) -
            evalInt q F)) := Valuation.map_sub _ _ _
    _ < valuation k (evalInt q F) := max_lt (lt_of_le_of_lt (hpart s) hlt) hs

/-- The leading-term principle: if `F = X + O(X²)` then `|F(q)| = |q|` on the punctured
open unit disc — ultrametrically the leading term dominates the tail, which has valuation
at most `|q|²` by `valuation_evalInt_le_pow`. -/
theorem valuation_evalInt_eq (q : k) (hq0 : q ≠ 0) (hq : valuation k q < 1)
    {F : ℤ⟦X⟧} (h0 : PowerSeries.constantCoeff F = 0) (h1 : PowerSeries.coeff 1 F = 1) :
    valuation k (evalInt q F) = valuation k q := by
  have hsplit : evalInt q F = q + evalInt q (F - PowerSeries.X) := by
    conv_lhs => rw [show F = PowerSeries.X + (F - PowerSeries.X) by ring]
    rw [evalInt_add (summable_evalInt q hq _) (summable_evalInt q hq _), evalInt_X]
  have hlow : ∀ m < 2, PowerSeries.coeff m (F - PowerSeries.X) = 0 := by
    intro m hm
    rcases m with - | - | m
    · simp [PowerSeries.coeff_zero_eq_constantCoeff, h0]
    · simp [h1, PowerSeries.coeff_X]
    · exact absurd hm (by omega)
  have hr : valuation k (evalInt q (F - PowerSeries.X)) < valuation k q :=
    lt_of_le_of_lt (valuation_evalInt_le_pow q hq hlow)
      (pow_lt_self_of_lt_one₀ (zero_lt_iff.mpr ((valuation k).ne_zero_iff.mpr hq0)) hq one_lt_two)
  rw [hsplit, (valuation k).map_add_eq_of_lt_left hr]

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
then a round-trip identity (`tateParameter (j(q)) = q`, future work), and no choice is
involved anywhere. -/
noncomputable def WeierstrassCurve.tateParameter (j : k) : k :=
  TateCurve.evalInt j⁻¹ TateCurve.jInvReverse
