/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Yin
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurveUniformisation
public import FLT.KnownIn1980s.EllipticCurves.TateCurveBaseChange

/-!
# Functoriality of the Tate curve coordinates in a continuous field morphism

The defining series of Tate's theory — the coefficients `tateA₄`, `tateA₆` of the Tate
curve and the coordinates `tateX`, `tateY` of its uniformisation — have universal
(integer) coefficients, so they commute with every continuous morphism `f : k →+* l` of
nonarchimedean local fields: a continuous ring homomorphism maps a convergent sum
termwise to a convergent sum (`HasSum.map`), and `f` transforms each term of the series
over `k` into the corresponding term over `l`.

This file proves these transport identities in the generality of an arbitrary continuous
ring homomorphism `f`, which covers the two consumers at once:

* the structure map `algebraMap k l` of a valuative extension, which is continuous by
  `ValuativeExtension.continuous_algebraMap` — this gives the base-change functoriality
  of Tate's uniformisation (`WeierstrassCurve.tateEquiv_baseChange`);
* a continuous `k`-algebra automorphism `σ` of `l` — this gives Galois equivariance
  (`WeierstrassCurve.tateEquiv_galois`).

Compare `TateCurve.evalInt_map` (in `TateCurveBaseChange`), which proves the
`algebraMap` case of `evalInt_map_of_continuous` by a quantitative partial-sum argument
that avoids continuity; here continuity is available, and the `HasSum.map` route also
handles the two-sided coordinate series `tateX`, `tateY`, which are not `evalInt`s.

On the hypotheses `|q| < 1` and `|f q| < 1`: see the docstring of
`WeierstrassCurve.tateCurve_baseChange` for why the source-side hypothesis is the honest
convergence hypothesis and costs nothing; the target-side hypothesis `|f q| < 1` is used
to re-express the transported sums as the defining (Lambert-type) series over `l`, and
is automatic for both consumers (for `algebraMap` by `valuation_algebraMap_lt_one`, for
`σ` because `σ q = q`).
-/

@[expose] public section

open ValuativeRel

open scoped PowerSeries

-- let k and l be nonarchimedean local fields, and let f : k → l be a continuous ring
-- homomorphism (not necessarily an isometry or a valuative extension)
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
variable {l : Type*} [Field l] [ValuativeRel l] [TopologicalSpace l]
  [IsNonarchimedeanLocalField l]
variable (f : k →+* l) (hf : Continuous f)

namespace TateCurve

include hf in
/-- Evaluation of integral power series on the open unit disc commutes with a continuous
ring homomorphism: the coefficients are (the same) integers on both sides, and a
continuous ring homomorphism maps the convergent sum termwise (`HasSum.map`). Compare
`TateCurve.evalInt_map`, which proves this for `algebraMap k l` of a valuative extension
by a quantitative argument avoiding continuity. -/
theorem evalInt_map_of_continuous {q : k} (hq : valuation k q < 1) (F : ℤ⟦X⟧) :
    f (evalInt q F) = evalInt (f q) F := by
  simp only [evalInt]
  rw [(summable_evalInt q hq F).map_tsum f hf]
  exact tsum_congr fun n ↦ by rw [map_mul, map_intCast, map_pow]

end TateCurve

-- The correction series `s₁(q) = ∑_{n≥1} nqⁿ/(1-qⁿ)` of `tateX`/`tateY` is the
-- evaluation of the integral power series `∑ σ₁(N)qᴺ`, by the Lambert rearrangement.
private theorem tateS₁_eq_evalInt {k : Type*} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : k) (hq : valuation k q < 1) :
    ∑' n : ℕ, ((n + 1 : ℕ) : k) * q ^ (n + 1) / (1 - q ^ (n + 1)) =
      TateCurve.evalInt q (TateCurve.sInt 1) := by
  have hF : ∀ n, PowerSeries.coeff n (TateCurve.sInt 1) = ∑ d ∈ n.divisors, (d : ℤ) := by
    intro n
    rw [TateCurve.sInt, PowerSeries.coeff_mk, ArithmeticFunction.sigma_apply]
    push_cast
    simp
  rw [← TateCurve.tsum_lambert_eq_evalInt q hq _ hF]
  exact tsum_congr fun m ↦ by push_cast; ring

namespace WeierstrassCurve

include hf in
/-- The coefficient `a₄(q)` of the Tate curve commutes with a continuous ring
homomorphism of nonarchimedean local fields. -/
theorem tateA₄_map_of_continuous {q : k} (hq : valuation k q < 1)
    (hq' : valuation l (f q) < 1) :
    f (tateA₄ q) = tateA₄ (f q) := by
  rw [tateA₄_eq_evalInt q hq, tateA₄_eq_evalInt (f q) hq',
    TateCurve.evalInt_map_of_continuous f hf hq]

include hf in
/-- The coefficient `a₆(q)` of the Tate curve commutes with a continuous ring
homomorphism of nonarchimedean local fields. -/
theorem tateA₆_map_of_continuous {q : k} (hq : valuation k q < 1)
    (hq' : valuation l (f q) < 1) :
    f (tateA₆ q) = tateA₆ (f q) := by
  rw [tateA₆_eq_evalInt q hq, tateA₆_eq_evalInt (f q) hq',
    TateCurve.evalInt_map_of_continuous f hf hq]

include hf in
/-- The Tate curve commutes with a continuous ring homomorphism of nonarchimedean local
fields. Compare `WeierstrassCurve.tateCurve_baseChange`, the `algebraMap` special
case. -/
theorem tateCurve_map_of_continuous {q : k} (hq : valuation k q < 1)
    (hq' : valuation l (f q) < 1) :
    (tateCurve q).map f = tateCurve (f q) := by
  ext <;> simp [WeierstrassCurve.map, tateCurve, tateA₄_map_of_continuous f hf hq hq',
    tateA₆_map_of_continuous f hf hq hq']

include hf in
/-- The coordinate `X(u, q)` of Tate's uniformisation commutes with a continuous ring
homomorphism of nonarchimedean local fields: the two-sided series is mapped termwise
(`HasSum.map` applied to `TateCurve.summable_tateX_int`), and the correction series
`2s₁(q)` is an integral power-series evaluation (`TateCurve.tsum_lambert_eq_evalInt`
applied to `TateCurve.sInt 1`), which transports by `evalInt_map_of_continuous`. -/
theorem tateX_map_of_continuous (q u : kˣ) (hq : valuation k (q : k) < 1)
    (hq' : valuation l (f (q : k)) < 1) :
    f (tateX (u : k) (q : k)) = tateX (f (u : k)) (f (q : k)) := by
  simp only [tateX]
  rw [map_sub, map_mul, map_ofNat]
  congr 1
  · rw [(TateCurve.summable_tateX_int q u hq).map_tsum f hf]
    exact tsum_congr fun n ↦ by
      rw [map_div₀, map_mul, map_zpow₀, map_pow, map_sub, map_one, map_mul, map_zpow₀]
  · congr 1
    rw [tateS₁_eq_evalInt (q : k) hq, TateCurve.evalInt_map_of_continuous f hf hq,
      tateS₁_eq_evalInt (f (q : k)) hq']

include hf in
/-- The coordinate `Y(u, q)` of Tate's uniformisation commutes with a continuous ring
homomorphism of nonarchimedean local fields; as `tateX_map_of_continuous`. -/
theorem tateY_map_of_continuous (q u : kˣ) (hq : valuation k (q : k) < 1)
    (hq' : valuation l (f (q : k)) < 1) :
    f (tateY (u : k) (q : k)) = tateY (f (u : k)) (f (q : k)) := by
  simp only [tateY]
  rw [map_add]
  congr 1
  · rw [(TateCurve.summable_tateY_int q u hq).map_tsum f hf]
    exact tsum_congr fun n ↦ by
      rw [map_div₀, map_pow, map_mul, map_zpow₀, map_pow, map_sub, map_one, map_mul,
        map_zpow₀]
  · rw [tateS₁_eq_evalInt (q : k) hq, TateCurve.evalInt_map_of_continuous f hf hq,
      tateS₁_eq_evalInt (f (q : k)) hq']

end WeierstrassCurve
