/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
module

public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# The Lambert series rearrangement, hypothesis-driven

Material destined for Mathlib.

This file proves the general Lambert series rearrangement
`∑_{m≥1} c(m)rᵐ/(1-rᵐ) = ∑_{N≥1} (∑_{d ∣ N} c(d))rᴺ` (`tsum_lambert_of_summable`) over an
arbitrary Hausdorff topological field, with the two analytic inputs — the geometric
expansion of each row and the summability of the double series — taken as *hypotheses*.

## How this differs from the existing mathlib lemma

Mathlib's `tsum_pow_div_one_sub_eq_tsum_sigma` (in
`Mathlib.NumberTheory.TsumDivisorsAntidiagonal`, whence the name of this file) states
`∑' n : ℕ+, n ^ k * r ^ n / (1 - r ^ n) = ∑' n : ℕ+, σ k n * r ^ n` for a complete
nontrivially normed field and `‖r‖ < 1`. Two restrictions are baked into it:

* **The analysis is normed.** Summability of the double series and the geometric row
  expansions are established through `‖·‖`-estimates, so the lemma is unusable over a
  nonarchimedean local field in the `ValuativeRel` framework, which carries no canonical
  `NormedField` instance (its valuation takes values in an abstract rank-one group with
  zero, not in `ℝ`). Yet the *rearrangement itself* — regrouping the double series
  `∑_{m,j} c(m)r^{mj}` along the fibres of `(m, j) ↦ mj`, which are the divisor pairs —
  is pure algebra plus unconditional-summability bookkeeping, valid in any Hausdorff
  topological field.
* **The coefficients are the powers `c(d) = dᵏ`** (so the divisor sums are `σ k`). The
  rearrangement works for arbitrary coefficients; the Tate curve needs
  `c(d) = -((5d³ + 7d⁵)/12)`, which is not a power of `d`.

`tsum_lambert_of_summable` removes both restrictions by isolating the two analytic facts
as hypotheses `hgeo` and `hsum`. The two known Lambert lemmas then become corollaries by
discharging the hypotheses in their respective settings:

* over a complete nontrivially normed field, by `hasSum_geometric_of_norm_lt_one` and
  `summable_prod_mul_pow` — this rederivation of `tsum_pow_div_one_sub_eq_tsum_sigma` is
  carried out below (as an `example`; in a mathlib PR it would simply become the new
  proof of that lemma);
* over a nonarchimedean local field, by `TateCurve.hasSum_geometric_succ` and
  `TateCurve.summable_of_valuation_le_pow` — recovering `TateCurve.tsum_lambert` of
  `FLT.KnownIn1980s.EllipticCurves.TateCurveBaseChange` (rewiring that file through this
  one is left for the upstreaming pass).
-/

@[expose] public section

open scoped ArithmeticFunction.sigma

variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [T2Space 𝕜]

/-- The Lambert series rearrangement
`∑_{m≥1} c(m)rᵐ/(1-rᵐ) = ∑_{N≥1} (∑_{d ∣ N} c(d))rᴺ` over a Hausdorff topological field,
with the analytic inputs as hypotheses: `hgeo` says each row `rᵐ/(1-rᵐ)` has its geometric
expansion `∑_{j≥1} r^{mj}`, and `hsum` says the double series is (unconditionally)
summable. Given these, the double series is regrouped along the fibres of `(m, j) ↦ mj`,
which are exactly the divisor pairs of `N`. -/
theorem tsum_lambert_of_summable (r : 𝕜) (c : ℕ → 𝕜)
    (hgeo : ∀ m : ℕ+, HasSum (fun j : ℕ ↦ r ^ ((m : ℕ) * (j + 1)))
      (r ^ (m : ℕ) / (1 - r ^ (m : ℕ))))
    (hsum : Summable fun p : ℕ+ × ℕ+ ↦ c p.1 * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) :
    ∑' m : ℕ+, c m * r ^ (m : ℕ) / (1 - r ^ (m : ℕ)) =
      ∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, c d) * r ^ (N : ℕ) := by
  obtain ⟨S, hS⟩ := hsum
  have hrow (m : ℕ+) : HasSum (fun j ↦ c m * r ^ ((m : ℕ) * (j + 1)))
      (c m * r ^ (m : ℕ) / (1 - r ^ (m : ℕ))) := by
    simpa only [mul_div_assoc] using (hgeo m).mul_left (c m)
  have hfib (N : ℕ+) : HasSum (fun x : (Nat.divisorsAntidiagonal (N : ℕ)) ↦
      ((fun p : ℕ+ × ℕ+ ↦ c p.1 * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) ∘
        ⇑sigmaAntidiagonalEquivProd) ⟨N, x⟩)
      ((∑ d ∈ (N : ℕ).divisors, c d) * r ^ (N : ℕ)) := by
    have hterm : ∀ x, ((fun p ↦ c p.1 * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) ∘ ⇑sigmaAntidiagonalEquivProd)
        ⟨N, x⟩ = c (x : ℕ × ℕ).1 * r ^ (N : ℕ) :=
      fun x ↦ by simp only [Function.comp_apply, sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk,
        divisorsAntidiagonalFactors, PNat.mk_coe, (Nat.mem_divisorsAntidiagonal.mp x.2).1]
    convert hasSum_fintype _ using 1
    · rw [Finset.univ_eq_attach, Finset.sum_congr rfl fun x _ ↦ hterm x,
        Finset.sum_attach (Nat.divisorsAntidiagonal N) (fun y ↦ c y.1 * r ^ (N : ℕ)),
        ← Finset.sum_mul, Nat.sum_divisorsAntidiagonal (fun d _ ↦ c d)]
  rw [(hS.prod_fiberwise fun m ↦ Equiv.pnatEquivNat.symm.hasSum_iff.mp ((hrow) m)).tsum_eq,
    ((sigmaAntidiagonalEquivProd.hasSum_iff.mpr hS).sigma hfib).tsum_eq]

/- Sanity check, and the shape of the eventual mathlib PR: mathlib's
`tsum_pow_div_one_sub_eq_tsum_sigma` is deduced from `tsum_lambert_of_summable` by
discharging `hgeo` with the normed-field geometric series and `hsum` with mathlib's own
`summable_prod_mul_pow`. Upstream, this deduction would replace the current proof of that
lemma. -/
section Normed

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {r : 𝕜}

omit [CompleteSpace 𝕜] in
/-- The geometric series of `rᵐ`, indexed from the first term: for `‖r‖ < 1` and `m ≠ 0`,
`∑_{j≥1} r^{mj} = rᵐ/(1-rᵐ)`. This discharges the `hgeo` hypothesis of
`tsum_lambert_of_summable` over a normed field (no completeness is needed: the limit is
explicit). -/
theorem hasSum_geometric_pow_mul_succ (hr : ‖r‖ < 1) {m : ℕ} (hm : m ≠ 0) :
    HasSum (fun j : ℕ ↦ r ^ (m * (j + 1))) (r ^ m / (1 - r ^ m)) := by
  have hrm : ‖r ^ m‖ < 1 := by
    simpa [norm_pow] using pow_lt_one₀ (norm_nonneg r) hr hm
  have hfun : (fun j : ℕ ↦ r ^ (m * (j + 1))) = fun j : ℕ ↦ r ^ m * (r ^ m) ^ j := by
    funext j
    ring
  simpa [hfun, div_eq_mul_inv] using (hasSum_geometric_of_norm_lt_one hrm).mul_left _

/-- The variant of `summable_prod_mul_pow` with the weight on the *first* coordinate.
This discharges the `hsum` hypothesis of `tsum_lambert_of_summable` for the weights `dᵏ`
over a complete normed field. -/
theorem summable_prod_mul_pow' [NormSMulClass ℤ 𝕜] (k : ℕ) (hr : ‖r‖ < 1) :
    Summable fun p : ℕ+ × ℕ+ ↦ ((p.1 : ℕ) : 𝕜) ^ k * r ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
  refine (summable_prod_mul_pow k hr).prod_symm.congr fun p ↦ ?_
  simp only [Prod.fst_swap, Prod.snd_swap, mul_comm (p.2 : ℕ) (p.1 : ℕ)]

example [NormSMulClass ℤ 𝕜] (hr : ‖r‖ < 1) (k : ℕ) :
    ∑' n : ℕ+, n ^ k * r ^ (n : ℕ) / (1 - r ^ (n : ℕ)) = ∑' n : ℕ+, σ k n * r ^ (n : ℕ) := by
  refine Eq.trans (tsum_congr fun n ↦ ?_)
    ((tsum_lambert_of_summable r (fun d ↦ (d : 𝕜) ^ k)
      (fun m ↦ hasSum_geometric_pow_mul_succ hr m.pos.ne')
      (summable_prod_mul_pow' k hr)).trans (tsum_congr fun N ↦ ?_))
  · ring
  · rw [ArithmeticFunction.sigma_apply]
    push_cast
    ring

end Normed
