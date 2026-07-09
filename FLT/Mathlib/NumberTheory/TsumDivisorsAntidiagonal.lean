/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram
-/
module

public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
public import Mathlib.Topology.Algebra.TopologicallyNilpotent

/-!
# The Lambert series rearrangement, hypothesis-driven

Material destined for Mathlib.

This file proves the general Lambert series rearrangement
`∑_{m≥1} c(m)rᵐ/(1-rᵐ) = ∑_{N≥1} (∑_{d ∣ N} c(d))rᴺ` over a topological field, with the analytic
inputs taken as *hypotheses* rather than derived from a norm. The rearrangement itself — regrouping
the double series `∑_{m,j} c(m)r^{mj}` along the fibres of `(m, j) ↦ mj`, which are exactly the
divisor pairs of `N` — is pure algebra plus unconditional-summability bookkeeping. Only the two
analytic facts (the geometric row expansions and the summability of the double series) genuinely use
the topology, and they are what the hypotheses below isolate.

## Two formulations

* `tsum_lambert_of_summable`, over an **arbitrary Hausdorff topological field**, takes *both*
  analytic inputs as hypotheses:
  * `hgeo` — each row has its geometric expansion, `HasSum (fun j ↦ r^{m(j+1)}) (rᵐ/(1-rᵐ))`;
  * `hsum` — the double series is (unconditionally) summable.

* `tsum_lambert_of_summable_of_isTopologicallyNilpotent`, over a **complete uniform field**,
  replaces the per-row `hgeo` by the single, cleaner hypothesis that `r` is topologically nilpotent
  (`IsTopologicallyNilpotent r`, i.e. `rⁿ → 0`). This is a *trade*, not a free weakening. `hgeo`
  implies `IsTopologicallyNilpotent r` (a `HasSum` family is null along the cofinite filter — see
  the `example` motivating the companion), so the hypothesis is genuinely weaker; but reconstructing
  each row's `HasSum` from `rⁿ → 0` still needs the row to be summable, and the only source of that
  is `hsum`, whose fibres are summable only when `𝕜` is **complete** (`Summable.comp_injective`).
  Completeness cannot be dropped: over a bare topological field `rⁿ → 0` does not imply the
  geometric row is unconditionally summable. Topological nilpotency then supplies each row's *value*
  through the sequential geometric limit `∑_{j<N} (rᵐ)ʲ → (1-rᵐ)⁻¹`
  (`isTopologicallyNilpotent_iff_tendsto_geomSum`), which `Summable.hasSum_iff_tendsto_nat` upgrades
  to the required `HasSum`.

Both intended instantiations are complete, so the second formulation is the convenient one there;
the first is kept for its full topological-field generality.

## How this differs from the existing mathlib lemma

Mathlib's `tsum_pow_div_one_sub_eq_tsum_sigma` (in
`Mathlib.NumberTheory.TsumDivisorsAntidiagonal`, whence the name of this file) states
`∑' n : ℕ+, n ^ k * r ^ n / (1 - r ^ n) = ∑' n : ℕ+, σ k n * r ^ n` for a complete
nontrivially normed field and `‖r‖ < 1`. Two restrictions are baked into it:

* **The analysis is normed.** Summability of the double series and the geometric row
  expansions are established through `‖·‖`-estimates, so the lemma is unusable over a
  nonarchimedean local field in the `ValuativeRel` framework, which carries no canonical
  `NormedField` instance (its valuation takes values in an abstract rank-one group with
  zero, not in `ℝ`).
* **The coefficients are the powers `c(d) = dᵏ`** (so the divisor sums are `σ k`). The
  rearrangement works for arbitrary coefficients; the Tate curve needs
  `c(d) = -((5d³ + 7d⁵)/12)`, which is not a power of `d`.

The two known Lambert lemmas become corollaries by discharging the hypotheses in their respective
settings:

* over a complete nontrivially normed field, by `hasSum_geometric_of_norm_lt_one` /
  `tendsto_pow_atTop_nhds_zero_of_norm_lt_one` and `summable_prod_mul_pow` — this rederivation of
  `tsum_pow_div_one_sub_eq_tsum_sigma` is carried out below (as an `example`; in a mathlib PR it
  would simply become the new proof of that lemma);
* over a nonarchimedean local field, by `TateCurve.hasSum_geometric_succ` /
  `TateCurve.tendsto_pow_nhds_zero` and `TateCurve.summable_of_valuation_le_pow` — recovering
  `TateCurve.tsum_lambert` of `FLT.KnownIn1980s.EllipticCurves.TateCurveBaseChange` (rewiring that
  file through this one is left for the upstreaming pass).
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
      ⇑sigmaAntidiagonalEquivProd) ⟨N, x⟩) ((∑ d ∈ (N : ℕ).divisors, c d) * r ^ (N : ℕ)) := by
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

/- `hgeo → IsTopologicallyNilpotent r`: the row hypothesis is strictly stronger than topological
nilpotency, which is why the completeness-based companion below can take the weaker
`IsTopologicallyNilpotent r` in its place. Only the first row `hgeo 1` is needed — a `HasSum` family
is null along the cofinite filter (`= atTop` on `ℕ`), i.e. `rⁿ → 0`. -/
example (r : 𝕜)
    (hgeo : ∀ m : ℕ+, HasSum (fun j : ℕ ↦ r ^ ((m : ℕ) * (j + 1)))
      (r ^ (m : ℕ) / (1 - r ^ (m : ℕ)))) :
    IsTopologicallyNilpotent r := by
  have h := (hgeo 1).summable.tendsto_cofinite_zero
  simp only [PNat.one_coe, one_mul, Nat.cofinite_eq_atTop] at h
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp h

/-- The sequential geometric limit that identifies each row's value in the companion below: over a
Hausdorff topological field, `r` is topologically nilpotent iff the geometric partial sums
`∑_{n<N} rⁿ` converge to `(1-r)⁻¹`. This *sequential* convergence is weaker than `HasSum`, but
combined with row summability from `hsum` (through `Summable.hasSum_iff_tendsto_nat`) it recovers
the row `HasSum` that `tsum_lambert_of_summable` takes as `hgeo`. -/
theorem isTopologicallyNilpotent_iff_tendsto_geomSum (r : 𝕜) :
    IsTopologicallyNilpotent r ↔
      Filter.Tendsto (fun N ↦ ∑ n ∈ Finset.range N, r ^ n) Filter.atTop (nhds (1 - r)⁻¹) := by
  constructor
  · intro hr
    have hr1 : r ≠ 1 := by
      rintro rfl
      have h1 : Filter.Tendsto (fun n : ℕ ↦ (1 : 𝕜) ^ n) Filter.atTop (nhds 0) := hr
      simp only [one_pow] at h1
      exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)
    rw [funext fun N ↦ geom_sum_eq hr1 N]
    have hlim : Filter.Tendsto (fun N ↦ (r ^ N - 1) / (r - 1)) Filter.atTop
      (nhds (((0 : 𝕜) - 1) / (r - 1))) := (hr.sub_const 1).div_const _
    have hval : ((0 : 𝕜) - 1) / (r - 1) = (1 - r)⁻¹ := by
      grind
    rwa [hval] at hlim
  · intro h
    have hdiff := (h.comp (Filter.tendsto_add_atTop_nat 1)).sub h
    have hstep : (fun N ↦ (∑ n ∈ Finset.range (N + 1), r ^ n) - ∑ n ∈ Finset.range N, r ^ n)
        = fun N ↦ r ^ N := funext fun N ↦ by rw [Finset.sum_range_succ]; ring
    simp_rw [sub_self, Function.comp_apply, hstep] at hdiff
    exact hdiff

/- **The completeness-based companion.** Over a *complete* Hausdorff uniform field, the per-row
hypothesis `hgeo` of `tsum_lambert_of_summable` can be replaced by the single, cleaner assumption
that `r` is topologically nilpotent. Completeness is what lets `hsum` supply each row's summability
(a row is a fibre of the summable double series, via `Summable.comp_injective`); topological
nilpotency then supplies each row's value (via `isTopologicallyNilpotent_iff_tendsto_geomSum`). Both
intended instantiations satisfy the hypotheses: a complete normed field, and a nonarchimedean local
field (`IsNonarchimedeanLocalField` provides `CompleteSpace`). See the module docstring for why
completeness cannot be dropped here. -/
section Complete

variable {𝕜 : Type*} [Field 𝕜] [UniformSpace 𝕜] [IsUniformAddGroup 𝕜] [IsTopologicalRing 𝕜]
  [CompleteSpace 𝕜] [T2Space 𝕜]

/-- The Lambert series rearrangement from topological nilpotency, over a complete uniform field: the
companion to `tsum_lambert_of_summable` that trades the per-row hypothesis `hgeo` for the single
assumption `IsTopologicallyNilpotent r`, at the cost of assuming `𝕜` complete. -/
theorem tsum_lambert_of_summable_of_isTopologicallyNilpotent (r : 𝕜) (c : ℕ → 𝕜)
    (htn : IsTopologicallyNilpotent r)
    (hsum : Summable fun p : ℕ+ × ℕ+ ↦ c p.1 * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) :
    ∑' m : ℕ+, c m * r ^ (m : ℕ) / (1 - r ^ (m : ℕ)) =
      ∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, c d) * r ^ (N : ℕ) := by
  suffices ∀ m :  ℕ+, HasSum (fun j ↦ c m * r ^ ((m : ℕ) * (j + 1)))
      (c m * r ^ (m : ℕ) / (1 - r ^ (m : ℕ))) by
    have hfib (N : ℕ+) : HasSum (fun x : (Nat.divisorsAntidiagonal (N : ℕ)) ↦
        ((fun p : ℕ+ × ℕ+ ↦ c p.1 * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) ∘
        ⇑sigmaAntidiagonalEquivProd) ⟨N, x⟩) ((∑ d ∈ (N : ℕ).divisors, c d) * r ^ (N : ℕ)) := by
      have hterm : ∀ x, ((fun p ↦ c p.1 * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) ∘
          ⇑sigmaAntidiagonalEquivProd) ⟨N, x⟩ = c (x : ℕ × ℕ).1 * r ^ (N : ℕ) :=
        fun x ↦ by simp only [Function.comp_apply, sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk,
          divisorsAntidiagonalFactors, PNat.mk_coe, (Nat.mem_divisorsAntidiagonal.mp x.2).1]
      convert hasSum_fintype _ using 1
      rw [Finset.univ_eq_attach, Finset.sum_congr rfl fun x _ ↦ hterm x,
        Finset.sum_attach (Nat.divisorsAntidiagonal N) (fun y ↦ c y.1 * r ^ (N : ℕ)),
        ← Finset.sum_mul, Nat.sum_divisorsAntidiagonal (fun d _ ↦ c d)]
    obtain ⟨_, hS⟩ := hsum
    rw [(hS.prod_fiberwise fun m ↦ Equiv.pnatEquivNat.symm.hasSum_iff.mp (this m)).tsum_eq,
      ((sigmaAntidiagonalEquivProd.hasSum_iff.mpr hS).sigma hfib).tsum_eq]
  intro m
  have : Summable (fun j : ℕ ↦ c (m : ℕ) * r ^ ((m : ℕ) * (j + 1))) := by
    suffices Function.Injective (fun j : ℕ ↦ (m, j.succPNat)) by
      simpa only [Function.comp_def, Nat.succPNat_coe, Nat.succ_eq_add_one] using
        hsum.comp_injective this
    exact fun a b h ↦ Nat.succPNat_injective (Prod.ext_iff.1 h).2
  have htnm : IsTopologicallyNilpotent (r ^ (m : ℕ)) := by
    change Filter.Tendsto (fun n : ℕ ↦ (r ^ (m : ℕ)) ^ n) Filter.atTop (nhds 0)
    simpa only [Function.comp_def, pow_mul] using htn.comp
      (Filter.tendsto_atTop_mono (fun n ↦ Nat.le_mul_of_pos_left n m.pos) Filter.tendsto_id)
  have hfac : ∀ N : ℕ, ∑ j ∈ Finset.range N, c (m : ℕ) * r ^ ((m : ℕ) * (j + 1))
      = c (m : ℕ) * r ^ (m : ℕ) * ∑ j ∈ Finset.range N, (r ^ (m : ℕ)) ^ j := fun N ↦ by
    simpa [Finset.mul_sum] using Finset.sum_congr rfl fun j _ ↦ by rw [pow_mul, pow_succ]; ring
  simpa only [this.hasSum_iff_tendsto_nat, hfac, div_eq_mul_inv] using
    ((isTopologicallyNilpotent_iff_tendsto_geomSum (r ^ (m : ℕ))).mp htnm).const_mul
    (c (m : ℕ) * r ^ (m : ℕ))

end Complete

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

/- Confirmation that the completeness-based companion is genuinely usable in this setting: a
`NontriviallyNormedField` with `[CompleteSpace]` supplies the uniform-field instances the variant
needs, and `‖r‖ < 1` discharges `IsTopologicallyNilpotent r`. -/
example (r : 𝕜) (c : ℕ → 𝕜) (hr : ‖r‖ < 1)
    (hsum : Summable fun p : ℕ+ × ℕ+ ↦ c p.1 * r ^ ((p.1 : ℕ) * (p.2 : ℕ))) :
    ∑' m : ℕ+, c m * r ^ (m : ℕ) / (1 - r ^ (m : ℕ)) =
      ∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, c d) * r ^ (N : ℕ) :=
  tsum_lambert_of_summable_of_isTopologicallyNilpotent r c
    (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hr) hsum

end Normed
