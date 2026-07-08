/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateParameter

import FLT.Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!

# Base change of integral power series evaluations

Support for the functoriality of the Tate curve
(`WeierstrassCurve.tateCurve_baseChange`): the coefficients of the Tate curve are
evaluations `TateCurve.evalInt` of *integral* power series, and such evaluations commute
with any valuative extension `k → l` of nonarchimedean local fields
(`TateCurve.evalInt_map` below) — both evaluations are within `|q|^N` of the common
`N`-th partial sum, whose bound transfers along the strictly monotone map of value groups
`ValuativeExtension.mapValueGroupWithZero`, so no continuity argument is needed.

To apply this to the Tate curve one needs its defining coefficient series `tateA₄`,
`tateA₆` — which are Lambert-type series `∑_{n≥1} c(n)qⁿ/(1-qⁿ)`, not power series — to
*be* such evaluations. This is the Lambert series rearrangement
`∑_{m≥1} c(m)qᵐ/(1-qᵐ) = ∑_{N≥1} (∑_{d ∣ N} c(d))qᴺ` (`TateCurve.tsum_lambert`), proved
by expanding each `qᵐ/(1-qᵐ)` as a geometric series and regrouping the double series
along the fibres of `(m, j) ↦ mj`. The corresponding formal power series over `ℤ` are
`TateCurve.a₄Formal` and `TateCurve.a₆Formal`; the identities
`tateA₄ q = evalInt q a₄Formal`, `tateA₆ q = evalInt q a₆Formal` are proved in
`FLT.KnownIn1980s.EllipticCurves.TateCurve`, where `tateA₄` and `tateA₆` are defined.

Everything here is extracted (minimally) from FLT PR #1081.
-/

@[expose] public section

open scoped ArithmeticFunction.sigma -- `σ k n` notation for the sum of the `k`th powers
                                     -- of the divisors of `n`
open scoped Topology -- `𝓝` notation for neighbourhood filters
open ValuativeRel -- `𝒪[k]` notation for the ring of integers of `k`, and `valuation`

namespace TateCurve

open PowerSeries

/-! ### The formal `a₄`- and `a₆`-series of the Tate curve -/

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

/-! ### Subtraction of evaluations -/

section Evaluation

variable {k : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k]

theorem evalInt_sub {q : k} {F G : ℤ⟦X⟧}
    (hF : Summable fun n ↦ ((coeff n F : ℤ) : k) * q ^ n)
    (hG : Summable fun n ↦ ((coeff n G : ℤ) : k) * q ^ n) :
    evalInt q (F - G) = evalInt q F - evalInt q G := by
  simp only [evalInt, map_sub, Int.cast_sub, sub_mul]
  exact hF.tsum_sub hG

end Evaluation

/-! ### Nonarchimedean summability and the Lambert rearrangement -/

-- let k be a nonarchimedean local field
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

-- The nonarchimedean convergence criterion `TateCurve.summable_of_valuation_le_pow` used
-- throughout this section lives in `FLT.KnownIn1980s.EllipticCurves.TateParameter`
-- (imported above), next to its specialisation `summable_evalInt`.

-- `TateCurve.tendsto_pow_nhds_zero` also lives in `TateParameter` (imported above),
-- next to the summability criterion.

/-- The geometric series over a nonarchimedean local field: for `|x| < 1`,
`x + x² + x³ + ⋯ = x/(1 - x)`. (Summability is by the nonarchimedean criterion — the
terms tend to zero — and the value is identified through the partial sums
`x(xⁿ - 1)/(x - 1)`.) -/
theorem hasSum_geometric_succ {x : k} (hx : valuation k x < 1) :
    HasSum (fun j : ℕ ↦ x ^ (j + 1)) (x / (1 - x)) := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have h1x : (1 : k) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  obtain ⟨S, hS⟩ : Summable fun j : ℕ ↦ x ^ (j + 1) :=
    summable_of_valuation_le_pow hx (fun j ↦ j + 1)
      (fun N ↦ (Set.finite_Iio N).subset fun j hj ↦ Set.mem_Iio.mpr (Nat.lt_of_succ_lt hj))
      fun j ↦ le_of_eq (map_pow _ _ _)
  suffices hlim : Filter.Tendsto (fun n : ℕ ↦ ∑ j ∈ Finset.range n, x ^ (j + 1))
      Filter.atTop (𝓝 (x / (1 - x))) from
    tendsto_nhds_unique hS.tendsto_sum_nat hlim ▸ hS
  have hps : ∀ n : ℕ, ∑ j ∈ Finset.range n, x ^ (j + 1) = x * ((x ^ n - 1) / (x - 1)) := by
    intro n
    rw [← geom_sum_eq hx1 n, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  simp only [hps]
  have h := (((tendsto_pow_nhds_zero hx).sub_const 1).div_const (x - 1)).const_mul x
  convert h using 2
  rw [zero_sub]
  field_simp
  ring

/-- The Lambert series rearrangement over a nonarchimedean local field: for any integer
coefficients `c` and `|q| < 1`,
`∑_{m≥1} c(m)qᵐ/(1 - qᵐ) = ∑_{N≥1} (∑_{d ∣ N} c(d))qᴺ`.
This is the valuative instantiation of the general `tsum_lambert_of_summable`
(`FLT.Mathlib.NumberTheory.TsumDivisorsAntidiagonal`): the geometric row expansions come
from `hasSum_geometric_succ`, and the double series is summable since its terms tend to
zero nonarchimedeanly (`summable_of_valuation_le_pow`). -/
theorem tsum_lambert (q : k) (hq : valuation k q < 1) (c : ℕ → ℤ) :
    ∑' m : ℕ, ((c (m + 1) : ℤ) : k) * q ^ (m + 1) / (1 - q ^ (m + 1)) =
      ∑' N : ℕ, ((∑ d ∈ N.divisors, c d : ℤ) : k) * q ^ N := by
  -- powers of `q` stay in the open unit disc
  have hqpow : ∀ n : ℕ+, valuation k (q ^ (n : ℕ)) < 1 := fun n ↦ by
    rw [map_pow]
    calc valuation k q ^ (n : ℕ) ≤ valuation k q ^ 1 :=
          pow_le_pow_right_of_le_one' hq.le n.pos
      _ = valuation k q := pow_one _
      _ < 1 := hq
  -- each row of the double series is a geometric series
  have hgeo : ∀ m : ℕ+, HasSum (fun j : ℕ ↦ q ^ ((m : ℕ) * (j + 1)))
      (q ^ (m : ℕ) / (1 - q ^ (m : ℕ))) := fun m ↦ by
    simpa only [← pow_mul] using hasSum_geometric_succ (hqpow m)
  -- the double series is summable, its terms tending to zero nonarchimedeanly
  have hsum : Summable fun p : ℕ+ × ℕ+ ↦ ((c p.1 : ℤ) : k) * q ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
    refine summable_of_valuation_le_pow hq (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ)) (fun N ↦ ?_) fun p ↦ ?_
    · refine (((Set.finite_Iio N).preimage PNat.coe_injective.injOn).prod
        ((Set.finite_Iio N).preimage PNat.coe_injective.injOn)).subset fun p hp ↦ ?_
      have h1 : (p.1 : ℕ) ≤ (p.1 : ℕ) * (p.2 : ℕ) := Nat.le_mul_of_pos_right _ p.2.pos
      have h2 : (p.2 : ℕ) ≤ (p.1 : ℕ) * (p.2 : ℕ) := Nat.le_mul_of_pos_left _ p.1.pos
      exact Set.mem_prod.mpr ⟨Set.mem_preimage.mpr (Set.mem_Iio.mpr (lt_of_le_of_lt h1 hp)),
        Set.mem_preimage.mpr (Set.mem_Iio.mpr (lt_of_le_of_lt h2 hp))⟩
    · rw [map_mul, map_pow]
      simpa using mul_le_mul_left (valuation_intCast_le_one _)
        (valuation k q ^ ((p.1 : ℕ) * (p.2 : ℕ)))
  calc ∑' m : ℕ, ((c (m + 1) : ℤ) : k) * q ^ (m + 1) / (1 - q ^ (m + 1))
      = ∑' m : ℕ+, ((c m : ℤ) : k) * q ^ (m : ℕ) / (1 - q ^ (m : ℕ)) :=
        (tsum_pnat_eq_tsum_succ (f := fun n ↦ ((c n : ℤ) : k) * q ^ n / (1 - q ^ n))).symm
    _ = ∑' N : ℕ+, (∑ d ∈ (N : ℕ).divisors, ((c d : ℤ) : k)) * q ^ (N : ℕ) :=
        tsum_lambert_of_summable q (fun d ↦ ((c d : ℤ) : k)) hgeo hsum
    _ = ∑' N : ℕ+, ((∑ d ∈ (N : ℕ).divisors, c d : ℤ) : k) * q ^ (N : ℕ) :=
        tsum_congr fun N ↦ by push_cast; ring
    _ = ∑' N : ℕ, ((∑ d ∈ N.divisors, c d : ℤ) : k) * q ^ N := by
        refine PNat.coe_injective.tsum_eq
          (f := fun N : ℕ ↦ ((∑ d ∈ N.divisors, c d : ℤ) : k) * q ^ N) fun x hx ↦ ?_
        cases x with
        | zero => simp at hx
        | succ n => exact ⟨n.succPNat, rfl⟩

/-- Bridge form of the Lambert rearrangement: if the coefficients of `F ∈ ℤ⟦X⟧` are the
divisor sums `Fₙ = ∑_{d ∣ n} c(d)`, then the Lambert series of `c` *is* the evaluation of
`F` on the open unit disc. This is the form in which `tsum_lambert` is consumed: it turns
the defining series of the Tate curve coefficients (`tateA₄`, `tateA₆`) into `evalInt`s in
one step. -/
theorem tsum_lambert_eq_evalInt (q : k) (hq : valuation k q < 1) (c : ℕ → ℤ) {F : ℤ⟦X⟧}
    (hF : ∀ n, PowerSeries.coeff n F = ∑ d ∈ n.divisors, c d) :
    ∑' m : ℕ, ((c (m + 1) : ℤ) : k) * q ^ (m + 1) / (1 - q ^ (m + 1)) = evalInt q F := by
  rw [tsum_lambert q hq c]
  simp only [evalInt]
  exact tsum_congr fun N ↦ by rw [hF N]

/-! ### The quantitative tail bound and base change of evaluations -/

/-- Quantitative tail bound: the evaluation of an integral power series on the open unit
disc is within `|q|^N` of its `N`-th partial sum. -/
theorem valuation_evalInt_sub_sum_le (q : k) (hq : valuation k q < 1)
    (F : ℤ⟦X⟧) (N : ℕ) :
    valuation k (evalInt q F -
      ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n) ≤
    valuation k q ^ N := by
  -- the partial sum is the evaluation of the truncation
  have htrunc : evalInt q ((F.trunc N : Polynomial ℤ) : ℤ⟦X⟧) =
      ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n := by
    have h0 : ∀ n ∉ Finset.range N,
        ((PowerSeries.coeff n ((F.trunc N : Polynomial ℤ) : ℤ⟦X⟧) : ℤ) : k) * q ^ n = 0 := by
      intro n hn
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc,
        if_neg (by simpa using hn), Int.cast_zero, zero_mul]
    refine (hasSum_sum_of_ne_finset_zero h0).tsum_eq.trans ?_
    exact Finset.sum_congr rfl fun n hn ↦ by
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos (Finset.mem_range.mp hn)]
  rw [← htrunc, ← evalInt_sub (summable_evalInt q hq _) (summable_evalInt q hq _)]
  refine valuation_evalInt_le_pow q hq fun m hm ↦ ?_
  rw [map_sub, Polynomial.coeff_coe, PowerSeries.coeff_trunc, if_pos hm, sub_self]

-- Now let `l` be a second nonarchimedean local field and let `k → l` be a morphism of
-- fields inducing the valuative relation on `k` from the one on `l` (the
-- `ValuativeExtension` hypothesis).
variable {l : Type*} [Field l] [ValuativeRel l] [TopologicalSpace l]
  [IsNonarchimedeanLocalField l] [Algebra k l] [ValuativeExtension k l]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [TopologicalSpace l]
  [IsNonarchimedeanLocalField l] in
/-- A valuative extension maps the open unit disc into the open unit disc: the induced
map of value groups (`ValuativeExtension.mapValueGroupWithZero`) is strictly monotone. -/
theorem valuation_algebraMap_lt_one {q : k} (hq : valuation k q < 1) :
    valuation l (algebraMap k l q) < 1 := by
  simpa using ValuativeExtension.mapValueGroupWithZero_strictMono (A := k) (B := l) hq

/-- Evaluation of integral power series commutes with valuative extensions of
nonarchimedean local fields: the coefficients are (the same) integers on both sides, and
both evaluations are within `|q|^N` of the common `N`-th partial sum
(`valuation_evalInt_sub_sum_le`), whose bound transfers along the strictly monotone map
of value groups — no continuity argument is needed. -/
theorem evalInt_map (q : k) (hq : valuation k q < 1) (F : ℤ⟦X⟧) :
    algebraMap k l (evalInt q F) = evalInt (algebraMap k l q) F := by
  have hq' : valuation l (algebraMap k l q) < 1 := valuation_algebraMap_lt_one hq
  rw [← sub_eq_zero]
  by_contra h
  obtain ⟨N, hN⟩ := exists_pow_valuation_lt (algebraMap k l q) hq'
    (Units.mk0 _ ((valuation l).ne_zero_iff.mpr h))
  -- the image of the `k`-side partial sum is the `l`-side partial sum
  have hmapsum : algebraMap k l
      (∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n) =
      ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : l) * (algebraMap k l q) ^ n := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun n _ ↦ by rw [map_mul, map_pow, map_intCast]
  -- the `k`-side tail bound, transferred along the map of value groups
  have h1 : valuation l (algebraMap k l (evalInt q F) -
      ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : l) * (algebraMap k l q) ^ n) ≤
      valuation l (algebraMap k l q) ^ N := by
    rw [← hmapsum, ← map_sub]
    calc valuation l (algebraMap k l (evalInt q F -
            ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n))
        = ValuativeExtension.mapValueGroupWithZero k l (valuation k (evalInt q F -
            ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : k) * q ^ n)) :=
          (ValuativeExtension.mapValueGroupWithZero_valuation _).symm
      _ ≤ ValuativeExtension.mapValueGroupWithZero k l (valuation k q ^ N) :=
          ValuativeExtension.mapValueGroupWithZero_strictMono.monotone
            (valuation_evalInt_sub_sum_le q hq F N)
      _ = valuation l (algebraMap k l q) ^ N := by
          rw [map_pow, ValuativeExtension.mapValueGroupWithZero_valuation]
  -- the `l`-side tail bound
  have h2 := valuation_evalInt_sub_sum_le (algebraMap k l q) hq' F N
  -- ultrametrically, the difference is then smaller than its own valuation: absurd
  refine absurd ?_ (lt_irrefl (valuation l
    (algebraMap k l (evalInt q F) - evalInt (algebraMap k l q) F)))
  calc valuation l (algebraMap k l (evalInt q F) - evalInt (algebraMap k l q) F)
      = valuation l ((algebraMap k l (evalInt q F) -
          ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : l) * (algebraMap k l q) ^ n) -
        (evalInt (algebraMap k l q) F -
          ∑ n ∈ Finset.range N, ((PowerSeries.coeff n F : ℤ) : l) * (algebraMap k l q) ^ n)) := by
        congr 1
        ring
    _ ≤ max _ _ := Valuation.map_sub _ _ _
    _ ≤ valuation l (algebraMap k l q) ^ N := max_le h1 h2
    _ < _ := hN

end TateCurve
