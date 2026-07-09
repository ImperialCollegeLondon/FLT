/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram, Samuel Yin
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import FLT.KnownIn1980s.EllipticCurves.TateCurveDescent

import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import FLT.Slop.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# The Tate curve `E_q`, its coordinate series, and its discriminant

The Tate curve `E_q : y² + xy = x³ + a₄(q)x + a₆(q)` (`WeierstrassCurve.tateCurve`), the
uniformisation coordinate series `X(u, q)`, `Y(u, q)` (`WeierstrassCurve.tateX`/`tateY`), the
nonarchimedean summation calculus for the defining series (`hasSum_geometric_deriv`,
`hasSum_geom_rows`, …), and the discriminant computation `Δ(q) = q∏(1-qⁿ)²⁴` (`tateΔ_eq_prod`),
giving `Δ(q) ≠ 0`, i.e. `E_q` is an elliptic curve.

First of the files split out of `TateCurveUniformisation`; see that file's module docstring for
the overview of Tate's uniformisation.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄k).Point` notation for the group of `k`-points
open scoped PowerSeries -- `ℤ⟦X⟧` notation for `PowerSeries ℤ`
open scoped Topology -- `𝓝` notation for neighbourhood filters
open ValuativeRel -- `𝒪[k]` notation for the ring of integers of `k`, and `valuation`

-- Can be deleted when mathlib#41391 lands
set_option linter.overlappingInstances false

/-! ### The Tate curve `E_q` and the coordinate series `X(u, q)`, `Y(u, q)`

For `q` with `0 < |q| < 1` there is an explicit Weierstrass curve `E_q`, whose coefficients
are power series in `q` with integer coefficients, together with a uniformisation
`kˣ/qᶻ ≅ E_q(k)` given by explicit power series `X(u, q)`, `Y(u, q)` — all of it involving
no choices whatsoever, and commuting on the nose with every valuative morphism of fields.
-/

section TateCurve

-- For the defining series we only need a topology on the field: this section makes sense
-- (and the series converge) over any field complete with respect to a rank 1
-- nonarchimedean valuation.
variable {k : Type*} [Field k] [TopologicalSpace k]

/-- The coefficient `a₄(q) = -5s₃(q)` of the Tate curve, where
`sₖ(q) = ∑_{n≥1} nᵏqⁿ/(1-qⁿ)` (Silverman, ATAEC V.3). -/
noncomputable def WeierstrassCurve.tateA₄ (q : k) : k :=
  -5 * ∑' n : ℕ, ((n + 1 : ℕ) : k) ^ 3 * q ^ (n + 1) / (1 - q ^ (n + 1))

/-- The coefficient `a₆(q) = -(5s₃(q) + 7s₅(q))/12` of the Tate curve, where
`sₖ(q) = ∑_{n≥1} nᵏqⁿ/(1-qⁿ)`; the integrality `12 ∣ 5n³ + 7n⁵` makes sense of the
division by `12` in every characteristic (Silverman, ATAEC V.3). -/
noncomputable def WeierstrassCurve.tateA₆ (q : k) : k :=
  ∑' n : ℕ, -(((5 * (n + 1) ^ 3 + 7 * (n + 1) ^ 5) / 12 : ℤ) : k) * q ^ (n + 1) /
    (1 - q ^ (n + 1))

/-- The Tate curve `E_q : y² + xy = x³ + a₄(q)x + a₆(q)` (Silverman, ATAEC V.3). -/
noncomputable def WeierstrassCurve.tateCurve (q : k) : WeierstrassCurve k :=
  ⟨1, 0, 0, tateA₄ q, tateA₆ q⟩

/-- The `x`-coordinate `X(u, q) = ∑_{n ∈ ℤ} qⁿu/(1 - qⁿu)² - 2s₁(q)` of Tate's
uniformisation, where `s₁(q) = ∑_{n ≥ 1} nqⁿ/(1 - qⁿ)`. This is the function `X(u, q)` of
Silverman, ATAEC V.1.1; for `0 < |q| < 1` and `u ∉ qᶻ` the sums converge (junk value
otherwise). -/
noncomputable def WeierstrassCurve.tateX (u q : k) : k :=
  (∑' n : ℤ, q ^ n * u / (1 - q ^ n * u) ^ 2) -
    2 * ∑' n : ℕ, ((n + 1 : ℕ) : k) * q ^ (n + 1) / (1 - q ^ (n + 1))

/-- The `y`-coordinate `Y(u, q) = ∑_{n ∈ ℤ} (qⁿu)²/(1 - qⁿu)³ + s₁(q)` of Tate's
uniformisation, where `s₁(q) = ∑_{n ≥ 1} nqⁿ/(1 - qⁿ)`. This is the function `Y(u, q)` of
Silverman, ATAEC V.1.1. -/
noncomputable def WeierstrassCurve.tateY (u q : k) : k :=
  (∑' n : ℤ, (q ^ n * u) ^ 2 / (1 - q ^ n * u) ^ 3) +
    ∑' n : ℕ, ((n + 1 : ℕ) : k) * q ^ (n + 1) / (1 - q ^ (n + 1))

end TateCurve

-- let k be a nonarchimedean local field
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

/-- Any unit of `k` can be moved into the annulus `|q| < |·| ≤ 1` by a power of `q`:
a fundamental domain for the action of `qᶻ` on `kˣ`. As with
`exists_pow_valuation_lt`, this is where the rank-one hypothesis enters, through the
strictly monotone embedding of the value group into `ℝ≥0` and the archimedean property
`exists_mem_Ioc_zpow` there. -/
theorem TateCurve.exists_zpow_mul_mem_annulus (q : kˣ) (hq : valuation k (q : k) < 1)
    (u : kˣ) : ∃ m : ℤ, valuation k (q : k) < valuation k ((q : k) ^ m * (u : k)) ∧
      valuation k ((q : k) ^ m * (u : k)) ≤ 1 := by
  obtain ⟨s⟩ := ValuativeRel.IsRankLeOne.nonempty (R := k)
  set β := s.emb (valuation k (q : k)) with hβ
  set α := s.emb (valuation k (u : k)) with hα
  have hβ0 : 0 < β := by
    have h : valuation k (q : k) ≠ 0 := (valuation k).ne_zero_iff.mpr (Units.ne_zero q)
    simpa [hβ] using s.strictMono (zero_lt_iff.mpr h)
  have hβ1 : β < 1 := by simpa [hβ] using s.strictMono hq
  have hα0 : 0 < α := by
    have h : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr (Units.ne_zero u)
    simpa [hα] using s.strictMono (zero_lt_iff.mpr h)
  obtain ⟨n, hn⟩ := exists_mem_Ioc_zpow hα0 ((one_lt_inv₀ hβ0).mpr hβ1)
  have hn1 : β ^ (-n) < α := by
    have := hn.1
    rwa [inv_zpow, ← zpow_neg] at this
  have hn2 : α ≤ β ^ (-(n + 1)) := by
    have := hn.2
    rwa [inv_zpow, ← zpow_neg] at this
  refine ⟨n + 1, ?_, ?_⟩
  · rw [map_mul, map_zpow₀]
    refine s.strictMono.lt_iff_lt.mp ?_
    rw [map_mul, map_zpow₀]
    calc β = β ^ (n + 1) * β ^ (-n) := by
          rw [← zpow_add₀ hβ0.ne', show n + 1 + -n = 1 by ring, zpow_one]
      _ < β ^ (n + 1) * α := mul_lt_mul_of_pos_left hn1 (zpow_pos hβ0 _)
  · rw [map_mul, map_zpow₀]
    refine s.strictMono.le_iff_le.mp ?_
    rw [map_mul, map_zpow₀, map_one]
    calc β ^ (n + 1) * α ≤ β ^ (n + 1) * β ^ (-(n + 1)) :=
          mul_le_mul_of_nonneg_left hn2 (zpow_pos hβ0 _).le
      _ = 1 := by rw [← zpow_add₀ hβ0.ne', show n + 1 + -(n + 1) = 0 by ring, zpow_zero]

/-- The derived geometric series over a nonarchimedean local field: for `|x| < 1`,
`∑_{j≥1} j·xʲ = x/(1-x)²`. Obtained as the Cauchy product of the geometric series with
itself: the `N`-th antidiagonal has `N + 1` terms, all equal to `x^(N+1)`. -/
theorem TateCurve.hasSum_geometric_deriv {x : k} (hx : valuation k x < 1) :
    HasSum (fun j : ℕ ↦ ((j + 1 : ℕ) : k) * x ^ (j + 1)) (x / (1 - x) ^ 2) := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  have h1x : (1 : k) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hgeo₁ := hasSum_geometric_succ hx
  have hgeo₀ : HasSum (fun j : ℕ ↦ x ^ j) (x / (1 - x) + 1) := by
    simpa using (hasSum_nat_add_iff (f := fun j : ℕ ↦ x ^ j) 1).mp hgeo₁
  have hdouble : Summable fun p : ℕ × ℕ ↦ x ^ (p.1 + 1) * x ^ p.2 := by
    refine summable_of_valuation_le_pow hx (fun p ↦ p.1 + p.2) (fun N ↦ ?_) fun p ↦ ?_
    · exact ((Set.finite_Iio N).prod (Set.finite_Iio N)).subset fun p hp ↦
        Set.mem_prod.mpr ⟨Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_right _ _) hp),
          Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_left _ _) hp)⟩
    · rw [← pow_add, map_pow]
      exact pow_le_pow_right_of_le_one' hx.le (by omega)
  have key := hgeo₁.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hgeo₀.summable hdouble
  rw [hgeo₁.tsum_eq, hgeo₀.tsum_eq] at key
  have hsummable : Summable fun j : ℕ ↦ ((j + 1 : ℕ) : k) * x ^ (j + 1) := by
    refine summable_of_valuation_le_pow hx (fun j ↦ j) (fun N ↦ Set.finite_Iio N) fun j ↦ ?_
    rw [map_mul, map_pow, show (((j + 1 : ℕ)) : k) = (((j + 1 : ℕ) : ℤ) : k) by push_cast; ring]
    calc valuation k (((j + 1 : ℕ) : ℤ) : k) * valuation k x ^ (j + 1)
        ≤ 1 * valuation k x ^ (j + 1) := mul_le_mul_left (valuation_intCast_le_one _) _
      _ = valuation k x ^ (j + 1) := one_mul _
      _ ≤ valuation k x ^ j := pow_le_pow_right_of_le_one' hx.le (Nat.le_succ j)
  have hinner : ∀ N : ℕ, (∑ kl ∈ Finset.antidiagonal N, x ^ (kl.1 + 1) * x ^ kl.2)
      = ((N + 1 : ℕ) : k) * x ^ (N + 1) := fun N ↦ by
    have h1 : ∀ kl ∈ Finset.antidiagonal N, x ^ (kl.1 + 1) * x ^ kl.2 = x ^ (N + 1) := by
      intro kl hkl
      rw [Finset.mem_antidiagonal] at hkl
      rw [← pow_add]
      congr 1
      omega
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  refine hsummable.hasSum_iff.mpr ?_
  calc ∑' j : ℕ, ((j + 1 : ℕ) : k) * x ^ (j + 1)
      = ∑' N : ℕ, ∑ kl ∈ Finset.antidiagonal N, x ^ (kl.1 + 1) * x ^ kl.2 :=
        tsum_congr fun N ↦ (hinner N).symm
    _ = x / (1 - x) * (x / (1 - x) + 1) := key.symm
    _ = x / (1 - x) ^ 2 := by
        field_simp
        ring

private theorem TateCurve.sum_range_succ_choose_two (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (i + 1) = (n + 2).choose 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h := Nat.choose_succ_succ (n + 2) 1
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Nat.choose_one_right] at h
      rw [show n + 1 + 2 = n + 2 + 1 from by omega]
      omega

/-- The twice-derived geometric series `∑_{d≥1} (d+1 choose 2)·xᵈ = x/(1-x)³`: the Cauchy
product of `hasSum_geometric_deriv` with the geometric series. These are the coefficients
of the `u⁻ᵈ`-half of the `y`-coordinate of Tate's uniformisation. -/
theorem TateCurve.hasSum_geometric_div_cube {x : k} (hx : valuation k x < 1) :
    HasSum (fun j : ℕ ↦ (((j + 2).choose 2 : ℕ) : k) * x ^ (j + 1)) (x / (1 - x) ^ 3) := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  have h1x : (1 : k) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hderiv := hasSum_geometric_deriv hx
  have hgeo₀ : HasSum (fun j : ℕ ↦ x ^ j) (x / (1 - x) + 1) := by
    simpa using (hasSum_nat_add_iff (f := fun j : ℕ ↦ x ^ j) 1).mp (hasSum_geometric_succ hx)
  have hdouble : Summable fun p : ℕ × ℕ ↦ ((p.1 + 1 : ℕ) : k) * x ^ (p.1 + 1) * x ^ p.2 := by
    refine summable_of_valuation_le_pow hx (fun p ↦ p.1 + p.2) (fun N ↦ ?_) fun p ↦ ?_
    · exact ((Set.finite_Iio N).prod (Set.finite_Iio N)).subset fun p hp ↦
        Set.mem_prod.mpr ⟨Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_right _ _) hp),
          Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_left _ _) hp)⟩
    · rw [map_mul, map_mul, map_pow, map_pow]
      calc valuation k ((p.1 + 1 : ℕ) : k) * valuation k x ^ (p.1 + 1) * valuation k x ^ p.2
          ≤ 1 * valuation k x ^ (p.1 + 1) * valuation k x ^ p.2 :=
            mul_le_mul_left (mul_le_mul_left (valuation_natCast_le_one _) _) _
        _ = valuation k x ^ (p.1 + 1 + p.2) := by rw [one_mul, ← pow_add]
        _ ≤ valuation k x ^ (p.1 + p.2) :=
            pow_le_pow_right_of_le_one' hx.le (by omega)
  have key := hderiv.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hgeo₀.summable hdouble
  rw [hderiv.tsum_eq, hgeo₀.tsum_eq] at key
  have hinner : ∀ N : ℕ,
      (∑ kl ∈ Finset.antidiagonal N, ((kl.1 + 1 : ℕ) : k) * x ^ (kl.1 + 1) * x ^ kl.2)
      = (((N + 2).choose 2 : ℕ) : k) * x ^ (N + 1) := fun N ↦ by
    have h1 : ∀ kl ∈ Finset.antidiagonal N, ((kl.1 + 1 : ℕ) : k) * x ^ (kl.1 + 1) * x ^ kl.2
        = ((kl.1 + 1 : ℕ) : k) * x ^ (N + 1) := by
      intro kl hkl
      rw [Finset.mem_antidiagonal] at hkl
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← Nat.cast_sum,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ_choose_two]
  have hsummable : Summable fun j : ℕ ↦ (((j + 2).choose 2 : ℕ) : k) * x ^ (j + 1) := by
    refine summable_of_valuation_le_pow hx (fun j ↦ j) (fun N ↦ Set.finite_Iio N) fun j ↦ ?_
    rw [map_mul, map_pow]
    calc valuation k (((j + 2).choose 2 : ℕ) : k) * valuation k x ^ (j + 1)
        ≤ 1 * valuation k x ^ (j + 1) := mul_le_mul_left (valuation_natCast_le_one _) _
      _ = valuation k x ^ (j + 1) := one_mul _
      _ ≤ valuation k x ^ j := pow_le_pow_right_of_le_one' hx.le (Nat.le_succ j)
  refine hsummable.hasSum_iff.mpr ?_
  calc ∑' j : ℕ, (((j + 2).choose 2 : ℕ) : k) * x ^ (j + 1)
      = ∑' N : ℕ, ∑ kl ∈ Finset.antidiagonal N, ((kl.1 + 1 : ℕ) : k) * x ^ (kl.1 + 1) * x ^ kl.2 :=
        tsum_congr fun N ↦ (hinner N).symm
    _ = x / (1 - x) ^ 2 * (x / (1 - x) + 1) := key.symm
    _ = x / (1 - x) ^ 3 := by
        field_simp
        ring

/-- The series `∑_{d≥1} (d choose 2)·xᵈ = x²/(1-x)³`: the Cauchy product of the geometric
series with `hasSum_geometric_deriv`. These are the coefficients of the `uᵈ`-half of the
`y`-coordinate of Tate's uniformisation. -/
theorem TateCurve.hasSum_geometric_sq_div_cube {x : k} (hx : valuation k x < 1) :
    HasSum (fun j : ℕ ↦ (((j + 1).choose 2 : ℕ) : k) * x ^ (j + 1)) (x ^ 2 / (1 - x) ^ 3) := by
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx
  have h1x : (1 : k) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hgeo₁ := hasSum_geometric_succ hx
  have hderiv := hasSum_geometric_deriv hx
  have hdouble : Summable fun p : ℕ × ℕ ↦
      x ^ (p.1 + 1) * (((p.2 + 1 : ℕ) : k) * x ^ (p.2 + 1)) := by
    refine summable_of_valuation_le_pow hx (fun p ↦ p.1 + p.2) (fun N ↦ ?_) fun p ↦ ?_
    · exact ((Set.finite_Iio N).prod (Set.finite_Iio N)).subset fun p hp ↦
        Set.mem_prod.mpr ⟨Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_right _ _) hp),
          Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_left _ _) hp)⟩
    · rw [map_mul, map_mul, map_pow, map_pow]
      calc valuation k x ^ (p.1 + 1) * (valuation k ((p.2 + 1 : ℕ) : k) *
            valuation k x ^ (p.2 + 1))
          ≤ valuation k x ^ (p.1 + 1) * (1 * valuation k x ^ (p.2 + 1)) :=
            mul_le_mul' le_rfl (mul_le_mul_left (valuation_natCast_le_one _) _)
        _ = valuation k x ^ (p.1 + 1 + (p.2 + 1)) := by rw [one_mul, ← pow_add]
        _ ≤ valuation k x ^ (p.1 + p.2) :=
            pow_le_pow_right_of_le_one' hx.le (by omega)
  have key := hgeo₁.summable.tsum_mul_tsum_eq_tsum_sum_antidiagonal hderiv.summable hdouble
  rw [hgeo₁.tsum_eq, hderiv.tsum_eq] at key
  have hinner : ∀ N : ℕ,
      (∑ kl ∈ Finset.antidiagonal N, x ^ (kl.1 + 1) * (((kl.2 + 1 : ℕ) : k) * x ^ (kl.2 + 1)))
      = (((N + 2).choose 2 : ℕ) : k) * x ^ (N + 2) := fun N ↦ by
    have h1 : ∀ kl ∈ Finset.antidiagonal N,
        x ^ (kl.1 + 1) * (((kl.2 + 1 : ℕ) : k) * x ^ (kl.2 + 1))
        = ((kl.2 + 1 : ℕ) : k) * x ^ (N + 2) := by
      intro kl hkl
      rw [Finset.mem_antidiagonal] at hkl
      rw [mul_left_comm, ← pow_add]
      congr 2
      omega
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← Nat.cast_sum,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    congr 2
    calc ∑ i ∈ Finset.range (N + 1), (N - i + 1)
        = ∑ i ∈ Finset.range (N + 1), (i + 1) := Finset.sum_range_reflect (fun j ↦ j + 1) (N + 1)
      _ = (N + 2).choose 2 := sum_range_succ_choose_two N
  have h2 : HasSum (fun N : ℕ ↦ (((N + 2).choose 2 : ℕ) : k) * x ^ (N + 2))
      (x / (1 - x) * (x / (1 - x) ^ 2)) := by
    have hsummable : Summable fun N : ℕ ↦ (((N + 2).choose 2 : ℕ) : k) * x ^ (N + 2) := by
      refine summable_of_valuation_le_pow hx (fun j ↦ j) (fun N ↦ Set.finite_Iio N) fun j ↦ ?_
      rw [map_mul, map_pow]
      calc valuation k (((j + 2).choose 2 : ℕ) : k) * valuation k x ^ (j + 2)
          ≤ 1 * valuation k x ^ (j + 2) := mul_le_mul_left (valuation_natCast_le_one _) _
        _ = valuation k x ^ (j + 2) := one_mul _
        _ ≤ valuation k x ^ j := pow_le_pow_right_of_le_one' hx.le (by omega)
    refine hsummable.hasSum_iff.mpr ?_
    calc ∑' N : ℕ, (((N + 2).choose 2 : ℕ) : k) * x ^ (N + 2)
        = ∑' N : ℕ, ∑ kl ∈ Finset.antidiagonal N,
            x ^ (kl.1 + 1) * (((kl.2 + 1 : ℕ) : k) * x ^ (kl.2 + 1)) :=
          tsum_congr fun N ↦ (hinner N).symm
      _ = x / (1 - x) * (x / (1 - x) ^ 2) := key.symm
  have h3 := (hasSum_nat_add_iff
    (f := fun j : ℕ ↦ (((j + 1).choose 2 : ℕ) : k) * x ^ (j + 1)) 1).mp h2
  have hval : x / (1 - x) * (x / (1 - x) ^ 2) +
      ∑ i ∈ Finset.range 1, (((i + 1).choose 2 : ℕ) : k) * x ^ (i + 1) = x ^ 2 / (1 - x) ^ 3 := by
    rw [Finset.sum_range_one, show Nat.choose 1 2 = 0 from rfl, Nat.cast_zero, zero_mul,
      add_zero, div_mul_div_comm, show x * x = x ^ 2 by ring,
      show (1 - x) * (1 - x) ^ 2 = (1 - x) ^ 3 by ring]
  rwa [hval] at h3

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The inversion symmetry of the summands of `tateX`: `v/(1-v)² = v⁻¹/(1-v⁻¹)²`. This is
what makes the two-sided sum `∑_{n ∈ ℤ}` symmetric under `(u, n) ↦ (u⁻¹, -n)`, and it
converts the `n ≤ -1` half of the sum into geometric series in `q^{-n}u⁻¹`. -/
theorem TateCurve.div_one_sub_sq_inv {v : k} (hv : v ≠ 0) :
    v / (1 - v) ^ 2 = v⁻¹ / (1 - v⁻¹) ^ 2 := by
  rcases eq_or_ne v 1 with rfl | hv1
  · simp
  · have h1 : (1 : k) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
    have h2 : (1 : k) - v⁻¹ ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h ↦ hv1 (by rw [← inv_inv v, ← h, inv_one])
    field_simp
    ring

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The inversion antisymmetry of the summands of `tateY`:
`v²/(1-v)³ = -(v⁻¹/(1-v⁻¹)³)`. It converts the `n ≤ -1` half of the `y`-coordinate sum
into (negated) geometric series in `q^{-n}u⁻¹`, and is the source of the asymmetric
coefficients `(d choose 2)uᵈ - (d+1 choose 2)u⁻ᵈ` in Silverman's `q`-expansion. -/
theorem TateCurve.sq_div_one_sub_cube_inv {v : k} (hv : v ≠ 0) :
    v ^ 2 / (1 - v) ^ 3 = -(v⁻¹ / (1 - v⁻¹) ^ 3) := by
  rcases eq_or_ne v 1 with rfl | hv1
  · simp
  · have h1 : (1 : k) - v ≠ 0 := sub_ne_zero.mpr (Ne.symm hv1)
    have h2 : (1 : k) - v⁻¹ ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h ↦ hv1 (by rw [← inv_inv v, ← h, inv_one])
    field_simp
    ring

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The sublevel sets of `(d, e) ↦ de` on `ℕ+ × ℕ+` are finite. -/
theorem TateCurve.finite_pnat_mul_lt (N : ℕ) :
    {p : ℕ+ × ℕ+ | (p.1 : ℕ) * (p.2 : ℕ) < N}.Finite := by
  refine (((Set.finite_Iio N).preimage PNat.coe_injective.injOn).prod
    ((Set.finite_Iio N).preimage PNat.coe_injective.injOn)).subset fun p hp ↦ ?_
  have h1 : (p.1 : ℕ) ≤ (p.1 : ℕ) * (p.2 : ℕ) := Nat.le_mul_of_pos_right _ p.2.pos
  have h2 : (p.2 : ℕ) ≤ (p.1 : ℕ) * (p.2 : ℕ) := Nat.le_mul_of_pos_left _ p.1.pos
  exact Set.mem_prod.mpr ⟨Set.mem_preimage.mpr (Set.mem_Iio.mpr (lt_of_le_of_lt h1 hp)),
    Set.mem_preimage.mpr (Set.mem_Iio.mpr (lt_of_le_of_lt h2 hp))⟩

/-- Regrouping a double power series along `(d, e) ↦ de`: the `k`-coefficient core of the
Lambert rearrangement (`tsum_lambert` is the `ℤ`-coefficient case, composed with the
geometric expansion of `qᵈ/(1-qᵈ)`). Summability of the double family is a hypothesis, to
accommodate the annulus weights `d·u^{-d}`, whose natural bound is by powers of `q·u⁻¹`
rather than `q`. -/
theorem TateCurve.hasSum_sum_divisors_mul_pow (x : k) (w : ℕ → k)
    (hsum : Summable fun p : ℕ+ × ℕ+ ↦ w (p.1 : ℕ) * x ^ ((p.1 : ℕ) * (p.2 : ℕ))) :
    HasSum (fun N : ℕ ↦ (∑ d ∈ N.divisors, w d) * x ^ N)
      (∑' p : ℕ+ × ℕ+, w (p.1 : ℕ) * x ^ ((p.1 : ℕ) * (p.2 : ℕ))) := by
  obtain ⟨S, hS⟩ := hsum
  have hsigma : HasSum ((fun p : ℕ+ × ℕ+ ↦ w (p.1 : ℕ) * x ^ ((p.1 : ℕ) * (p.2 : ℕ))) ∘
      ⇑sigmaAntidiagonalEquivProd) S :=
    sigmaAntidiagonalEquivProd.hasSum_iff.mpr hS
  have hfib : ∀ N : ℕ+, HasSum (fun y : (Nat.divisorsAntidiagonal (N : ℕ)) ↦
      ((fun p : ℕ+ × ℕ+ ↦ w (p.1 : ℕ) * x ^ ((p.1 : ℕ) * (p.2 : ℕ))) ∘
        ⇑sigmaAntidiagonalEquivProd) ⟨N, y⟩)
      ((∑ d ∈ (N : ℕ).divisors, w d) * x ^ (N : ℕ)) := by
    intro N
    have hterm : ∀ y : (Nat.divisorsAntidiagonal (N : ℕ)),
        ((fun p : ℕ+ × ℕ+ ↦ w (p.1 : ℕ) * x ^ ((p.1 : ℕ) * (p.2 : ℕ))) ∘
          ⇑sigmaAntidiagonalEquivProd) ⟨N, y⟩ = w (y : ℕ × ℕ).1 * x ^ (N : ℕ) := by
      intro y
      have hy := (Nat.mem_divisorsAntidiagonal.mp y.2).1
      simp only [Function.comp_apply, sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk,
        divisorsAntidiagonalFactors, PNat.mk_coe]
      rw [hy]
    convert hasSum_fintype _ using 1
    · symm
      rw [Finset.univ_eq_attach, Finset.sum_congr rfl fun y _ ↦ hterm y,
        Finset.sum_attach (Nat.divisorsAntidiagonal (N : ℕ)) (fun y ↦ w y.1 * x ^ (N : ℕ)),
        ← Finset.sum_mul, Nat.sum_divisorsAntidiagonal (fun d _ ↦ w d)]
  have hcolsPNat : HasSum (fun N : ℕ+ ↦ (∑ d ∈ (N : ℕ).divisors, w d) * x ^ (N : ℕ)) S :=
    hsigma.sigma hfib
  have hcols : HasSum (fun N : ℕ ↦ (∑ d ∈ N.divisors, w d) * x ^ N) S := by
    refine (PNat.coe_injective.hasSum_iff fun n hn ↦ ?_).mp hcolsPNat
    cases n with
    | zero => simp
    | succ n => exact absurd ⟨n.succPNat, rfl⟩ hn
  rwa [hS.tsum_eq]

/-- Workhorse for the annulus expansions: if `g` has the geometric-type expansion
`g x = ∑_{d ≥ 1} a(d)·xᵈ` on the open unit disc, then the row sums `∑_n g(qⁿ⁺¹t)`
regroup along `(d, e) ↦ de` into a `q`-power series with divisor-sum coefficients
`∑_{d ∣ N} a(d)·tᵈ`. Both `HasSum`s are returned with a common (junk-free) value.
Summability of the double family is a hypothesis, to accommodate both `t = u` (bounded
by powers of `q`) and `t = u⁻¹` (bounded by powers of `q·u⁻¹`). -/
theorem TateCurve.hasSum_geom_rows (q t : k) (a : ℕ → ℕ) (g : k → k)
    (hgeo : ∀ x : k, valuation k x < 1 →
      HasSum (fun j : ℕ ↦ ((a (j + 1) : ℕ) : k) * x ^ (j + 1)) (g x))
    (hlt : ∀ n : ℕ, valuation k (q ^ (n + 1) * t) < 1)
    (hsum : Summable fun p : ℕ+ × ℕ+ ↦
      ((a (p.1 : ℕ) : ℕ) : k) * t ^ (p.1 : ℕ) * q ^ ((p.1 : ℕ) * (p.2 : ℕ))) :
    ∃ T : k, HasSum (fun n : ℕ ↦ g (q ^ (n + 1) * t)) T ∧
      HasSum (fun N : ℕ ↦ (∑ d ∈ N.divisors, ((a d : ℕ) : k) * t ^ d) * q ^ N) T := by
  have hdouble : Summable fun p : ℕ × ℕ ↦
      ((a (p.2 + 1) : ℕ) : k) * (q ^ (p.1 + 1) * t) ^ (p.2 + 1) := by
    have he := ((Equiv.prodComm ℕ ℕ).trans
      (Equiv.prodCongr Equiv.pnatEquivNat.symm Equiv.pnatEquivNat.symm)).summable_iff.mpr hsum
    refine he.congr fun p ↦ ?_
    change ((a (p.2 + 1) : ℕ) : k) * t ^ (p.2 + 1) * q ^ ((p.2 + 1) * (p.1 + 1)) = _
    rw [mul_pow, ← pow_mul]
    ring
  have hrows : HasSum (fun n : ℕ ↦ g (q ^ (n + 1) * t)) (∑' p : ℕ × ℕ,
      ((a (p.2 + 1) : ℕ) : k) * (q ^ (p.1 + 1) * t) ^ (p.2 + 1)) :=
    hdouble.hasSum.prod_fiberwise fun n ↦ hgeo _ (hlt n)
  have hreg : HasSum (fun N : ℕ ↦ (∑ d ∈ N.divisors, ((a d : ℕ) : k) * t ^ d) * q ^ N)
      (∑' p : ℕ+ × ℕ+, ((a (p.1 : ℕ) : ℕ) : k) * t ^ (p.1 : ℕ) * q ^ ((p.1 : ℕ) * (p.2 : ℕ))) :=
    hasSum_sum_divisors_mul_pow q (fun d ↦ ((a d : ℕ) : k) * t ^ d) hsum
  refine ⟨_, hrows, ?_⟩
  convert hreg using 1
  rw [← ((Equiv.prodComm ℕ ℕ).trans (Equiv.prodCongr Equiv.pnatEquivNat.symm
    Equiv.pnatEquivNat.symm)).tsum_eq (fun p : ℕ+ × ℕ+ ↦
      ((a (p.1 : ℕ) : ℕ) : k) * t ^ (p.1 : ℕ) * q ^ ((p.1 : ℕ) * (p.2 : ℕ)))]
  refine tsum_congr fun p ↦ ?_
  change ((a (p.2 + 1) : ℕ) : k) * (q ^ (p.1 + 1) * t) ^ (p.2 + 1) =
    ((a (p.2 + 1) : ℕ) : k) * t ^ (p.2 + 1) * q ^ ((p.2 + 1) * (p.1 + 1))
  rw [mul_pow, ← pow_mul]
  ring

open scoped ArithmeticFunction.sigma in
/-- The Lambert series rearrangement `∑_{n≥1} n³qⁿ/(1-qⁿ) = ∑_{n≥1} σ₃(n)qⁿ` for
`|q| < 1`: the defining series of `tateA₄` is the evaluation of the formal series
`a₄(q) = -5s₃(q) ∈ ℤ⟦q⟧`. -/
theorem WeierstrassCurve.tateA₄_eq_evalInt (q : k) (hq : valuation k q < 1) :
    tateA₄ q = TateCurve.evalInt q TateCurve.a₄Formal := by
  have hF : ∀ n, PowerSeries.coeff n TateCurve.a₄Formal
      = ∑ d ∈ n.divisors, -5 * (d : ℤ) ^ 3 := by
    intro n
    rw [TateCurve.coeff_a₄Formal, ArithmeticFunction.sigma_apply]
    push_cast
    rw [Finset.mul_sum]
  rw [← TateCurve.tsum_lambert_eq_evalInt q hq _ hF]
  simp only [tateA₄]
  rw [← tsum_mul_left]
  exact tsum_congr fun m ↦ by push_cast; ring

open scoped ArithmeticFunction.sigma in
/-- The Lambert series rearrangement for `tateA₆`, as for `tateA₄_eq_evalInt`; the
bookkeeping of the exact division by `12` uses `12 ∣ 5d³ + 7d⁵` termwise. -/
theorem WeierstrassCurve.tateA₆_eq_evalInt (q : k) (hq : valuation k q < 1) :
    tateA₆ q = TateCurve.evalInt q TateCurve.a₆Formal := by
  have h12 : ∀ d : ℤ, (12 : ℤ) ∣ 5 * d ^ 3 + 7 * d ^ 5 := by
    intro d
    have hz : ((5 * d ^ 3 + 7 * d ^ 5 : ℤ) : ZMod 12) = 0 := by
      push_cast
      generalize (d : ZMod 12) = r
      revert r
      decide
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp hz
  set c : ℕ → ℤ := fun d ↦ -((5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) / 12) with hc
  -- the coefficients of `a₆Formal` are the divisor sums of `c`: the divisor sum commutes
  -- with the exact division by `12`
  have hF : ∀ N, PowerSeries.coeff N TateCurve.a₆Formal = ∑ d ∈ N.divisors, c d := by
    intro N
    rw [TateCurve.coeff_a₆Formal]
    symm
    simp only [hc]
    have hσ : ∑ d ∈ N.divisors, (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5)
        = 5 * (σ 3 N : ℤ) + 7 * (σ 5 N : ℤ) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ArithmeticFunction.sigma_apply, ArithmeticFunction.sigma_apply]
      push_cast
      ring
    have hsum : (12 : ℤ) ∣ 5 * (σ 3 N : ℤ) + 7 * (σ 5 N : ℤ) := by
      rw [← hσ]
      exact Finset.dvd_sum fun d _ ↦ h12 d
    have hterm : ∀ d ∈ N.divisors, -((5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) / 12) * 12
        = -(5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) := fun d _ ↦ by
      rw [neg_mul, Int.ediv_mul_cancel (h12 d)]
    apply mul_right_cancel₀ (b := (12 : ℤ)) (by norm_num)
    rw [Finset.sum_mul, Finset.sum_congr rfl hterm, neg_mul, Int.ediv_mul_cancel hsum,
      ← hσ, Finset.sum_neg_distrib]
  rw [← TateCurve.tsum_lambert_eq_evalInt q hq c hF]
  simp only [tateA₆]
  refine tsum_congr fun m ↦ ?_
  simp only [hc]
  push_cast
  ring

open PowerSeries in
open scoped PowerSeries.WithPiTopology in
/-- Evaluation of the formal `η²⁴` product: for `|q| < 1` the formal series
`ΔFormal = X(∏(1-Xⁿ))²⁴ ∈ ℤ⟦X⟧` evaluates to the convergent product `q∏(1-qⁿ)²⁴` in `k`.
The evaluated finite partial products converge to `evalInt q (∏(1-Xⁿ⁺¹))` because the
difference has vanishing low coefficients (`coeff_prod_one_sub_X_pow_stable`), hence
small valuation (`valuation_evalInt_le_pow`); this is the statement `HasProd`, and the
rest is multiplicativity of `evalInt`. -/
theorem TateCurve.evalInt_ΔFormal (q : k) (hq : valuation k q < 1) :
    evalInt q ΔFormal = q * ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 := by
  -- evaluation is multiplicative on finite partial products
  have hfin : ∀ s : Finset ℕ, evalInt q (∏ n ∈ s, ((1 : ℤ⟦X⟧) - PowerSeries.X ^ (n + 1))) =
      ∏ n ∈ s, (1 - q ^ (n + 1)) := by
    intro s
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.prod_cons, evalInt_mul q hq, ih,
        evalInt_sub (summable_evalInt q hq 1) (summable_evalInt q hq (PowerSeries.X ^ (a + 1))),
        evalInt_one, evalInt_pow q hq, evalInt_X]
  -- the core: the evaluated partial products converge to the evaluated formal product
  have hprod : HasProd (fun n : ℕ ↦ 1 - q ^ (n + 1))
      (evalInt q (∏' n : ℕ, ((1 : ℤ⟦X⟧) - PowerSeries.X ^ (n + 1)))) := by
    simp only [HasProd, SummationFilter.unconditional_filter]
    rw [(IsValuativeTopology.hasBasis_nhds _).tendsto_right_iff]
    intro γ _
    obtain ⟨N, hN⟩ := exists_pow_valuation_lt q hq γ
    filter_upwards [Filter.eventually_ge_atTop (Finset.range (N + 1))] with s hs
    rw [← hfin s, ← evalInt_sub (summable_evalInt q hq _) (summable_evalInt q hq _)]
    refine lt_of_le_of_lt ((valuation_evalInt_le_pow q hq (M := N + 1)
      fun m hm ↦ ?_).trans (pow_le_pow_right_of_le_one' hq.le (Nat.le_succ N))) hN
    -- the difference of the partial and the full product has no low coefficients
    rw [map_sub, coeff_tprod_one_sub_X_pow m,
      coeff_prod_one_sub_X_pow_stable (Finset.range_subset_range.mpr (Nat.le_succ m))
        ((Finset.range_subset_range.mpr hm).trans hs), sub_self]
  -- promote to the 24-th powers and assemble
  have hpow : ∀ j : ℕ, HasProd (fun n : ℕ ↦ (1 - q ^ (n + 1)) ^ j)
      (evalInt q (∏' n : ℕ, ((1 : ℤ⟦X⟧) - PowerSeries.X ^ (n + 1))) ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => simpa only [pow_succ, Pi.mul_apply] using ih.mul hprod
  rw [(hpow 24).tprod_eq]
  simp only [ΔFormal]
  rw [evalInt_mul q hq, evalInt_pow q hq, evalInt_X]

/-- Silverman, ATAEC V.1.1(b): the discriminant of the Tate curve is
`Δ(q) = q∏_{n≥1}(1 - qⁿ)²⁴`. In particular, for `q ≠ 0` each factor of the right-hand
side is a unit of `𝒪[k]`, so `Δ(q) ≠ 0` and `E_q` is an elliptic curve.

The proof is a pure assembly: expand the Weierstrass discriminant of
`y² + xy = x³ + a₄x + a₆` as a polynomial in `a₄, a₆`, replace `tateA₄ q`, `tateA₆ q` by
evaluations of the formal series (`tateA₄_eq_evalInt`, `tateA₆_eq_evalInt`), pull the
polynomial through the ring homomorphism `evalInt q` (`evalInt_add/sub/mul/pow/C_mul`),
apply Jacobi's formal discriminant identity `TateCurve.ΔFormal_eq` in `ℤ⟦q⟧`, and
evaluate the resulting product (`evalInt_ΔFormal`). -/
theorem WeierstrassCurve.tateΔ_eq_prod (q : k) (hq : valuation k q < 1) :
    (tateCurve q).Δ = q * ∏' n : ℕ, (1 - q ^ (n + 1)) ^ 24 := by
  have hS : ∀ F : ℤ⟦X⟧, Summable fun n ↦ ((PowerSeries.coeff n F : ℤ) : k) * q ^ n :=
    TateCurve.summable_evalInt q hq
  -- the Weierstrass discriminant of `E_q`, explicitly: `b₂ = 1`, `b₄ = 2a₄`, `b₆ = 4a₆`,
  -- `b₈ = a₆ - a₄²` give `Δ = a₄² - a₆ - 64a₄³ + 72a₄a₆ - 432a₆²`
  have h1 : (tateCurve q).Δ = tateA₄ q ^ 2 - tateA₆ q - 64 * tateA₄ q ^ 3 +
      72 * (tateA₄ q * tateA₆ q) - 432 * tateA₆ q ^ 2 := by
    simp only [tateCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  rw [h1, tateA₄_eq_evalInt q hq, tateA₆_eq_evalInt q hq, ← TateCurve.evalInt_ΔFormal q hq,
    TateCurve.ΔFormal_eq, TateCurve.evalInt_sub (hS _) (hS _),
    TateCurve.evalInt_add (hS _) (hS _), TateCurve.evalInt_sub (hS _) (hS _),
    TateCurve.evalInt_sub (hS _) (hS _), TateCurve.evalInt_C_mul, TateCurve.evalInt_C_mul,
    TateCurve.evalInt_C_mul, TateCurve.evalInt_mul q hq, TateCurve.evalInt_pow q hq,
    TateCurve.evalInt_pow q hq, TateCurve.evalInt_pow q hq]
  push_cast
  ring

/-- The discriminant of the Tate curve is the evaluation of the formal discriminant. -/
theorem WeierstrassCurve.tateCurve_Δ_eq_evalInt (q : k) (hq : valuation k q < 1) :
    (tateCurve q).Δ = TateCurve.evalInt q TateCurve.ΔFormal := by
  rw [tateΔ_eq_prod q hq, TateCurve.evalInt_ΔFormal q hq]

/-- `c₄` of the Tate curve is the evaluation of the Eisenstein series `E₄ = 1 + 240s₃`. -/
theorem WeierstrassCurve.tateCurve_c₄_eq_evalInt (q : k) (hq : valuation k q < 1) :
    (tateCurve q).c₄ = TateCurve.evalInt q TateCurve.c₄Formal := by
  have h1 : (tateCurve q).c₄ = 1 - 48 * tateA₄ q := by
    simp only [tateCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have h2 : TateCurve.c₄Formal = 1 - PowerSeries.C 48 * TateCurve.a₄Formal := by
    simp only [TateCurve.c₄Formal, TateCurve.a₄Formal, map_ofNat]
    ring
  rw [h1, tateA₄_eq_evalInt q hq, h2,
    TateCurve.evalInt_sub (TateCurve.summable_evalInt q hq _)
      (TateCurve.summable_evalInt q hq _),
    TateCurve.evalInt_one, TateCurve.evalInt_C_mul]
  push_cast
  ring

/-- For `q ≠ 0` in the open unit disc, `|Δ(q)| = |q|`: the discriminant of the Tate curve
is `q + O(q²)`, and the leading term dominates ultrametrically. -/
theorem WeierstrassCurve.valuation_tateCurve_Δ (q : k) (hq0 : q ≠ 0)
    (hq : valuation k q < 1) : valuation k (tateCurve q).Δ = valuation k q := by
  rw [tateCurve_Δ_eq_evalInt q hq]
  exact TateCurve.valuation_evalInt_eq q hq0 hq TateCurve.constantCoeff_ΔFormal
    TateCurve.coeff_one_ΔFormal

/-- The Tate curve of a nonzero `q` in the open unit disc has nonvanishing discriminant
(so it is an elliptic curve). -/
theorem WeierstrassCurve.tateCurve_Δ_ne_zero (q : k) (hq0 : q ≠ 0)
    (hq : valuation k q < 1) : (tateCurve q).Δ ≠ 0 := by
  intro h
  have hv := valuation_tateCurve_Δ q hq0 hq
  rw [h, map_zero] at hv
  exact (valuation k).ne_zero_iff.mpr hq0 hv.symm

/-- `|c₄(q)| = 1` on the open unit disc: `c₄ = 1 + O(q)`. -/
theorem WeierstrassCurve.valuation_tateCurve_c₄ (q : k) (hq : valuation k q < 1) :
    valuation k (tateCurve q).c₄ = 1 := by
  rw [tateCurve_c₄_eq_evalInt q hq]
  have hsplit : TateCurve.evalInt q TateCurve.c₄Formal =
      1 + TateCurve.evalInt q (TateCurve.c₄Formal - 1) := by
    conv_lhs => rw [show TateCurve.c₄Formal = 1 + (TateCurve.c₄Formal - 1) by ring]
    rw [TateCurve.evalInt_add (TateCurve.summable_evalInt q hq _)
      (TateCurve.summable_evalInt q hq _), TateCurve.evalInt_one]
  have htail : valuation k (TateCurve.evalInt q (TateCurve.c₄Formal - 1)) < 1 := by
    refine lt_of_le_of_lt (TateCurve.valuation_evalInt_le_pow q hq (M := 1) fun m hm ↦ ?_)
      (by rwa [pow_one])
    rcases m with - | m
    · simp [PowerSeries.coeff_zero_eq_constantCoeff, TateCurve.constantCoeff_c₄Formal]
    · exact absurd hm (by omega)
  rw [hsplit, (valuation k).map_add_eq_of_lt_left (by rwa [map_one]), map_one]

theorem WeierstrassCurve.tateCurve_c₄_ne_zero (q : k) (hq : valuation k q < 1) :
    (tateCurve q).c₄ ≠ 0 := by
  intro h
  have hv := valuation_tateCurve_c₄ q hq
  rw [h, map_zero] at hv
  exact zero_ne_one hv
