/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram, Samuel Yin
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurveSeries

import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import FLT.Slop.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# The Tate curve `E_q`: the Weierstrass equation of the uniformisation

The `qᶻ`-invariance of the coordinate series (`tateX_zpow_mul_left`, `tateY_zpow_mul_left`),
Silverman's `q`-expansions of `X` and `Y` on the fundamental annulus `|q| < |u| ≤ 1`
(`tateX_eq_annulus`, `tateY_eq_annulus`), the evaluation calculus `TateCurve.evalK` /
`TateCurve.EvalBounded` on `k`-coefficient power series, and the proof that `(X(u, q), Y(u, q))`
lies on `E_q` (`tateCurve_equation`, `tateCurve_nonsingular`).

Second of the files split out of `TateCurveUniformisation`.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄k).Point` notation for the group of `k`-points
open scoped PowerSeries -- `ℤ⟦X⟧` notation for `PowerSeries ℤ`
open scoped Topology -- `𝓝` notation for neighbourhood filters
open ValuativeRel -- `𝒪[k]` notation for the ring of integers of `k`, and `valuation`

-- Can be deleted when mathlib#41391 lands
set_option linter.overlappingInstances false

-- let k be a nonarchimedean local field
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The `x`-coordinate series of Tate's uniformisation is invariant under `u ↦ qu`:
reindex the `ℤ`-indexed sum by `n ↦ n + 1`. This is the invariance that makes
`tateCurvePoint` descend to the quotient `kˣ/qᶻ`. -/
theorem WeierstrassCurve.tateX_mul_left (q : kˣ) (u : k) :
    tateX ((q : k) * u) (q : k) = tateX u (q : k) := by
  simp only [tateX]
  congr 1
  calc ∑' n : ℤ, (q : k) ^ n * ((q : k) * u) / (1 - (q : k) ^ n * ((q : k) * u)) ^ 2
      = ∑' n : ℤ, (q : k) ^ (n + 1) * u / (1 - (q : k) ^ (n + 1) * u) ^ 2 := by
        refine tsum_congr fun n ↦ ?_
        rw [zpow_add_one₀ (Units.ne_zero q)]
        ring
    _ = ∑' n : ℤ, (q : k) ^ n * u / (1 - (q : k) ^ n * u) ^ 2 :=
        (Equiv.addRight (1 : ℤ)).tsum_eq
          fun n ↦ (q : k) ^ n * u / (1 - (q : k) ^ n * u) ^ 2

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The `y`-coordinate series of Tate's uniformisation is invariant under `u ↦ qu`. -/
theorem WeierstrassCurve.tateY_mul_left (q : kˣ) (u : k) :
    tateY ((q : k) * u) (q : k) = tateY u (q : k) := by
  simp only [tateY]
  congr 1
  calc ∑' n : ℤ, ((q : k) ^ n * ((q : k) * u)) ^ 2 / (1 - (q : k) ^ n * ((q : k) * u)) ^ 3
      = ∑' n : ℤ, ((q : k) ^ (n + 1) * u) ^ 2 / (1 - (q : k) ^ (n + 1) * u) ^ 3 := by
        refine tsum_congr fun n ↦ ?_
        rw [zpow_add_one₀ (Units.ne_zero q)]
        ring
    _ = ∑' n : ℤ, ((q : k) ^ n * u) ^ 2 / (1 - (q : k) ^ n * u) ^ 3 :=
        (Equiv.addRight (1 : ℤ)).tsum_eq
          fun n ↦ ((q : k) ^ n * u) ^ 2 / (1 - (q : k) ^ n * u) ^ 3

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The `x`-coordinate series is invariant under `u ↦ qᵐu` for every `m : ℤ`. -/
theorem WeierstrassCurve.tateX_zpow_mul_left (q : kˣ) (m : ℤ) (u : k) :
    tateX ((q : k) ^ m * u) (q : k) = tateX u (q : k) := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
      rw [show (q : k) ^ ((m : ℤ) + 1) * u = (q : k) * ((q : k) ^ (m : ℤ) * u) by
        rw [zpow_add_one₀ (Units.ne_zero q)]; ring, tateX_mul_left, ih]
  | pred m ih =>
      have h1 := tateX_mul_left q ((q : k) ^ (-(m : ℤ) - 1) * u)
      rw [show (q : k) * ((q : k) ^ (-(m : ℤ) - 1) * u) = (q : k) ^ (-(m : ℤ) - 1 + 1) * u by
        rw [zpow_add_one₀ (Units.ne_zero q)]; ring, Int.sub_add_cancel] at h1
      exact h1.symm.trans ih

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The `y`-coordinate series is invariant under `u ↦ qᵐu` for every `m : ℤ`. -/
theorem WeierstrassCurve.tateY_zpow_mul_left (q : kˣ) (m : ℤ) (u : k) :
    tateY ((q : k) ^ m * u) (q : k) = tateY u (q : k) := by
  induction m using Int.induction_on with
  | zero => simp
  | succ m ih =>
      rw [show (q : k) ^ ((m : ℤ) + 1) * u = (q : k) * ((q : k) ^ (m : ℤ) * u) by
        rw [zpow_add_one₀ (Units.ne_zero q)]; ring, tateY_mul_left, ih]
  | pred m ih =>
      have h1 := tateY_mul_left q ((q : k) ^ (-(m : ℤ) - 1) * u)
      rw [show (q : k) * ((q : k) ^ (-(m : ℤ) - 1) * u) = (q : k) ^ (-(m : ℤ) - 1 + 1) * u by
        rw [zpow_add_one₀ (Units.ne_zero q)]; ring, Int.sub_add_cancel] at h1
      exact h1.symm.trans ih

/-- Silverman's `q`-expansion of the `x`-coordinate on the annulus `|q| < |u| ≤ 1`:
`X(u, q) = u/(1-u)² + ∑_{N ≥ 1} (∑_{d ∣ N} (d·uᵈ + d·u⁻ᵈ - 2d))·qᴺ`. The two halves of
the two-sided sum expand geometrically (`hasSum_geom_rows` with `hasSum_geometric_deriv`,
the `n ≤ -1` half after the inversion `div_one_sub_sq_inv`), and the Lambert correction
regroups by `tsum_lambert`. -/
theorem WeierstrassCurve.tateX_eq_annulus (q u : kˣ) (hq : valuation k (q : k) < 1)
    (h₁ : valuation k (q : k) < valuation k (u : k)) (h₂ : valuation k (u : k) ≤ 1) :
    tateX (u : k) (q : k) = (u : k) / (1 - (u : k)) ^ 2 +
      ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : k) * (u : k) ^ d
        + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ N := by
  have hq0 : (q : k) ≠ 0 := Units.ne_zero q
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr hu0
  have hρ : valuation k ((q : k) * (u : k)⁻¹) < 1 := by
    rw [map_mul, map_inv₀, ← div_eq_mul_inv]
    exact (div_lt_one₀ (TateCurve.valuation_unit_pos u)).mpr h₁
  -- the discs on which the geometric expansions are valid
  have hposlt : ∀ n : ℕ, valuation k ((q : k) ^ (n + 1) * (u : k)) < 1 := by
    intro n
    rw [map_mul, map_pow]
    calc valuation k (q : k) ^ (n + 1) * valuation k (u : k)
        ≤ valuation k (q : k) ^ (n + 1) * 1 := mul_le_mul' le_rfl h₂
      _ = valuation k (q : k) ^ (n + 1) := mul_one _
      _ ≤ valuation k (q : k) ^ 1 := pow_le_pow_right_of_le_one' hq.le (by omega)
      _ = valuation k (q : k) := pow_one _
      _ < 1 := hq
  have hneglt : ∀ n : ℕ, valuation k ((q : k) ^ (n + 1) * (u : k)⁻¹) < 1 := by
    intro n
    refine lt_of_le_of_lt ?_ hρ
    rw [map_mul, map_mul, map_pow]
    refine mul_le_mul' ?_ le_rfl
    calc valuation k (q : k) ^ (n + 1) ≤ valuation k (q : k) ^ 1 :=
          pow_le_pow_right_of_le_one' hq.le (by omega)
      _ = valuation k (q : k) := pow_one _
  -- summability of the two double families
  have hsumApos : Summable fun p : ℕ+ × ℕ+ ↦
      ((p.1 : ℕ) : k) * (u : k) ^ (p.1 : ℕ) * (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
    refine TateCurve.summable_of_valuation_le_pow hq (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ))
      (fun N ↦ TateCurve.finite_pnat_mul_lt N) fun p ↦ ?_
    rw [map_mul, map_mul, map_pow, map_pow]
    calc valuation k ((p.1 : ℕ) : k) * valuation k (u : k) ^ (p.1 : ℕ) *
          valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ))
        ≤ 1 * 1 * valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
          mul_le_mul' (mul_le_mul' (valuation_natCast_le_one _)
            (pow_le_one' h₂ _)) le_rfl
      _ = valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by rw [one_mul, one_mul]
  have hsumAneg : Summable fun p : ℕ+ × ℕ+ ↦
      ((p.1 : ℕ) : k) * ((u : k)⁻¹) ^ (p.1 : ℕ) * (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
    refine TateCurve.summable_of_valuation_le_pow hρ (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ))
      (fun N ↦ TateCurve.finite_pnat_mul_lt N) fun p ↦ ?_
    simp only [map_mul, map_pow, map_inv₀]
    have h1u := TateCurve.one_le_valuation_inv (w := u) h₂
    calc valuation k ((p.1 : ℕ) : k) * (valuation k (u : k))⁻¹ ^ (p.1 : ℕ) *
          valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ))
        ≤ 1 * (valuation k (u : k))⁻¹ ^ ((p.1 : ℕ) * (p.2 : ℕ)) *
            valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
          mul_le_mul' (mul_le_mul' (valuation_natCast_le_one _)
            (pow_le_pow_right' h1u (Nat.le_mul_of_pos_right _ p.2.pos))) le_rfl
      _ = (valuation k (q : k) * (valuation k (u : k))⁻¹) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
          rw [one_mul, mul_pow, mul_comm]
  -- the two regrouped halves
  obtain ⟨TA, hrowsA, hNA⟩ := TateCurve.hasSum_geom_rows (q : k) (u : k) (fun d ↦ d)
    (fun x ↦ x / (1 - x) ^ 2) (fun x hx ↦ TateCurve.hasSum_geometric_deriv hx) hposlt hsumApos
  obtain ⟨TC, hrowsC, hNC⟩ := TateCurve.hasSum_geom_rows (q : k) ((u : k)⁻¹) (fun d ↦ d)
    (fun x ↦ x / (1 - x) ^ 2) (fun x hx ↦ TateCurve.hasSum_geometric_deriv hx) hneglt hsumAneg
  have hNA' : HasSum (fun N : ℕ ↦
      (∑ d ∈ N.divisors, ((d : ℕ) : k) * (u : k) ^ d) * (q : k) ^ N) TA := hNA
  have hNC' : HasSum (fun N : ℕ ↦
      (∑ d ∈ N.divisors, ((d : ℕ) : k) * ((u : k)⁻¹) ^ d) * (q : k) ^ N) TC := hNC
  -- rows in the shape of the two-sided sum
  have hcoe : ∀ n : ℕ, (q : k) ^ ((n : ℤ) + 1) = (q : k) ^ (n + 1) := by
    intro n
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hposrows : HasSum (fun n : ℕ ↦
      (q : k) ^ ((n : ℤ) + 1) * (u : k) / (1 - (q : k) ^ ((n : ℤ) + 1) * (u : k)) ^ 2) TA := by
    have heq : (fun n : ℕ ↦
        (q : k) ^ ((n : ℤ) + 1) * (u : k) / (1 - (q : k) ^ ((n : ℤ) + 1) * (u : k)) ^ 2) =
        fun n : ℕ ↦ (q : k) ^ (n + 1) * (u : k) / (1 - (q : k) ^ (n + 1) * (u : k)) ^ 2 := by
      funext n
      rw [hcoe n]
    rw [heq]
    exact hrowsA
  have hnegrows : HasSum (fun n : ℕ ↦ (q : k) ^ (-((n : ℤ) + 1)) * (u : k) /
      (1 - (q : k) ^ (-((n : ℤ) + 1)) * (u : k)) ^ 2) TC := by
    have heq : (fun n : ℕ ↦ (q : k) ^ (-((n : ℤ) + 1)) * (u : k) /
        (1 - (q : k) ^ (-((n : ℤ) + 1)) * (u : k)) ^ 2) =
        fun n : ℕ ↦ (q : k) ^ (n + 1) * (u : k)⁻¹ /
          (1 - (q : k) ^ (n + 1) * (u : k)⁻¹) ^ 2 := by
      funext n
      rw [zpow_neg, hcoe n,
        TateCurve.div_one_sub_sq_inv (v := ((q : k) ^ (n + 1))⁻¹ * (u : k))
          (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hq0)) hu0),
        mul_inv, inv_inv]
    rw [heq]
    exact hrowsC
  have hzsum : HasSum (fun n : ℤ ↦ (q : k) ^ n * (u : k) / (1 - (q : k) ^ n * (u : k)) ^ 2)
      (TA + (u : k) / (1 - (u : k)) ^ 2 + TC) := by
    have h := HasSum.of_add_one_of_neg_add_one
      (f := fun n : ℤ ↦ (q : k) ^ n * (u : k) / (1 - (q : k) ^ n * (u : k)) ^ 2)
      hposrows hnegrows
    simpa using h
  -- the Lambert correction
  have hσ : Summable fun N : ℕ ↦ (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N := by
    refine TateCurve.summable_of_valuation_le_pow hq (fun N ↦ N)
      (fun N ↦ Set.finite_Iio N) fun N ↦ ?_
    rw [map_mul, map_pow]
    calc valuation k (∑ d ∈ N.divisors, ((d : ℕ) : k)) * valuation k (q : k) ^ N
        ≤ 1 * valuation k (q : k) ^ N :=
          mul_le_mul_left ((valuation k).map_sum_le
            fun d _ ↦ valuation_natCast_le_one d) _
      _ = valuation k (q : k) ^ N := one_mul _
  have hlam : (∑' m : ℕ, ((m + 1 : ℕ) : k) * (q : k) ^ (m + 1) / (1 - (q : k) ^ (m + 1)))
      = ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N := by
    calc ∑' m : ℕ, ((m + 1 : ℕ) : k) * (q : k) ^ (m + 1) / (1 - (q : k) ^ (m + 1))
        = ∑' m : ℕ, (((fun d ↦ (d : ℤ)) (m + 1) : ℤ) : k) * (q : k) ^ (m + 1) /
            (1 - (q : k) ^ (m + 1)) := tsum_congr fun m ↦ by push_cast; ring
      _ = ∑' N : ℕ, ((∑ d ∈ N.divisors, (d : ℤ) : ℤ) : k) * (q : k) ^ N :=
          TateCurve.tsum_lambert (q : k) hq fun d ↦ (d : ℤ)
      _ = ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N :=
          tsum_congr fun N ↦ by push_cast; ring
  -- assemble
  have hcomb : (∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k) * (u : k) ^ d) * (q : k) ^ N) +
      (∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k) * ((u : k)⁻¹) ^ d) * (q : k) ^ N) -
      2 * ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N =
      ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : k) * (u : k) ^ d
        + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ N := by
    rw [← Summable.tsum_add hNA'.summable hNC'.summable,
      show (2 : k) * ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N =
        ∑' N : ℕ, 2 * ((∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N) from tsum_mul_left.symm,
      ← Summable.tsum_sub (hNA'.summable.add hNC'.summable) (hσ.mul_left 2)]
    refine tsum_congr fun N ↦ ?_
    rw [← add_mul, ← Finset.sum_add_distrib, ← mul_assoc, Finset.mul_sum, ← sub_mul,
      ← Finset.sum_sub_distrib]
  simp only [tateX]
  rw [hzsum.tsum_eq, hlam, ← hNA'.tsum_eq, ← hNC'.tsum_eq]
  linear_combination hcomb

/-- Silverman's `q`-expansion of the `y`-coordinate on the annulus `|q| < |u| ≤ 1`:
`Y(u, q) = u²/(1-u)³ + ∑_{N ≥ 1} (∑_{d ∣ N} ((d 2)uᵈ - (d+1 2)u⁻ᵈ + d))·qᴺ`, with
binomial-coefficient weights. The `n ≤ -1` half enters with a sign through the inversion
antisymmetry `sq_div_one_sub_cube_inv`. -/
theorem WeierstrassCurve.tateY_eq_annulus (q u : kˣ) (hq : valuation k (q : k) < 1)
    (h₁ : valuation k (q : k) < valuation k (u : k)) (h₂ : valuation k (u : k) ≤ 1) :
    tateY (u : k) (q : k) = (u : k) ^ 2 / (1 - (u : k)) ^ 3 +
      ∑' N : ℕ, (∑ d ∈ N.divisors, (((d.choose 2 : ℕ) : k) * (u : k) ^ d
        - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) * (q : k) ^ N := by
  have hq0 : (q : k) ≠ 0 := Units.ne_zero q
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr hu0
  have hρ : valuation k ((q : k) * (u : k)⁻¹) < 1 := by
    rw [map_mul, map_inv₀, ← div_eq_mul_inv]
    exact (div_lt_one₀ (TateCurve.valuation_unit_pos u)).mpr h₁
  have hposlt : ∀ n : ℕ, valuation k ((q : k) ^ (n + 1) * (u : k)) < 1 := by
    intro n
    rw [map_mul, map_pow]
    calc valuation k (q : k) ^ (n + 1) * valuation k (u : k)
        ≤ valuation k (q : k) ^ (n + 1) * 1 := mul_le_mul' le_rfl h₂
      _ = valuation k (q : k) ^ (n + 1) := mul_one _
      _ ≤ valuation k (q : k) ^ 1 := pow_le_pow_right_of_le_one' hq.le (by omega)
      _ = valuation k (q : k) := pow_one _
      _ < 1 := hq
  have hneglt : ∀ n : ℕ, valuation k ((q : k) ^ (n + 1) * (u : k)⁻¹) < 1 := by
    intro n
    refine lt_of_le_of_lt ?_ hρ
    rw [map_mul, map_mul, map_pow]
    refine mul_le_mul' ?_ le_rfl
    calc valuation k (q : k) ^ (n + 1) ≤ valuation k (q : k) ^ 1 :=
          pow_le_pow_right_of_le_one' hq.le (by omega)
      _ = valuation k (q : k) := pow_one _
  have hsumYpos : Summable fun p : ℕ+ × ℕ+ ↦
      (((p.1 : ℕ).choose 2 : ℕ) : k) * (u : k) ^ (p.1 : ℕ) *
        (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
    refine TateCurve.summable_of_valuation_le_pow hq (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ))
      (fun N ↦ TateCurve.finite_pnat_mul_lt N) fun p ↦ ?_
    rw [map_mul, map_mul, map_pow, map_pow]
    calc valuation k ((((p.1 : ℕ).choose 2 : ℕ)) : k) * valuation k (u : k) ^ (p.1 : ℕ) *
          valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ))
        ≤ 1 * 1 * valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
          mul_le_mul' (mul_le_mul' (valuation_natCast_le_one _)
            (pow_le_one' h₂ _)) le_rfl
      _ = valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by rw [one_mul, one_mul]
  have hsumYneg : Summable fun p : ℕ+ × ℕ+ ↦
      ((((p.1 : ℕ) + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ (p.1 : ℕ) *
        (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
    refine TateCurve.summable_of_valuation_le_pow hρ (fun p ↦ (p.1 : ℕ) * (p.2 : ℕ))
      (fun N ↦ TateCurve.finite_pnat_mul_lt N) fun p ↦ ?_
    simp only [map_mul, map_pow, map_inv₀]
    have h1u := TateCurve.one_le_valuation_inv (w := u) h₂
    calc valuation k (((((p.1 : ℕ) + 1).choose 2 : ℕ)) : k) *
          (valuation k (u : k))⁻¹ ^ (p.1 : ℕ) *
          valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ))
        ≤ 1 * (valuation k (u : k))⁻¹ ^ ((p.1 : ℕ) * (p.2 : ℕ)) *
            valuation k (q : k) ^ ((p.1 : ℕ) * (p.2 : ℕ)) :=
          mul_le_mul' (mul_le_mul' (valuation_natCast_le_one _)
            (pow_le_pow_right' h1u (Nat.le_mul_of_pos_right _ p.2.pos))) le_rfl
      _ = (valuation k (q : k) * (valuation k (u : k))⁻¹) ^ ((p.1 : ℕ) * (p.2 : ℕ)) := by
          rw [one_mul, mul_pow, mul_comm]
  obtain ⟨TA, hrowsA, hNA⟩ := TateCurve.hasSum_geom_rows (q : k) (u : k) (fun d ↦ d.choose 2)
    (fun x ↦ x ^ 2 / (1 - x) ^ 3) (fun x hx ↦ TateCurve.hasSum_geometric_sq_div_cube hx)
    hposlt hsumYpos
  obtain ⟨TC, hrowsC, hNC⟩ := TateCurve.hasSum_geom_rows (q : k) ((u : k)⁻¹)
    (fun d ↦ (d + 1).choose 2) (fun x ↦ x / (1 - x) ^ 3)
    (fun x hx ↦ TateCurve.hasSum_geometric_div_cube hx) hneglt hsumYneg
  have hNA' : HasSum (fun N : ℕ ↦
      (∑ d ∈ N.divisors, ((d.choose 2 : ℕ) : k) * (u : k) ^ d) * (q : k) ^ N) TA := hNA
  have hNC' : HasSum (fun N : ℕ ↦
      (∑ d ∈ N.divisors, (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d) * (q : k) ^ N) TC :=
    hNC
  have hcoe : ∀ n : ℕ, (q : k) ^ ((n : ℤ) + 1) = (q : k) ^ (n + 1) := by
    intro n
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hposrows : HasSum (fun n : ℕ ↦ ((q : k) ^ ((n : ℤ) + 1) * (u : k)) ^ 2 /
      (1 - (q : k) ^ ((n : ℤ) + 1) * (u : k)) ^ 3) TA := by
    have heq : (fun n : ℕ ↦ ((q : k) ^ ((n : ℤ) + 1) * (u : k)) ^ 2 /
        (1 - (q : k) ^ ((n : ℤ) + 1) * (u : k)) ^ 3) =
        fun n : ℕ ↦ ((q : k) ^ (n + 1) * (u : k)) ^ 2 /
          (1 - (q : k) ^ (n + 1) * (u : k)) ^ 3 := by
      funext n
      rw [hcoe n]
    rw [heq]
    exact hrowsA
  have hnegrows : HasSum (fun n : ℕ ↦ ((q : k) ^ (-((n : ℤ) + 1)) * (u : k)) ^ 2 /
      (1 - (q : k) ^ (-((n : ℤ) + 1)) * (u : k)) ^ 3) (-TC) := by
    have heq : (fun n : ℕ ↦ ((q : k) ^ (-((n : ℤ) + 1)) * (u : k)) ^ 2 /
        (1 - (q : k) ^ (-((n : ℤ) + 1)) * (u : k)) ^ 3) =
        fun n : ℕ ↦ -((q : k) ^ (n + 1) * (u : k)⁻¹ /
          (1 - (q : k) ^ (n + 1) * (u : k)⁻¹) ^ 3) := by
      funext n
      rw [zpow_neg, hcoe n,
        TateCurve.sq_div_one_sub_cube_inv (v := ((q : k) ^ (n + 1))⁻¹ * (u : k))
          (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hq0)) hu0),
        mul_inv, inv_inv]
    rw [heq]
    exact hrowsC.neg
  have hzsum : HasSum (fun n : ℤ ↦ ((q : k) ^ n * (u : k)) ^ 2 /
      (1 - (q : k) ^ n * (u : k)) ^ 3)
      (TA + (u : k) ^ 2 / (1 - (u : k)) ^ 3 + -TC) := by
    have h := HasSum.of_add_one_of_neg_add_one
      (f := fun n : ℤ ↦ ((q : k) ^ n * (u : k)) ^ 2 / (1 - (q : k) ^ n * (u : k)) ^ 3)
      hposrows hnegrows
    simpa using h
  have hσ : Summable fun N : ℕ ↦ (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N := by
    refine TateCurve.summable_of_valuation_le_pow hq (fun N ↦ N)
      (fun N ↦ Set.finite_Iio N) fun N ↦ ?_
    rw [map_mul, map_pow]
    calc valuation k (∑ d ∈ N.divisors, ((d : ℕ) : k)) * valuation k (q : k) ^ N
        ≤ 1 * valuation k (q : k) ^ N :=
          mul_le_mul_left ((valuation k).map_sum_le
            fun d _ ↦ valuation_natCast_le_one d) _
      _ = valuation k (q : k) ^ N := one_mul _
  have hlam : (∑' m : ℕ, ((m + 1 : ℕ) : k) * (q : k) ^ (m + 1) / (1 - (q : k) ^ (m + 1)))
      = ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N := by
    calc ∑' m : ℕ, ((m + 1 : ℕ) : k) * (q : k) ^ (m + 1) / (1 - (q : k) ^ (m + 1))
        = ∑' m : ℕ, (((fun d ↦ (d : ℤ)) (m + 1) : ℤ) : k) * (q : k) ^ (m + 1) /
            (1 - (q : k) ^ (m + 1)) := tsum_congr fun m ↦ by push_cast; ring
      _ = ∑' N : ℕ, ((∑ d ∈ N.divisors, (d : ℤ) : ℤ) : k) * (q : k) ^ N :=
          TateCurve.tsum_lambert (q : k) hq fun d ↦ (d : ℤ)
      _ = ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N :=
          tsum_congr fun N ↦ by push_cast; ring
  have hcomb : (∑' N : ℕ,
      (∑ d ∈ N.divisors, ((d.choose 2 : ℕ) : k) * (u : k) ^ d) * (q : k) ^ N) -
      (∑' N : ℕ,
        (∑ d ∈ N.divisors, (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d) * (q : k) ^ N) +
      ∑' N : ℕ, (∑ d ∈ N.divisors, ((d : ℕ) : k)) * (q : k) ^ N =
      ∑' N : ℕ, (∑ d ∈ N.divisors, (((d.choose 2 : ℕ) : k) * (u : k) ^ d
        - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) * (q : k) ^ N := by
    rw [← Summable.tsum_sub hNA'.summable hNC'.summable,
      ← Summable.tsum_add (hNA'.summable.sub hNC'.summable) hσ]
    refine tsum_congr fun N ↦ ?_
    rw [← sub_mul, ← Finset.sum_sub_distrib, ← add_mul, ← Finset.sum_add_distrib]
  simp only [tateY]
  rw [hzsum.tsum_eq, hlam, ← hNA'.tsum_eq, ← hNC'.tsum_eq]
  linear_combination hcomb

/-! ### Evaluation of `k`-coefficient power series on the annulus

The annulus `q`-expansions above present `tateX` and `tateY` as values of power series in
`k⟦q⟧` whose terms at `q` are `O(ρⁿ)` in valuation, for `ρ = |q|/|u| < 1`
(`TateCurve.EvalBounded`). On this class, evaluation (`TateCurve.evalK`) is a ring
homomorphism — the nonarchimedean Mertens theorem again, now with the constant tracked
through the bounds. Applying it to the descended formal identity
`TateCurve.weierstrass_equation_field` yields the Weierstrass equation for the values,
which is the annulus case of Silverman V.1.1(a). -/

/-- Powers of any `ρ < 1` in the value group eventually drop below any nonzero `γ`: the
generalisation of `exists_pow_valuation_lt` from `|q|` to arbitrary `ρ`, by the same
rank-one embedding argument. -/
theorem TateCurve.exists_pow_lt {ρ : ValueGroupWithZero k} (hρ : ρ < 1)
    (γ : (ValueGroupWithZero k)ˣ) : ∃ N : ℕ, ρ ^ N < γ := by
  rcases eq_or_ne ρ 0 with rfl | h0
  · exact ⟨1, by rw [pow_one]; exact zero_lt_iff.mpr γ.ne_zero⟩
  · obtain ⟨s⟩ := ValuativeRel.IsRankLeOne.nonempty (R := k)
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
      (show 0 < s.emb γ from by simpa using s.strictMono (zero_lt_iff.mpr γ.ne_zero))
      (show s.emb ρ < 1 from by simpa using s.strictMono hρ)
    exact ⟨N, s.strictMono.lt_iff_lt.mp (by rwa [map_pow])⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- Clearing the constant: `ρᴺ < C⁻¹γ` implies `CρᴺN < γ` in the value group. -/
theorem TateCurve.mul_pow_lt {C ρ γ : ValueGroupWithZero k} (hC : C ≠ 0) {N : ℕ}
    (hN : ρ ^ N < C⁻¹ * γ) : C * ρ ^ N < γ := by
  have hle : C * ρ ^ N ≤ γ := by
    calc C * ρ ^ N ≤ C * (C⁻¹ * γ) := mul_le_mul' le_rfl hN.le
      _ = γ := by rw [← mul_assoc, mul_inv_cancel₀ hC, one_mul]
  refine lt_of_le_of_ne hle fun heq ↦ hN.ne ?_
  exact mul_left_cancel₀ hC (by rw [heq, ← mul_assoc, mul_inv_cancel₀ hC, one_mul])

/-- The nonarchimedean summability criterion with a constant: a series whose terms have
valuation at most `C·ρⁿ` with `ρ < 1` converges. Generalises
`summable_of_valuation_le_pow` to carry the constant `C` needed for series with large
leading coefficients (such as `u/(1-u)²` for `u` close to `1`). -/
theorem TateCurve.summable_of_valuation_le_const_mul_pow {C ρ : ValueGroupWithZero k}
    (hC : C ≠ 0) (hρ : ρ < 1) (f : ℕ → k)
    (hf : ∀ n, valuation k (f n) ≤ C * ρ ^ n) : Summable f := by
  letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
  haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
  haveI : NonarchimedeanRing k := by
    convert! ValuativeRel.nonarchimedeanRing k
    exact Valuation.toTopologicalSpace_eq _
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop, (IsValuativeTopology.hasBasis_nhds (0 : k)).tendsto_right_iff]
  intro γ _
  obtain ⟨N, hN⟩ := exists_pow_lt hρ (Units.mk0 (C⁻¹ * (γ : ValueGroupWithZero k))
    (mul_ne_zero (inv_ne_zero hC) γ.ne_zero))
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  simp only [sub_zero]
  calc valuation k (f n) ≤ C * ρ ^ n := hf n
    _ ≤ C * ρ ^ N := mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' hρ.le hn)
    _ < γ := mul_pow_lt hC hN

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The class of power series `F ∈ k⟦X⟧` whose terms at `q` are `O(ρⁿ)` in valuation:
`|coeff n F·qⁿ| ≤ C·ρⁿ` for some nonzero constant `C`. For `ρ < 1` such series are
evaluable at `q` (`EvalBounded.summable`), and the class is a subring on which evaluation
is multiplicative (`evalK_mul`) — the constant is what accommodates coefficients like
`u/(1-u)²` (large for `u` near `1`) and the growing denominators `u⁻ᵈ` of the annulus
expansions (bounded by `ρ = |q|/|u|`-powers rather than `|q|`-powers). -/
def TateCurve.EvalBounded (q : k) (ρ : ValueGroupWithZero k) (F : k⟦X⟧) : Prop :=
  ∃ C : ValueGroupWithZero k, C ≠ 0 ∧
    ∀ n : ℕ, valuation k (PowerSeries.coeff n F * q ^ n) ≤ C * ρ ^ n

theorem TateCurve.EvalBounded.summable {q : k} {ρ : ValueGroupWithZero k} {F : k⟦X⟧}
    (hF : EvalBounded q ρ F) (hρ : ρ < 1) :
    Summable fun n : ℕ ↦ PowerSeries.coeff n F * q ^ n := by
  obtain ⟨C, hC, hb⟩ := hF
  exact summable_of_valuation_le_const_mul_pow hC hρ _ hb

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem TateCurve.EvalBounded.add {q : k} {ρ : ValueGroupWithZero k} {F G : k⟦X⟧}
    (hF : EvalBounded q ρ F) (hG : EvalBounded q ρ G) : EvalBounded q ρ (F + G) := by
  obtain ⟨C₁, hC₁, h₁⟩ := hF
  obtain ⟨C₂, hC₂, h₂⟩ := hG
  refine ⟨max C₁ C₂, (lt_max_of_lt_left (zero_lt_iff.mpr hC₁)).ne', fun n ↦ ?_⟩
  rw [map_add, add_mul]
  refine le_trans ((valuation k).map_add _ _) (max_le ?_ ?_)
  · exact (h₁ n).trans (mul_le_mul' (le_max_left _ _) le_rfl)
  · exact (h₂ n).trans (mul_le_mul' (le_max_right _ _) le_rfl)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem TateCurve.EvalBounded.mul {q : k} {ρ : ValueGroupWithZero k} {F G : k⟦X⟧}
    (hF : EvalBounded q ρ F) (hG : EvalBounded q ρ G) : EvalBounded q ρ (F * G) := by
  obtain ⟨C₁, hC₁, h₁⟩ := hF
  obtain ⟨C₂, hC₂, h₂⟩ := hG
  refine ⟨C₁ * C₂, mul_ne_zero hC₁ hC₂, fun n ↦ ?_⟩
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine (valuation k).map_sum_le fun kl hkl ↦ ?_
  rw [Finset.mem_antidiagonal] at hkl
  calc valuation k (PowerSeries.coeff kl.1 F * PowerSeries.coeff kl.2 G * q ^ n)
      = valuation k (PowerSeries.coeff kl.1 F * q ^ kl.1) *
        valuation k (PowerSeries.coeff kl.2 G * q ^ kl.2) := by
        rw [← map_mul]
        congr 1
        rw [← hkl, pow_add]
        ring
    _ ≤ C₁ * ρ ^ kl.1 * (C₂ * ρ ^ kl.2) := mul_le_mul' (h₁ _) (h₂ _)
    _ = C₁ * C₂ * ρ ^ n := by rw [mul_mul_mul_comm, ← pow_add, hkl]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem TateCurve.EvalBounded.pow {q : k} {ρ : ValueGroupWithZero k} {F : k⟦X⟧}
    (hF : EvalBounded q ρ F) (m : ℕ) : EvalBounded q ρ (F ^ m) := by
  induction m with
  | zero =>
      refine ⟨1, one_ne_zero, fun n ↦ ?_⟩
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      · simp [PowerSeries.coeff_one, hn]
  | succ m ih =>
      rw [pow_succ]
      exact ih.mul hF

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- Constant power series are evaluation-bounded (with constant `max 1 |a|`). -/
theorem TateCurve.evalBounded_C (q : k) (ρ : ValueGroupWithZero k) (a : k) :
    EvalBounded q ρ (PowerSeries.C a) := by
  refine ⟨max 1 (valuation k a), (lt_max_of_lt_left zero_lt_one).ne', fun n ↦ ?_⟩
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero, mul_one, pow_zero, mul_one, PowerSeries.coeff_zero_C]
    exact le_max_right _ _
  · rw [PowerSeries.coeff_C, if_neg hn, zero_mul, map_zero]
    exact zero_le

/-- Evaluation of a `k`-coefficient power series at `q`: `F(q) = ∑ₙ (coeff n F)·qⁿ`
(junk unless the series converges, e.g. for `EvalBounded` series at `ρ < 1`). Extends
`TateCurve.evalInt` from integral to `k`-coefficient series. -/
noncomputable def TateCurve.evalK (q : k) (F : k⟦X⟧) : k :=
  ∑' n : ℕ, PowerSeries.coeff n F * q ^ n

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- `evalK` at an integral series is `evalInt`. -/
theorem TateCurve.evalK_intSeries (q : k) (F : ℤ⟦X⟧) :
    evalK q (F.map (Int.castRingHom k)) = evalInt q F :=
  tsum_congr fun n ↦ by rw [PowerSeries.coeff_map, eq_intCast]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- Integral series are evaluation-bounded (with constant `1`) for any `ρ ≥ |q|`. -/
theorem TateCurve.evalBounded_intSeries (q : k) {ρ : ValueGroupWithZero k}
    (hqρ : valuation k q ≤ ρ) (F : ℤ⟦X⟧) :
    EvalBounded q ρ (F.map (Int.castRingHom k)) := by
  refine ⟨1, one_ne_zero, fun n ↦ ?_⟩
  rw [one_mul, PowerSeries.coeff_map, eq_intCast, map_mul, map_pow]
  calc valuation k ((PowerSeries.coeff n F : ℤ) : k) * valuation k q ^ n
      ≤ 1 * valuation k q ^ n := mul_le_mul_left (valuation_intCast_le_one _) _
    _ = valuation k q ^ n := one_mul _
    _ ≤ ρ ^ n := pow_le_pow_left' hqρ n

theorem TateCurve.evalK_add {q : k} {ρ : ValueGroupWithZero k} (hρ : ρ < 1) {F G : k⟦X⟧}
    (hF : EvalBounded q ρ F) (hG : EvalBounded q ρ G) :
    evalK q (F + G) = evalK q F + evalK q G := by
  simp only [evalK, map_add, add_mul]
  exact Summable.tsum_add (hF.summable hρ) (hG.summable hρ)

/-- Evaluation of `k`-coefficient power series is multiplicative on the bounded class:
the nonarchimedean Mertens theorem, with the constant carried through the double-series
summability bound. Extends `TateCurve.evalInt_mul`. -/
theorem TateCurve.evalK_mul {q : k} {ρ : ValueGroupWithZero k} (hρ : ρ < 1) {F G : k⟦X⟧}
    (hF : EvalBounded q ρ F) (hG : EvalBounded q ρ G) :
    evalK q (F * G) = evalK q F * evalK q G := by
  have hf := hF.summable hρ
  have hg := hG.summable hρ
  obtain ⟨C₁, hC₁, h₁⟩ := hF
  obtain ⟨C₂, hC₂, h₂⟩ := hG
  have hfg : Summable fun x : ℕ × ℕ ↦
      (PowerSeries.coeff x.1 F * q ^ x.1) * (PowerSeries.coeff x.2 G * q ^ x.2) := by
    letI : UniformSpace k := IsTopologicalAddGroup.rightUniformSpace k
    haveI : IsUniformAddGroup k := isUniformAddGroup_of_addCommGroup
    haveI : NonarchimedeanRing k := by
      convert! ValuativeRel.nonarchimedeanRing k
      exact Valuation.toTopologicalSpace_eq _
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [(IsValuativeTopology.hasBasis_nhds (0 : k)).tendsto_right_iff]
    intro γ _
    obtain ⟨N, hN⟩ := exists_pow_lt hρ (Units.mk0
      ((C₁ * C₂)⁻¹ * (γ : ValueGroupWithZero k))
      (mul_ne_zero (inv_ne_zero (mul_ne_zero hC₁ hC₂)) γ.ne_zero))
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset ((Set.finite_Iio N).prod (Set.finite_Iio N)) fun x hx ↦ ?_
    simp only [Set.mem_setOf_eq, sub_zero] at hx
    have hbound : valuation k ((PowerSeries.coeff x.1 F * q ^ x.1) *
        (PowerSeries.coeff x.2 G * q ^ x.2)) ≤ C₁ * C₂ * ρ ^ (x.1 + x.2) :=
      calc valuation k ((PowerSeries.coeff x.1 F * q ^ x.1) *
            (PowerSeries.coeff x.2 G * q ^ x.2))
          = valuation k (PowerSeries.coeff x.1 F * q ^ x.1) *
            valuation k (PowerSeries.coeff x.2 G * q ^ x.2) := map_mul _ _ _
        _ ≤ C₁ * ρ ^ x.1 * (C₂ * ρ ^ x.2) := mul_le_mul' (h₁ _) (h₂ _)
        _ = C₁ * C₂ * ρ ^ (x.1 + x.2) := by rw [mul_mul_mul_comm, ← pow_add]
    have hlt : x.1 + x.2 < N := lt_of_not_ge fun hge ↦
      hx (lt_of_le_of_lt (hbound.trans (mul_le_mul' le_rfl
        (pow_le_pow_right_of_le_one' hρ.le hge))) (mul_pow_lt (mul_ne_zero hC₁ hC₂) hN))
    exact Set.mem_prod.mpr ⟨Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_right _ _) hlt),
      Set.mem_Iio.mpr (lt_of_le_of_lt (Nat.le_add_left _ _) hlt)⟩
  simp only [evalK]
  rw [hf.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg hfg]
  refine tsum_congr fun n ↦ ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun kl hkl ↦ ?_
  rw [Finset.mem_antidiagonal] at hkl
  rw [← hkl, pow_add]
  ring

theorem TateCurve.evalK_pow {q : k} {ρ : ValueGroupWithZero k} (hρ : ρ < 1) {F : k⟦X⟧}
    (hF : EvalBounded q ρ F) (m : ℕ) : evalK q (F ^ m) = evalK q F ^ m := by
  induction m with
  | zero =>
      rw [pow_zero, pow_zero]
      have h : (fun n : ℕ ↦ PowerSeries.coeff n (1 : k⟦X⟧) * q ^ n) =
          fun n ↦ if n = 0 then 1 else 0 := by
        funext n
        rcases eq_or_ne n 0 with rfl | hn
        · simp
        · simp [PowerSeries.coeff_one, hn]
      rw [show evalK q 1 = ∑' n : ℕ, PowerSeries.coeff n (1 : k⟦X⟧) * q ^ n from rfl, h,
        tsum_ite_eq]
  | succ m ih => rw [pow_succ, pow_succ, evalK_mul hρ (hF.pow m) hF, ih]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem TateCurve.EvalBounded.neg {q : k} {ρ : ValueGroupWithZero k} {F : k⟦X⟧}
    (hF : EvalBounded q ρ F) : EvalBounded q ρ (-F) := by
  obtain ⟨C, hC, hb⟩ := hF
  exact ⟨C, hC, fun n ↦ by rw [map_neg, neg_mul, (valuation k).map_neg]; exact hb n⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem TateCurve.EvalBounded.sub {q : k} {ρ : ValueGroupWithZero k} {F G : k⟦X⟧}
    (hF : EvalBounded q ρ F) (hG : EvalBounded q ρ G) : EvalBounded q ρ (F - G) := by
  rw [sub_eq_add_neg]
  exact hF.add hG.neg

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- Evaluation bounds are monotone in the radius. -/
theorem TateCurve.EvalBounded.mono {q : k} {ρ ρ' : ValueGroupWithZero k} (h : ρ ≤ ρ')
    {F : k⟦X⟧} (hF : EvalBounded q ρ F) : EvalBounded q ρ' F := by
  obtain ⟨C, hC, hb⟩ := hF
  exact ⟨C, hC, fun n ↦ (hb n).trans (mul_le_mul' le_rfl (pow_le_pow_left' h n))⟩

theorem TateCurve.evalK_sub {q : k} {ρ : ValueGroupWithZero k} (hρ : ρ < 1) {F G : k⟦X⟧}
    (hF : EvalBounded q ρ F) (hG : EvalBounded q ρ G) :
    evalK q (F - G) = evalK q F - evalK q G := by
  simp only [evalK, map_sub, sub_mul]
  exact Summable.tsum_sub (hF.summable hρ) (hG.summable hρ)

/-- Evaluation commutes with negation. -/
theorem TateCurve.evalK_neg (q : k) (F : k⟦X⟧) : evalK q (-F) = -evalK q F := by
  simp only [evalK, map_neg, neg_mul]
  exact tsum_neg

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- A power series whose `n`-th coefficient has valuation at most `M ^ n` is
evaluation-bounded at `q` with radius `|q| * M` and constant `1`. -/
theorem TateCurve.evalBounded_of_coeff_le_pow {q : k} {M : ValueGroupWithZero k} {F : k⟦X⟧}
    (h : ∀ n, valuation k (PowerSeries.coeff n F) ≤ M ^ n) :
    EvalBounded q (valuation k q * M) F :=
  ⟨1, one_ne_zero, fun n ↦ by
    rw [one_mul, map_mul, map_pow, mul_pow, mul_comm (valuation k q ^ n)]
    exact mul_le_mul' (h n) le_rfl⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- A divisor-sum series `∑_{d ∣ n} c n d` whose summands satisfy `|c n d| ≤ M ^ d` (for
`1 ≤ M`) is evaluation-bounded at `q` with radius `|q| * M`: the ultrametric inequality
turns the termwise bound into `|∑_{d ∣ n} c n d| ≤ M ^ n`, since every `d ∣ n` has `d ≤ n`. -/
theorem TateCurve.evalBounded_divisorSum {q : k} {M : ValueGroupWithZero k} (h1M : 1 ≤ M)
    (c : ℕ → ℕ → k) (hc : ∀ n, ∀ d ∈ n.divisors, valuation k (c n d) ≤ M ^ d) :
    EvalBounded q (valuation k q * M) (PowerSeries.mk fun n ↦ ∑ d ∈ n.divisors, c n d) := by
  refine evalBounded_of_coeff_le_pow fun n ↦ ?_
  rw [PowerSeries.coeff_mk]
  exact (valuation k).map_sum_le fun d hd ↦
    (hc n d hd).trans (pow_le_pow_right' h1M (Nat.divisor_le hd))

/-- The three properties of a bound `M` shared by the fundamental annulus (`M = |u|⁻¹`,
see `annulusBound_narrow`) and the wide annulus (`M = max |u|⁻¹ |u|`, see
`annulusBound_wide`). Both `XField` and `YField` are evaluation-bounded with radius
`|q| * M` for any such `M`. -/
structure TateCurve.AnnulusBound (u : kˣ) (M : ValueGroupWithZero k) : Prop where
  one_le : 1 ≤ M
  val_le : valuation k (u : k) ≤ M
  inv_le : (valuation k (u : k))⁻¹ ≤ M

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- On the fundamental annulus `|u| ≤ 1`, take `M = |u|⁻¹`. -/
theorem TateCurve.annulusBound_narrow (u : kˣ) (h₂ : valuation k (u : k) ≤ 1) :
    AnnulusBound u (valuation k (u : k))⁻¹ :=
  ⟨one_le_valuation_inv h₂, h₂.trans (one_le_valuation_inv h₂), le_rfl⟩

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- On the wide annulus, take `M = max |u|⁻¹ |u|`; no constraint on `|u|` is needed. -/
theorem TateCurve.annulusBound_wide (u : kˣ) :
    AnnulusBound u (max (valuation k (u : k))⁻¹ (valuation k (u : k))) := by
  refine ⟨?_, le_max_right _ _, le_max_left _ _⟩
  rcases le_total (valuation k (u : k)) 1 with h | h
  · exact le_max_of_le_left (one_le_valuation_inv h)
  · exact le_max_of_le_right h

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The divisor-sum tail of `XField u` is evaluation-bounded with radius `|q| * M` for any
annulus bound `M`: each summand `d·u^d`, `d·u⁻ᵈ`, `2d` has valuation at most `M ^ d`. -/
theorem TateCurve.evalBounded_XField_tail_of_annulusBound (q u : kˣ)
    {M : ValueGroupWithZero k} (hM : AnnulusBound u M) :
    EvalBounded (q : k) (valuation k (q : k) * M)
      (PowerSeries.mk fun n ↦ ∑ d ∈ n.divisors,
        ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) := by
  refine evalBounded_divisorSum hM.one_le _ fun n d _ ↦ ?_
  have h1d : (1 : ValueGroupWithZero k) ≤ M ^ d := one_le_pow₀ hM.one_le
  refine le_trans ((valuation k).map_sub _ _)
    (max_le (le_trans ((valuation k).map_add _ _) (max_le ?_ ?_)) ?_)
  · rw [map_mul, map_pow]
    calc valuation k ((d : ℕ) : k) * valuation k (u : k) ^ d
        ≤ 1 * M ^ d := mul_le_mul' (valuation_natCast_le_one d) (pow_le_pow_left' hM.val_le d)
      _ = M ^ d := one_mul _
  · rw [map_mul, map_pow, map_inv₀]
    calc valuation k ((d : ℕ) : k) * (valuation k (u : k))⁻¹ ^ d
        ≤ 1 * M ^ d := mul_le_mul' (valuation_natCast_le_one d) (pow_le_pow_left' hM.inv_le d)
      _ = M ^ d := one_mul _
  · rw [show ((2 : k) * (d : k)) = ((2 * d : ℕ) : k) by push_cast; ring]
    exact le_trans (valuation_natCast_le_one _) h1d

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The divisor-sum tail of `YField u`; as for `evalBounded_XField_tail_of_annulusBound`. -/
theorem TateCurve.evalBounded_YField_tail_of_annulusBound (q u : kˣ)
    {M : ValueGroupWithZero k} (hM : AnnulusBound u M) :
    EvalBounded (q : k) (valuation k (q : k) * M)
      (PowerSeries.mk fun n ↦ ∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : k) * (u : k) ^ d
        - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) := by
  refine evalBounded_divisorSum hM.one_le _ fun n d _ ↦ ?_
  have h1d : (1 : ValueGroupWithZero k) ≤ M ^ d := one_le_pow₀ hM.one_le
  refine le_trans ((valuation k).map_add _ _)
    (max_le (le_trans ((valuation k).map_sub _ _) (max_le ?_ ?_)) ?_)
  · rw [map_mul, map_pow]
    calc valuation k ((d.choose 2 : ℕ) : k) * valuation k (u : k) ^ d
        ≤ 1 * M ^ d := mul_le_mul' (valuation_natCast_le_one _) (pow_le_pow_left' hM.val_le d)
      _ = M ^ d := one_mul _
  · rw [map_mul, map_pow, map_inv₀]
    calc valuation k (((d + 1).choose 2 : ℕ) : k) * (valuation k (u : k))⁻¹ ^ d
        ≤ 1 * M ^ d := mul_le_mul' (valuation_natCast_le_one _) (pow_le_pow_left' hM.inv_le d)
      _ = M ^ d := one_mul _
  · exact le_trans (valuation_natCast_le_one d) h1d

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The divisor-sum tail of `XField u` is evaluation-bounded by `(|q|/|u|)ⁿ`-powers: the
`u⁻ᵈ`-terms grow like `|u|⁻ⁿ`, which the annulus bound absorbs. -/
theorem TateCurve.evalBounded_XField_tail (q u : kˣ) (h₂ : valuation k (u : k) ≤ 1) :
    EvalBounded (q : k) (valuation k (q : k) * (valuation k (u : k))⁻¹)
      (PowerSeries.mk fun n ↦ ∑ d ∈ n.divisors,
        ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) :=
  evalBounded_XField_tail_of_annulusBound q u (annulusBound_narrow u h₂)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem TateCurve.evalBounded_XField (q u : kˣ) (h₂ : valuation k (u : k) ≤ 1) :
    EvalBounded (q : k) (valuation k (q : k) * (valuation k (u : k))⁻¹)
      (XField (u : k)) :=
  (evalBounded_C _ _ _).add (evalBounded_XField_tail q u h₂)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The divisor-sum tail of `YField u`; as for `evalBounded_XField_tail`. -/
theorem TateCurve.evalBounded_YField_tail (q u : kˣ) (h₂ : valuation k (u : k) ≤ 1) :
    EvalBounded (q : k) (valuation k (q : k) * (valuation k (u : k))⁻¹)
      (PowerSeries.mk fun n ↦ ∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : k) * (u : k) ^ d
        - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) :=
  evalBounded_YField_tail_of_annulusBound q u (annulusBound_narrow u h₂)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem TateCurve.evalBounded_YField (q u : kˣ) (h₂ : valuation k (u : k) ≤ 1) :
    EvalBounded (q : k) (valuation k (q : k) * (valuation k (u : k))⁻¹)
      (YField (u : k)) :=
  (evalBounded_C _ _ _).add (evalBounded_YField_tail q u h₂)

/-- On the annulus, `tateX` is the value at `q` of the formal series `XField u`:
`tateX_eq_annulus` in evaluation form. -/
theorem WeierstrassCurve.tateX_eq_evalK (q u : kˣ) (hq : valuation k (q : k) < 1)
    (h₁ : valuation k (q : k) < valuation k (u : k)) (h₂ : valuation k (u : k) ≤ 1) :
    tateX (u : k) (q : k) = TateCurve.evalK (q : k) (TateCurve.XField (u : k)) := by
  have hvu : valuation k (u : k) ≠ 0 := TateCurve.valuation_unit_ne_zero u
  have hρ1 : valuation k (q : k) * (valuation k (u : k))⁻¹ < 1 := by
    rw [← div_eq_mul_inv]
    exact (div_lt_one₀ (TateCurve.valuation_unit_pos u)).mpr h₁
  have htail : Summable fun n : ℕ ↦ (∑ d ∈ n.divisors,
      ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ n :=
    ((TateCurve.evalBounded_XField_tail q u h₂).summable hρ1).congr fun n ↦ by
      rw [PowerSeries.coeff_mk]
  have hterm : ∀ n : ℕ,
      PowerSeries.coeff n (TateCurve.XField (u : k)) * (q : k) ^ n =
      (if n = 0 then (u : k) / (1 - (u : k)) ^ 2 else 0) + (∑ d ∈ n.divisors,
        ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ n := by
    intro n
    rw [TateCurve.coeff_XField, add_mul]
    congr 1
    rcases eq_or_ne n 0 with rfl | hn
    · rw [if_pos rfl, pow_zero, mul_one]
    · rw [if_neg hn, zero_mul]
  rw [tateX_eq_annulus q u hq h₁ h₂,
    show TateCurve.evalK (q : k) (TateCurve.XField (u : k)) = ∑' n : ℕ,
      ((if n = 0 then (u : k) / (1 - (u : k)) ^ 2 else 0) + (∑ d ∈ n.divisors,
        ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) * (q : k) ^ n)
      from tsum_congr hterm,
    Summable.tsum_add ((hasSum_ite_eq 0 _).summable) htail, tsum_ite_eq]

/-- On the annulus, `tateY` is the value at `q` of the formal series `YField u`:
`tateY_eq_annulus` in evaluation form. -/
theorem WeierstrassCurve.tateY_eq_evalK (q u : kˣ) (hq : valuation k (q : k) < 1)
    (h₁ : valuation k (q : k) < valuation k (u : k)) (h₂ : valuation k (u : k) ≤ 1) :
    tateY (u : k) (q : k) = TateCurve.evalK (q : k) (TateCurve.YField (u : k)) := by
  have hvu : valuation k (u : k) ≠ 0 := TateCurve.valuation_unit_ne_zero u
  have hρ1 : valuation k (q : k) * (valuation k (u : k))⁻¹ < 1 := by
    rw [← div_eq_mul_inv]
    exact (div_lt_one₀ (TateCurve.valuation_unit_pos u)).mpr h₁
  have htail : Summable fun n : ℕ ↦ (∑ d ∈ n.divisors,
      (((d.choose 2 : ℕ) : k) * (u : k) ^ d
        - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) * (q : k) ^ n :=
    ((TateCurve.evalBounded_YField_tail q u h₂).summable hρ1).congr fun n ↦ by
      rw [PowerSeries.coeff_mk]
  have hterm : ∀ n : ℕ,
      PowerSeries.coeff n (TateCurve.YField (u : k)) * (q : k) ^ n =
      (if n = 0 then (u : k) ^ 2 / (1 - (u : k)) ^ 3 else 0) + (∑ d ∈ n.divisors,
        (((d.choose 2 : ℕ) : k) * (u : k) ^ d
          - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) * (q : k) ^ n := by
    intro n
    rw [TateCurve.coeff_YField, add_mul]
    congr 1
    rcases eq_or_ne n 0 with rfl | hn
    · rw [if_pos rfl, pow_zero, mul_one]
    · rw [if_neg hn, zero_mul]
  rw [tateY_eq_annulus q u hq h₁ h₂,
    show TateCurve.evalK (q : k) (TateCurve.YField (u : k)) = ∑' n : ℕ,
      ((if n = 0 then (u : k) ^ 2 / (1 - (u : k)) ^ 3 else 0) + (∑ d ∈ n.divisors,
        (((d.choose 2 : ℕ) : k) * (u : k) ^ d
          - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) * (q : k) ^ n)
      from tsum_congr hterm,
    Summable.tsum_add ((hasSum_ite_eq 0 _).summable) htail, tsum_ite_eq]

/-- `tateA₄` is the value at `q` of the formal series `a₄Field k`. -/
theorem WeierstrassCurve.tateA₄_eq_evalK (q : k) (hq : valuation k q < 1) :
    tateA₄ q = TateCurve.evalK q (TateCurve.a₄Field k) :=
  (tateA₄_eq_evalInt q hq).trans (TateCurve.evalK_intSeries q TateCurve.a₄Formal).symm

/-- `tateA₆` is the value at `q` of the formal series `a₆Field k`. -/
theorem WeierstrassCurve.tateA₆_eq_evalK (q : k) (hq : valuation k q < 1) :
    tateA₆ q = TateCurve.evalK q (TateCurve.a₆Field k) :=
  (tateA₆_eq_evalInt q hq).trans (TateCurve.evalK_intSeries q TateCurve.a₆Formal).symm

/-- The annulus case of Silverman, ATAEC V.1.1(a): for `|q| < |u| ≤ 1` and `u ≠ 1`, the
pair `(X(u, q), Y(u, q))` satisfies the Weierstrass equation of the Tate curve. (In the
annulus the only power of `q` is `1` itself, so `u ≠ 1` is the full nondegeneracy
condition.)

The proof composes the three layers built above:

* the annulus `q`-expansions `tateX_eq_annulus`, `tateY_eq_annulus` present the
  coordinates as values `evalK q (XField u)`, `evalK q (YField u)` of formal series
  whose coefficients are Silverman's divisor sums (`tateX_eq_evalK`, `tateY_eq_evalK`),
  and likewise `tateA₄`, `tateA₆` for the Weierstrass coefficients;
* all four series are evaluation-bounded by `(|q|/|u|)ⁿ`-powers (`EvalBounded`), and on
  that class evaluation is a ring homomorphism (`evalK_add`, `evalK_mul`, `evalK_pow` —
  the nonarchimedean Mertens theorem);
* the formal Weierstrass identity, proved analytically over `ℚ(u)` and descended
  through `ℤ[u, u⁻¹, (1-u)⁻¹]` to every field (`weierstrass_equation_field`, using
  `u ≠ 0, 1`), therefore evaluates to the equation between the values. -/
theorem WeierstrassCurve.tateCurve_equation_of_annulus (q : kˣ)
    (hq : valuation k (q : k) < 1) (u : kˣ) (hu1 : u ≠ 1)
    (h₁ : valuation k (q : k) < valuation k (u : k)) (h₂ : valuation k (u : k) ≤ 1) :
    ((tateCurve (q : k))⁄k).Equation (tateX (u : k) (q : k)) (tateY (u : k) (q : k)) := by
  have hu0 : (u : k) ≠ 0 := Units.ne_zero u
  have hu1' : (u : k) ≠ 1 := fun h ↦ hu1 (Units.ext (by rw [Units.val_one]; exact h))
  have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr hu0
  have hρ1 : valuation k (q : k) * (valuation k (u : k))⁻¹ < 1 := by
    rw [← div_eq_mul_inv]
    exact (div_lt_one₀ (TateCurve.valuation_unit_pos u)).mpr h₁
  have hqρ : valuation k (q : k) ≤ valuation k (q : k) * (valuation k (u : k))⁻¹ :=
    calc valuation k (q : k) = valuation k (q : k) * 1 := (mul_one _).symm
      _ ≤ valuation k (q : k) * (valuation k (u : k))⁻¹ :=
        mul_le_mul' le_rfl (TateCurve.one_le_valuation_inv (w := u) h₂)
  -- the four series are evaluation-bounded on the annulus
  have hX := TateCurve.evalBounded_XField q u h₂
  have hY := TateCurve.evalBounded_YField q u h₂
  have hA₄ : TateCurve.EvalBounded (q : k) (valuation k (q : k) * (valuation k (u : k))⁻¹)
      (TateCurve.a₄Field k) := TateCurve.evalBounded_intSeries (q : k) hqρ TateCurve.a₄Formal
  have hA₆ : TateCurve.EvalBounded (q : k) (valuation k (q : k) * (valuation k (u : k))⁻¹)
      (TateCurve.a₆Field k) := TateCurve.evalBounded_intSeries (q : k) hqρ TateCurve.a₆Formal
  -- reduce to the coefficient identity `Y² + XY = X³ + a₄X + a₆`
  rw [show (tateCurve (q : k))⁄k = tateCurve (q : k) by
    simp only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id],
    WeierstrassCurve.Affine.equation_iff]
  rw [show (tateCurve (q : k)).a₁ = 1 from rfl, show (tateCurve (q : k)).a₂ = 0 from rfl,
    show (tateCurve (q : k)).a₃ = 0 from rfl,
    show (tateCurve (q : k)).a₄ = tateA₄ (q : k) from rfl,
    show (tateCurve (q : k)).a₆ = tateA₆ (q : k) from rfl,
    one_mul, zero_mul, add_zero, zero_mul, add_zero]
  -- express everything as values of the formal series and use the descended identity
  rw [tateX_eq_evalK q u hq h₁ h₂, tateY_eq_evalK q u hq h₁ h₂,
    tateA₄_eq_evalK (q : k) hq, tateA₆_eq_evalK (q : k) hq,
    ← TateCurve.evalK_pow hρ1 hY 2, ← TateCurve.evalK_mul hρ1 hX hY,
    ← TateCurve.evalK_add hρ1 (hY.pow 2) (hX.mul hY),
    ← TateCurve.evalK_pow hρ1 hX 3, ← TateCurve.evalK_mul hρ1 hA₄ hX,
    ← TateCurve.evalK_add hρ1 (hX.pow 3) (hA₄.mul hX),
    ← TateCurve.evalK_add hρ1 ((hX.pow 3).add (hA₄.mul hX)) hA₆]
  exact congrArg (TateCurve.evalK (q : k))
    (TateCurve.weierstrass_equation_field hu0 hu1')

/-- Silverman, ATAEC V.1.1(a), over `k`: for `u` not a power of `q`, the pair
`(X(u, q), Y(u, q))` satisfies the Weierstrass equation of the Tate curve `E_q`. The
formal kernel is `TateCurve.weierstrass_equation`, the identity
`Y² + XY = X³ + a₄X + a₆` in `(RatFunc ℚ)⟦q⟧` proved in
`FLT.KnownIn1980s.EllipticCurves.TateCurveConstruction`. The transport to `k` should
mirror `tateΔ_eq_prod`:

* the coefficients of the formal `X(u, q)`, `Y(u, q)` are Laurent polynomials in `u` over
  `ℤ` (only the `q⁰`-coefficients also require inverting `1 - u`), so the formal identity
  descends from `RatFunc ℚ` to the subring `ℤ[u, u⁻¹, (1 - u)⁻¹]` by injectivity;
* for `|q| < 1` and `u ∉ qᶻ` the doubly-infinite defining series of `tateX` and `tateY`
  rearrange into power series in `q` with those coefficients evaluated at `u ∈ kˣ` —
  legal, since `u ≠ 0, 1` — by the two-variable analogue of the Lambert rearrangement
  `TateCurve.tsum_lambert` (over `ℂ` this is `TateCurve.hasSum_X_eval` and
  `TateCurve.hasSum_Y_eval`);
* evaluation is a ring homomorphism on convergent series (`evalInt_add`, `evalInt_mul`
  and their two-variable extensions), so the formal identity evaluates to the equation
  in `k`.

Here the general case is reduced to the annulus case `tateCurve_equation_of_annulus`:
normalise `u` into `|q| < |u| ≤ 1` by a power of `q` (`exists_zpow_mul_mem_annulus`),
under which `tateX` and `tateY` are invariant (`tateX_zpow_mul_left`,
`tateY_zpow_mul_left`). -/
theorem WeierstrassCurve.tateCurve_equation (q : kˣ) (hq : valuation k (q : k) < 1)
    (u : kˣ) (hu : u ∉ Subgroup.zpowers q) :
    ((tateCurve (q : k))⁄k).Equation (tateX (u : k) (q : k)) (tateY (u : k) (q : k)) := by
  -- normalise `u` into the annulus `|q| < |·| ≤ 1` by a power of `q`
  obtain ⟨m, h₁, h₂⟩ := TateCurve.exists_zpow_mul_mem_annulus q hq u
  have hu' : q ^ m * u ∉ Subgroup.zpowers q := fun h ↦ hu (by
    have h2 := Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers q) (-m)) h
    rwa [show q ^ (-m) * (q ^ m * u) = u by group] at h2)
  have hu1 : (q ^ m * u : kˣ) ≠ 1 := fun h ↦ hu' (h ▸ Subgroup.one_mem _)
  have hcoe : ((q ^ m * u : kˣ) : k) = (q : k) ^ m * (u : k) := by push_cast; ring
  have h := tateCurve_equation_of_annulus q hq (q ^ m * u) hu1 (by rwa [hcoe])
    (by rwa [hcoe])
  rw [hcoe, tateX_zpow_mul_left, tateY_zpow_mul_left] at h
  exact h

/-- Silverman, ATAEC V.1.1(a): for `u` not a power of `q`, the pair `(X(u, q), Y(u, q))`
is a *nonsingular* point of the Tate curve `E_q`: it satisfies the Weierstrass equation
(`tateCurve_equation`), and every point of a Weierstrass curve with nonvanishing
discriminant is nonsingular (`tateCurve_Δ_ne_zero`, since `0 < |q| < 1`). -/
theorem WeierstrassCurve.tateCurve_nonsingular (q : kˣ) (hq : valuation k (q : k) < 1)
    (u : kˣ) (hu : u ∉ Subgroup.zpowers q) :
    ((tateCurve (q : k))⁄k).Nonsingular (tateX (u : k) (q : k)) (tateY (u : k) (q : k)) := by
  have hΔ : ((tateCurve (q : k))⁄k).Δ ≠ 0 := by
    rw [show (tateCurve (q : k))⁄k = tateCurve (q : k) by
      simp only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]]
    exact tateCurve_Δ_ne_zero (q : k) q.ne_zero hq
  exact (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (tateCurve_equation q hq u hu)
