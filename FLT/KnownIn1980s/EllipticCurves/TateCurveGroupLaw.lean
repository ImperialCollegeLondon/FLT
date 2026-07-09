/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, William Coram, Samuel Yin
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurvePoint
public import FLT.KnownIn1980s.EllipticCurves.TateCurveAdditionDescent
public import FLT.KnownIn1980s.EllipticCurves.MaybeMathlib

import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import FLT.Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean

/-!
# The Tate curve `E_q`: the group law and injectivity of the uniformisation

The chord-law identities `tateX_mul_of_ne`, `tateY_mul_of_ne` (via the two-variable descent
`TateCurve.chord_x_field`/`chord_y_field` and the wide-annulus evaluation bridges), the additivity
`tateCurvePoint_mul : φ(uv) = φ(u) + φ(v)` (Silverman's Lemma 3.1.2, `map_mul_of_generic`), and the
resulting injectivity `tateCurvePoint_eq_iff : φ(u) = φ(v) ↔ u⁻¹v ∈ qᶻ`.

Fourth of the files split out of `TateCurveUniformisation`.
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

/-! ### Evaluation on the wide annulus, and the chord law

The chord identities `TateCurve.chord_x_field`/`chord_y_field` relate the coordinate
series at `v₁`, `v₂` and the *product* `v₁v₂`. Working with representatives in the
fundamental annulus `|q| < |·| ≤ 1` is not enough (the product of two representatives
can fall below `|q|`), so we extend the evaluation bridges `tateX_eq_evalK`,
`tateY_eq_evalK` to the *wide annulus* `|q| < |u| < |q|⁻¹`, using the formal inversion
symmetries `TateCurve.XField_inv`/`YField_inv` and the value identities `tateX_inv`/
`tateY_inv` for the upper half. `exists_chord_reps` then selects representatives
`a ≡ u`, `b ≡ v (mod qᶻ)` with `a` and `ab` in the fundamental annulus and `b` in the
wide annulus. -/

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The wide-annulus bound for the divisor-sum tail of `XField u`: the summands
`d·u^{±d}` are bounded by `(max |u| |u|⁻¹)ⁿ`, and
`|q|·max |u| |u|⁻¹ = max (|q||u|) (|q||u|⁻¹)` is the stated radius. -/
private theorem TateCurve.evalBounded_XField_tail_wide (q u : kˣ) :
    EvalBounded (q : k) (max (valuation k (q : k) * (valuation k (u : k))⁻¹)
        (valuation k (q : k) * valuation k (u : k)))
      (PowerSeries.mk fun n ↦ ∑ d ∈ n.divisors,
        ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) := by
  have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr (Units.ne_zero u)
  set M := max (valuation k (u : k))⁻¹ (valuation k (u : k)) with hM
  have h1M : (1 : ValueGroupWithZero k) ≤ M := by
    rcases le_total (valuation k (u : k)) 1 with h | h
    · exact le_max_of_le_left ((one_le_inv₀ (zero_lt_iff.mpr hvu)).mpr h)
    · exact le_max_of_le_right h
  have huM : valuation k (u : k) ≤ M := le_max_right _ _
  have hiuM : (valuation k (u : k))⁻¹ ≤ M := le_max_left _ _
  refine ⟨1, one_ne_zero, fun n ↦ ?_⟩
  have h1n : (1 : ValueGroupWithZero k) ≤ M ^ n := by
    calc (1 : ValueGroupWithZero k) = M ^ 0 := (pow_zero _).symm
      _ ≤ M ^ n := pow_le_pow_right' h1M (Nat.zero_le n)
  have hsum : valuation k (∑ d ∈ n.divisors,
      ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) ≤ M ^ n := by
    refine (valuation k).map_sum_le fun d hd ↦ ?_
    have hdn : d ≤ n := Nat.divisor_le hd
    refine le_trans ((valuation k).map_sub _ _) (max_le (le_trans
      ((valuation k).map_add _ _) (max_le ?_ ?_)) ?_)
    · rw [map_mul, map_pow]
      calc valuation k ((d : ℕ) : k) * valuation k (u : k) ^ d
          ≤ 1 * M ^ d := mul_le_mul' (valuation_natCast_le_one d) (pow_le_pow_left' huM d)
        _ = M ^ d := one_mul _
        _ ≤ M ^ n := pow_le_pow_right' h1M hdn
    · rw [map_mul, map_pow, map_inv₀]
      calc valuation k ((d : ℕ) : k) * (valuation k (u : k))⁻¹ ^ d
          ≤ 1 * M ^ d := mul_le_mul' (valuation_natCast_le_one d) (pow_le_pow_left' hiuM d)
        _ = M ^ d := one_mul _
        _ ≤ M ^ n := pow_le_pow_right' h1M hdn
    · rw [show ((2 : k) * (d : k)) = ((2 * d : ℕ) : k) by push_cast; ring]
      exact le_trans (valuation_natCast_le_one _) h1n
  rw [one_mul, PowerSeries.coeff_mk, map_mul, map_pow]
  calc valuation k (∑ d ∈ n.divisors,
        ((d : k) * (u : k) ^ d + (d : k) * ((u : k)⁻¹) ^ d - 2 * (d : k))) *
        valuation k (q : k) ^ n
      ≤ M ^ n * valuation k (q : k) ^ n := mul_le_mul' hsum le_rfl
    _ = valuation k (q : k) ^ n * M ^ n := mul_comm _ _
    _ = (valuation k (q : k) * M) ^ n := (mul_pow _ _ _).symm
    _ = (max (valuation k (q : k) * (valuation k (u : k))⁻¹)
          (valuation k (q : k) * valuation k (u : k))) ^ n := by rw [hM, mul_max]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The wide-annulus bound for the divisor-sum tail of `YField u`; cf.
`evalBounded_XField_tail_wide`. -/
private theorem TateCurve.evalBounded_YField_tail_wide (q u : kˣ) :
    EvalBounded (q : k) (max (valuation k (q : k) * (valuation k (u : k))⁻¹)
        (valuation k (q : k) * valuation k (u : k)))
      (PowerSeries.mk fun n ↦ ∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : k) * (u : k) ^ d
        - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) := by
  have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr (Units.ne_zero u)
  set M := max (valuation k (u : k))⁻¹ (valuation k (u : k)) with hM
  have h1M : (1 : ValueGroupWithZero k) ≤ M := by
    rcases le_total (valuation k (u : k)) 1 with h | h
    · exact le_max_of_le_left ((one_le_inv₀ (zero_lt_iff.mpr hvu)).mpr h)
    · exact le_max_of_le_right h
  have huM : valuation k (u : k) ≤ M := le_max_right _ _
  have hiuM : (valuation k (u : k))⁻¹ ≤ M := le_max_left _ _
  refine ⟨1, one_ne_zero, fun n ↦ ?_⟩
  have h1n : (1 : ValueGroupWithZero k) ≤ M ^ n := by
    calc (1 : ValueGroupWithZero k) = M ^ 0 := (pow_zero _).symm
      _ ≤ M ^ n := pow_le_pow_right' h1M (Nat.zero_le n)
  have hsum : valuation k (∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : k) * (u : k) ^ d
      - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) ≤ M ^ n := by
    refine (valuation k).map_sum_le fun d hd ↦ ?_
    have hdn : d ≤ n := Nat.divisor_le hd
    refine le_trans ((valuation k).map_add _ _) (max_le (le_trans
      ((valuation k).map_sub _ _) (max_le ?_ ?_)) ?_)
    · rw [map_mul, map_pow]
      calc valuation k ((d.choose 2 : ℕ) : k) * valuation k (u : k) ^ d
          ≤ 1 * M ^ d := mul_le_mul' (valuation_natCast_le_one _) (pow_le_pow_left' huM d)
        _ = M ^ d := one_mul _
        _ ≤ M ^ n := pow_le_pow_right' h1M hdn
    · rw [map_mul, map_pow, map_inv₀]
      calc valuation k (((d + 1).choose 2 : ℕ) : k) * (valuation k (u : k))⁻¹ ^ d
          ≤ 1 * M ^ d := mul_le_mul' (valuation_natCast_le_one _) (pow_le_pow_left' hiuM d)
        _ = M ^ d := one_mul _
        _ ≤ M ^ n := pow_le_pow_right' h1M hdn
    · exact le_trans (valuation_natCast_le_one d) h1n
  rw [one_mul, PowerSeries.coeff_mk, map_mul, map_pow]
  calc valuation k (∑ d ∈ n.divisors, (((d.choose 2 : ℕ) : k) * (u : k) ^ d
        - (((d + 1).choose 2 : ℕ) : k) * ((u : k)⁻¹) ^ d + (d : k))) *
        valuation k (q : k) ^ n
      ≤ M ^ n * valuation k (q : k) ^ n := mul_le_mul' hsum le_rfl
    _ = valuation k (q : k) ^ n * M ^ n := mul_comm _ _
    _ = (valuation k (q : k) * M) ^ n := (mul_pow _ _ _).symm
    _ = (max (valuation k (q : k) * (valuation k (u : k))⁻¹)
          (valuation k (q : k) * valuation k (u : k))) ^ n := by rw [hM, mul_max]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The wide-annulus evaluation bound for the `x`-coordinate series: for
`|q||u| < 1` (and `u ≠ 0`), `XField u` is evaluation-bounded with radius
`ρ = max (|q|/|u|) (|q||u|)`, which is `< 1` exactly on the wide annulus
`|q| < |u| < |q|⁻¹`. -/
theorem TateCurve.evalBounded_XField_wide (q u : kˣ) :
    EvalBounded (q : k)
      (max (valuation k (q : k) * (valuation k (u : k))⁻¹)
        (valuation k (q : k) * valuation k (u : k)))
      (XField (u : k)) :=
  (evalBounded_C _ _ _).add (evalBounded_XField_tail_wide q u)

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/-- The wide-annulus evaluation bound for the `y`-coordinate series. -/
theorem TateCurve.evalBounded_YField_wide (q u : kˣ) :
    EvalBounded (q : k)
      (max (valuation k (q : k) * (valuation k (u : k))⁻¹)
        (valuation k (q : k) * valuation k (u : k)))
      (YField (u : k)) :=
  (evalBounded_C _ _ _).add (evalBounded_YField_tail_wide q u)

/-- On the wide annulus `|q| < |u| < |q|⁻¹`, `tateX` is the value at `q` of the formal
series `XField u`: the lower half `|u| ≤ 1` is `tateX_eq_evalK`, and the upper half
reduces to it through the inversion symmetries `tateX_inv` and
`TateCurve.XField_inv`. -/
theorem WeierstrassCurve.tateX_eq_evalK_wide (q u : kˣ) (hq : valuation k (q : k) < 1)
    (h₁ : valuation k (q : k) < valuation k (u : k))
    (h₂ : valuation k ((q : k) * (u : k)) < 1) :
    tateX (u : k) (q : k) = TateCurve.evalK (q : k) (TateCurve.XField (u : k)) := by
  rcases le_or_gt (valuation k (u : k)) 1 with hle | hgt
  · exact tateX_eq_evalK q u hq h₁ hle
  · have hu0 : (u : k) ≠ 0 := Units.ne_zero u
    have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr hu0
    have hcoe : ((u⁻¹ : kˣ) : k) = (u : k)⁻¹ := Units.val_inv_eq_inv_val u
    have hval : valuation k ((u⁻¹ : kˣ) : k) = (valuation k (u : k))⁻¹ := by
      rw [hcoe, map_inv₀]
    have h₂m : valuation k (q : k) * valuation k (u : k) < 1 := by rw [← map_mul]; exact h₂
    have hqinv : valuation k (q : k) < (valuation k (u : k))⁻¹ := by
      rw [← one_div, lt_div_iff₀ (zero_lt_iff.mpr hvu)]; exact h₂m
    have hinv_le : (valuation k (u : k))⁻¹ ≤ 1 := (inv_le_one₀ (zero_lt_iff.mpr hvu)).mpr hgt.le
    have h₁w : valuation k (q : k) < valuation k ((u⁻¹ : kˣ) : k) := by rw [hval]; exact hqinv
    have h₂w : valuation k ((u⁻¹ : kˣ) : k) ≤ 1 := by rw [hval]; exact hinv_le
    calc tateX (u : k) (q : k)
        = tateX ((u⁻¹ : kˣ) : k) (q : k) := by
          rw [hcoe]; exact (tateX_inv (q : k) (u : k)).symm
      _ = TateCurve.evalK (q : k) (TateCurve.XField ((u⁻¹ : kˣ) : k)) :=
          tateX_eq_evalK q u⁻¹ hq h₁w h₂w
      _ = TateCurve.evalK (q : k) (TateCurve.XField (u : k)) := by
          rw [hcoe, TateCurve.XField_inv hu0]

/-- On the wide annulus, `tateY` is the value at `q` of `YField u`; cf.
`tateX_eq_evalK_wide`. -/
theorem WeierstrassCurve.tateY_eq_evalK_wide (q u : kˣ) (hq : valuation k (q : k) < 1)
    (h₁ : valuation k (q : k) < valuation k (u : k))
    (h₂ : valuation k ((q : k) * (u : k)) < 1) :
    tateY (u : k) (q : k) = TateCurve.evalK (q : k) (TateCurve.YField (u : k)) := by
  rcases le_or_gt (valuation k (u : k)) 1 with hle | hgt
  · exact tateY_eq_evalK q u hq h₁ hle
  · have hu0 : (u : k) ≠ 0 := Units.ne_zero u
    have hvu : valuation k (u : k) ≠ 0 := (valuation k).ne_zero_iff.mpr hu0
    have hcoe : ((u⁻¹ : kˣ) : k) = (u : k)⁻¹ := Units.val_inv_eq_inv_val u
    have hval : valuation k ((u⁻¹ : kˣ) : k) = (valuation k (u : k))⁻¹ := by
      rw [hcoe, map_inv₀]
    have h₂m : valuation k (q : k) * valuation k (u : k) < 1 := by rw [← map_mul]; exact h₂
    have hqinv : valuation k (q : k) < (valuation k (u : k))⁻¹ := by
      rw [← one_div, lt_div_iff₀ (zero_lt_iff.mpr hvu)]; exact h₂m
    have hinv_le : (valuation k (u : k))⁻¹ ≤ 1 := (inv_le_one₀ (zero_lt_iff.mpr hvu)).mpr hgt.le
    have h₁w : valuation k (q : k) < valuation k ((u⁻¹ : kˣ) : k) := by rw [hval]; exact hqinv
    have h₂w : valuation k ((u⁻¹ : kˣ) : k) ≤ 1 := by rw [hval]; exact hinv_le
    have hbY : TateCurve.EvalBounded (q : k) (valuation k (q : k) * valuation k (u : k))
        (TateCurve.YField (u : k)⁻¹) := by
      have h := TateCurve.evalBounded_YField q u⁻¹ h₂w
      rwa [hcoe, map_inv₀, inv_inv] at h
    have hbX : TateCurve.EvalBounded (q : k) (valuation k (q : k) * valuation k (u : k))
        (TateCurve.XField (u : k)⁻¹) := by
      have h := TateCurve.evalBounded_XField q u⁻¹ h₂w
      rwa [hcoe, map_inv₀, inv_inv] at h
    have hYw : tateY ((u⁻¹ : kˣ) : k) (q : k) =
        TateCurve.evalK (q : k) (TateCurve.YField ((u⁻¹ : kˣ) : k)) :=
      tateY_eq_evalK q u⁻¹ hq h₁w h₂w
    have hXw : tateX ((u⁻¹ : kˣ) : k) (q : k) =
        TateCurve.evalK (q : k) (TateCurve.XField ((u⁻¹ : kˣ) : k)) :=
      tateX_eq_evalK q u⁻¹ hq h₁w h₂w
    rw [hcoe] at hYw hXw
    have hYinv : TateCurve.YField (u : k) =
        -TateCurve.YField (u : k)⁻¹ - TateCurve.XField (u : k)⁻¹ := by
      have h := TateCurve.YField_inv (inv_ne_zero hu0)
      rwa [inv_inv] at h
    have hinv := tateY_inv q u⁻¹ hq
    rw [hcoe, inv_inv] at hinv
    rw [hinv, hYw, hXw, hYinv, TateCurve.evalK_sub h₂m hbY.neg hbX, TateCurve.evalK_neg]

/-- Representatives for the chord law: any pair `u, v ∈ kˣ` has representatives
`a = qᵐu`, `b = qⁿv` modulo `qᶻ` with `a` and `ab` in the fundamental annulus
`|q| < |·| ≤ 1` and `b` in the wide annulus (`|q| < |b|` and `|qb| < 1`). Take `a` and
`b₀` in the fundamental annulus (`exists_zpow_mul_mem_annulus`); if `|ab₀| > |q|` take
`b = b₀`, otherwise `b = q⁻¹b₀` — in the latter case `|b₀| ≤ |q|/|a| < 1` strictly, so
`|qb| = |b₀| < 1`, while `|ab| = |ab₀|/|q| ∈ (|q|, 1]` since `|q|² < |ab₀| ≤ |q|`. -/
theorem TateCurve.exists_chord_reps (q : kˣ) (hq : valuation k (q : k) < 1) (u v : kˣ) :
    ∃ m n : ℤ,
      valuation k (q : k) < valuation k ((q ^ m * u : kˣ) : k) ∧
      valuation k ((q ^ m * u : kˣ) : k) ≤ 1 ∧
      valuation k (q : k) < valuation k ((q ^ n * v : kˣ) : k) ∧
      valuation k ((q : k) * ((q ^ n * v : kˣ) : k)) < 1 ∧
      valuation k (q : k) < valuation k ((q ^ m * u * (q ^ n * v) : kˣ) : k) ∧
      valuation k ((q ^ m * u * (q ^ n * v) : kˣ) : k) ≤ 1 := by
  have hq0 : (q : k) ≠ 0 := Units.ne_zero q
  have hvq : valuation k (q : k) ≠ 0 := (valuation k).ne_zero_iff.mpr hq0
  have hQpos : 0 < valuation k (q : k) := zero_lt_iff.mpr hvq
  obtain ⟨m, hm1, hm2⟩ := exists_zpow_mul_mem_annulus q hq u
  obtain ⟨n₀, hn1, hn2⟩ := exists_zpow_mul_mem_annulus q hq v
  have eA : ((q ^ m * u : kˣ) : k) = (q : k) ^ m * (u : k) := by
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
  by_cases hab : valuation k (q : k) <
      valuation k ((q : k) ^ m * (u : k) * ((q : k) ^ n₀ * (v : k)))
  · have eB : ((q ^ n₀ * v : kˣ) : k) = (q : k) ^ n₀ * (v : k) := by
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
    have eAB : ((q ^ m * u * (q ^ n₀ * v) : kˣ) : k) =
        (q : k) ^ m * (u : k) * ((q : k) ^ n₀ * (v : k)) := by
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
    refine ⟨m, n₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eA]; exact hm1
    · rw [eA]; exact hm2
    · rw [eB]; exact hn1
    · rw [eB, map_mul]
      calc valuation k (q : k) * valuation k ((q : k) ^ n₀ * (v : k))
          ≤ valuation k (q : k) * 1 := mul_le_mul_right hn2 _
        _ = valuation k (q : k) := mul_one _
        _ < 1 := hq
    · rw [eAB]; exact hab
    · rw [eAB, map_mul]; exact mul_le_one₀ hm2 zero_le hn2
  · rw [not_lt] at hab
    have hb₀1 : valuation k ((q : k) ^ n₀ * (v : k)) < 1 := by
      by_contra h
      rw [not_lt] at h
      have h2 : valuation k ((q : k) ^ m * (u : k)) ≤
          valuation k ((q : k) ^ m * (u : k) * ((q : k) ^ n₀ * (v : k))) := by
        conv_rhs => rw [map_mul]
        exact le_mul_of_one_le_right' h
      exact absurd (hm1.trans_le (h2.trans hab)) (lt_irrefl _)
    have eB : ((q ^ (n₀ - 1) * v : kˣ) : k) = (q : k) ^ (n₀ - 1) * (v : k) := by
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
    have eAB : ((q ^ m * u * (q ^ (n₀ - 1) * v) : kˣ) : k) =
        (q : k) ^ m * (u : k) * ((q : k) ^ (n₀ - 1) * (v : k)) := by
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
    have hqB : (q : k) * ((q : k) ^ (n₀ - 1) * (v : k)) = (q : k) ^ n₀ * (v : k) := by
      rw [← mul_assoc, ← zpow_one_add₀ hq0, show (1 : ℤ) + (n₀ - 1) = n₀ by ring]
    have hQ_B : valuation k (q : k) * valuation k ((q : k) ^ (n₀ - 1) * (v : k)) =
        valuation k ((q : k) ^ n₀ * (v : k)) := by
      rw [← map_mul, hqB]
    have hBval : valuation k ((q : k) ^ (n₀ - 1) * (v : k)) =
        (valuation k (q : k))⁻¹ * valuation k ((q : k) ^ n₀ * (v : k)) := by
      rw [← hQ_B, inv_mul_cancel_left₀ hvq]
    have hqAB : (q : k) * ((q : k) ^ m * (u : k) * ((q : k) ^ (n₀ - 1) * (v : k))) =
        (q : k) ^ m * (u : k) * ((q : k) ^ n₀ * (v : k)) := by
      rw [mul_left_comm (q : k), hqB]
    have hQAB : valuation k (q : k) *
        valuation k ((q : k) ^ m * (u : k) * ((q : k) ^ (n₀ - 1) * (v : k))) =
        valuation k ((q : k) ^ m * (u : k) * ((q : k) ^ n₀ * (v : k))) := by
      rw [← map_mul, hqAB]
    have hABval : valuation k ((q : k) ^ m * (u : k) * ((q : k) ^ (n₀ - 1) * (v : k))) =
        (valuation k (q : k))⁻¹ *
          valuation k ((q : k) ^ m * (u : k) * ((q : k) ^ n₀ * (v : k))) := by
      rw [← hQAB, inv_mul_cancel_left₀ hvq]
    have hQQ : valuation k (q : k) * valuation k (q : k) <
        valuation k ((q : k) ^ n₀ * (v : k)) := by
      calc valuation k (q : k) * valuation k (q : k)
          < valuation k (q : k) * 1 := mul_lt_mul_of_pos_left hq hQpos
        _ = valuation k (q : k) := mul_one _
        _ < valuation k ((q : k) ^ n₀ * (v : k)) := hn1
    have hABbig : valuation k (q : k) * valuation k (q : k) <
        valuation k ((q : k) ^ m * (u : k) * ((q : k) ^ n₀ * (v : k))) := by
      rw [map_mul]
      exact mul_lt_mul_of_pos hm1 hn1 hQpos (hQpos.trans hn1)
    refine ⟨m, n₀ - 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [eA]; exact hm1
    · rw [eA]; exact hm2
    · rw [eB, hBval, lt_inv_mul_iff₀ hQpos]; exact hQQ
    · rw [eB, hqB]; exact hb₀1
    · rw [eAB, hABval, lt_inv_mul_iff₀ hQpos]; exact hABbig
    · rw [eAB, hABval]
      calc (valuation k (q : k))⁻¹ *
            valuation k ((q : k) ^ m * (u : k) * ((q : k) ^ n₀ * (v : k)))
          ≤ (valuation k (q : k))⁻¹ * valuation k (q : k) := mul_le_mul_right hab _
        _ = 1 := inv_mul_cancel₀ hvq

/-- The chord identities of `TateCurve.chord_x_field`/`chord_y_field`, transported to the
`tate`-coordinate *values* at `u, v, uv` via representatives in the (wide) annulus. This
is the common analytic core of `tateX_mul_of_ne` and `tateY_mul_of_ne`. -/
private theorem WeierstrassCurve.chord_law_values (q : kˣ) (hq : valuation k (q : k) < 1)
    (u v : kˣ) (hu : u ∉ Subgroup.zpowers q) (hv : v ∉ Subgroup.zpowers q)
    (huv : u * v ∉ Subgroup.zpowers q) :
    (tateX (u : k) (q : k) - tateX (v : k) (q : k)) ^ 2 * tateX ((u : k) * (v : k)) (q : k) =
        (tateY (u : k) (q : k) - tateY (v : k) (q : k)) ^ 2
          + (tateY (u : k) (q : k) - tateY (v : k) (q : k))
              * (tateX (u : k) (q : k) - tateX (v : k) (q : k))
          - (tateX (u : k) (q : k) + tateX (v : k) (q : k))
              * (tateX (u : k) (q : k) - tateX (v : k) (q : k)) ^ 2 ∧
      (tateX (v : k) (q : k) - tateX (u : k) (q : k)) * tateY ((u : k) * (v : k)) (q : k) =
        -((tateY (v : k) (q : k) - tateY (u : k) (q : k))
            + (tateX (v : k) (q : k) - tateX (u : k) (q : k))) * tateX ((u : k) * (v : k)) (q : k)
          - (tateY (u : k) (q : k) * tateX (v : k) (q : k)
            - tateY (v : k) (q : k) * tateX (u : k) (q : k)) := by
  obtain ⟨m, n, ha1, ha2, hb1, hb2, hab1, hab2⟩ := TateCurve.exists_chord_reps q hq u v
  -- coercion identities
  have eA : ((q ^ m * u : kˣ) : k) = (q : k) ^ m * (u : k) := by
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
  have eB : ((q ^ n * v : kˣ) : k) = (q : k) ^ n * (v : k) := by
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]
  have hABmul : ((q ^ m * u * (q ^ n * v) : kˣ) : k) =
      ((q ^ m * u : kˣ) : k) * ((q ^ n * v : kˣ) : k) := Units.val_mul _ _
  have hABcoe : ((q ^ m * u : kˣ) : k) * ((q ^ n * v : kˣ) : k) =
      (q : k) ^ (m + n) * ((u : k) * (v : k)) := by
    rw [eA, eB, zpow_add₀ (Units.ne_zero q)]; ring
  -- the value transports (qᶻ-invariance)
  have hXA : tateX ((q ^ m * u : kˣ) : k) (q : k) = tateX (u : k) (q : k) := by
    rw [eA]; exact tateX_zpow_mul_left q m (u : k)
  have hXB : tateX ((q ^ n * v : kˣ) : k) (q : k) = tateX (v : k) (q : k) := by
    rw [eB]; exact tateX_zpow_mul_left q n (v : k)
  have hYA : tateY ((q ^ m * u : kˣ) : k) (q : k) = tateY (u : k) (q : k) := by
    rw [eA]; exact tateY_zpow_mul_left q m (u : k)
  have hYB : tateY ((q ^ n * v : kˣ) : k) (q : k) = tateY (v : k) (q : k) := by
    rw [eB]; exact tateY_zpow_mul_left q n (v : k)
  have hXAB : tateX (((q ^ m * u : kˣ) : k) * ((q ^ n * v : kˣ) : k)) (q : k) =
      tateX ((u : k) * (v : k)) (q : k) := by
    rw [hABcoe]; exact tateX_zpow_mul_left q (m + n) ((u : k) * (v : k))
  have hYAB : tateY (((q ^ m * u : kˣ) : k) * ((q ^ n * v : kˣ) : k)) (q : k) =
      tateY ((u : k) * (v : k)) (q : k) := by
    rw [hABcoe]; exact tateY_zpow_mul_left q (m + n) ((u : k) * (v : k))
  -- upper-bound facts for the wide bridges
  have h₂A : valuation k ((q : k) * ((q ^ m * u : kˣ) : k)) < 1 := by
    rw [map_mul]
    calc valuation k (q : k) * valuation k ((q ^ m * u : kˣ) : k)
        ≤ valuation k (q : k) * 1 := mul_le_mul_right ha2 _
      _ = valuation k (q : k) := mul_one _
      _ < 1 := hq
  have h₂AB : valuation k ((q : k) * ((q ^ m * u * (q ^ n * v) : kˣ) : k)) < 1 := by
    rw [map_mul]
    calc valuation k (q : k) * valuation k ((q ^ m * u * (q ^ n * v) : kˣ) : k)
        ≤ valuation k (q : k) * 1 := mul_le_mul_right hab2 _
      _ = valuation k (q : k) := mul_one _
      _ < 1 := hq
  -- the bridges evalK ↦ value
  have bridgeXA : TateCurve.evalK (q : k) (TateCurve.XField ((q ^ m * u : kˣ) : k)) =
      tateX (u : k) (q : k) := (tateX_eq_evalK_wide q (q ^ m * u) hq ha1 h₂A).symm.trans hXA
  have bridgeXB : TateCurve.evalK (q : k) (TateCurve.XField ((q ^ n * v : kˣ) : k)) =
      tateX (v : k) (q : k) := (tateX_eq_evalK_wide q (q ^ n * v) hq hb1 hb2).symm.trans hXB
  have bridgeYA : TateCurve.evalK (q : k) (TateCurve.YField ((q ^ m * u : kˣ) : k)) =
      tateY (u : k) (q : k) := (tateY_eq_evalK_wide q (q ^ m * u) hq ha1 h₂A).symm.trans hYA
  have bridgeYB : TateCurve.evalK (q : k) (TateCurve.YField ((q ^ n * v : kˣ) : k)) =
      tateY (v : k) (q : k) := (tateY_eq_evalK_wide q (q ^ n * v) hq hb1 hb2).symm.trans hYB
  have bridgeXAB : TateCurve.evalK (q : k)
      (TateCurve.XField (((q ^ m * u : kˣ) : k) * ((q ^ n * v : kˣ) : k))) =
      tateX ((u : k) * (v : k)) (q : k) := by
    have h := (tateX_eq_evalK_wide q (q ^ m * u * (q ^ n * v)) hq hab1 h₂AB).symm
    rw [hABmul] at h; exact h.trans hXAB
  have bridgeYAB : TateCurve.evalK (q : k)
      (TateCurve.YField (((q ^ m * u : kˣ) : k) * ((q ^ n * v : kˣ) : k))) =
      tateY ((u : k) * (v : k)) (q : k) := by
    have h := (tateY_eq_evalK_wide q (q ^ m * u * (q ^ n * v)) hq hab1 h₂AB).symm
    rw [hABmul] at h; exact h.trans hYAB
  -- memberships of the representatives
  have hqmem : ∀ j : ℤ, q ^ j ∈ Subgroup.zpowers q := fun j ↦ zpow_mem (Subgroup.mem_zpowers q) j
  have hA : q ^ m * u ∉ Subgroup.zpowers q := by
    intro h; refine hu ?_
    have := mul_mem (hqmem (-m)) h
    rwa [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul] at this
  have hB : q ^ n * v ∉ Subgroup.zpowers q := by
    intro h; refine hv ?_
    have := mul_mem (hqmem (-n)) h
    rwa [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul] at this
  have hABeq : q ^ m * u * (q ^ n * v) = q ^ (m + n) * (u * v) := by
    rw [zpow_add, mul_mul_mul_comm]
  have hABmem : q ^ m * u * (q ^ n * v) ∉ Subgroup.zpowers q := by
    intro h; refine huv ?_
    rw [hABeq] at h
    have := mul_mem (hqmem (-(m + n))) h
    rwa [← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul] at this
  -- field genericity facts
  have hval1 : ∀ w : kˣ, w ∉ Subgroup.zpowers q → (w : k) ≠ 1 := by
    intro w hw hcon
    apply hw
    rw [Units.val_eq_one.mp hcon]
    exact Subgroup.one_mem _
  have hA0 : ((q ^ m * u : kˣ) : k) ≠ 0 := Units.ne_zero _
  have hB0 : ((q ^ n * v : kˣ) : k) ≠ 0 := Units.ne_zero _
  have hA1 : ((q ^ m * u : kˣ) : k) ≠ 1 := hval1 _ hA
  have hB1 : ((q ^ n * v : kˣ) : k) ≠ 1 := hval1 _ hB
  have hAB1 : ((q ^ m * u : kˣ) : k) * ((q ^ n * v : kˣ) : k) ≠ 1 := by
    rw [← hABmul]; exact hval1 _ hABmem
  -- the common radius and the six evaluation bounds
  have pA : (0 : ValueGroupWithZero k) < valuation k ((q ^ m * u : kˣ) : k) :=
    zero_lt_iff.mpr ((valuation k).ne_zero_iff.mpr (Units.ne_zero _))
  have pB : (0 : ValueGroupWithZero k) < valuation k ((q ^ n * v : kˣ) : k) :=
    zero_lt_iff.mpr ((valuation k).ne_zero_iff.mpr (Units.ne_zero _))
  have pAB : (0 : ValueGroupWithZero k) < valuation k ((q ^ m * u * (q ^ n * v) : kˣ) : k) :=
    zero_lt_iff.mpr ((valuation k).ne_zero_iff.mpr (Units.ne_zero _))
  set ρ := max (max (valuation k (q : k) * (valuation k ((q ^ m * u : kˣ) : k))⁻¹)
        (valuation k (q : k) * valuation k ((q ^ m * u : kˣ) : k)))
      (max (max (valuation k (q : k) * (valuation k ((q ^ n * v : kˣ) : k))⁻¹)
          (valuation k (q : k) * valuation k ((q ^ n * v : kˣ) : k)))
        (max (valuation k (q : k) * (valuation k ((q ^ m * u * (q ^ n * v) : kˣ) : k))⁻¹)
          (valuation k (q : k) * valuation k ((q ^ m * u * (q ^ n * v) : kˣ) : k)))) with hρdef
  have hρ : ρ < 1 := by
    rw [hρdef]
    refine max_lt (max_lt ?_ ?_) (max_lt (max_lt ?_ ?_) (max_lt ?_ ?_))
    · rw [← div_eq_mul_inv]; exact (div_lt_one₀ pA).mpr ha1
    · calc valuation k (q : k) * valuation k ((q ^ m * u : kˣ) : k)
          ≤ valuation k (q : k) * 1 := mul_le_mul_right ha2 _
        _ = valuation k (q : k) := mul_one _
        _ < 1 := hq
    · rw [← div_eq_mul_inv]; exact (div_lt_one₀ pB).mpr hb1
    · rw [← map_mul]; exact hb2
    · rw [← div_eq_mul_inv]; exact (div_lt_one₀ pAB).mpr hab1
    · calc valuation k (q : k) * valuation k ((q ^ m * u * (q ^ n * v) : kˣ) : k)
          ≤ valuation k (q : k) * 1 := mul_le_mul_right hab2 _
        _ = valuation k (q : k) := mul_one _
        _ < 1 := hq
  have bXA : TateCurve.EvalBounded (q : k) ρ (TateCurve.XField ((q ^ m * u : kˣ) : k)) :=
    (TateCurve.evalBounded_XField_wide q (q ^ m * u)).mono (by rw [hρdef]; exact le_max_left _ _)
  have bYA : TateCurve.EvalBounded (q : k) ρ (TateCurve.YField ((q ^ m * u : kˣ) : k)) :=
    (TateCurve.evalBounded_YField_wide q (q ^ m * u)).mono (by rw [hρdef]; exact le_max_left _ _)
  have bXB : TateCurve.EvalBounded (q : k) ρ (TateCurve.XField ((q ^ n * v : kˣ) : k)) :=
    (TateCurve.evalBounded_XField_wide q (q ^ n * v)).mono
      (by rw [hρdef]; exact le_max_of_le_right (le_max_left _ _))
  have bYB : TateCurve.EvalBounded (q : k) ρ (TateCurve.YField ((q ^ n * v : kˣ) : k)) :=
    (TateCurve.evalBounded_YField_wide q (q ^ n * v)).mono
      (by rw [hρdef]; exact le_max_of_le_right (le_max_left _ _))
  have bXAB : TateCurve.EvalBounded (q : k) ρ
      (TateCurve.XField (((q ^ m * u : kˣ) : k) * ((q ^ n * v : kˣ) : k))) := by
    have h : TateCurve.EvalBounded (q : k) ρ
        (TateCurve.XField ((q ^ m * u * (q ^ n * v) : kˣ) : k)) :=
      (TateCurve.evalBounded_XField_wide q (q ^ m * u * (q ^ n * v))).mono
        (by rw [hρdef]; exact le_max_of_le_right (le_max_right _ _))
    rwa [hABmul] at h
  have bYAB : TateCurve.EvalBounded (q : k) ρ
      (TateCurve.YField (((q ^ m * u : kˣ) : k) * ((q ^ n * v : kˣ) : k))) := by
    have h : TateCurve.EvalBounded (q : k) ρ
        (TateCurve.YField ((q ^ m * u * (q ^ n * v) : kˣ) : k)) :=
      (TateCurve.evalBounded_YField_wide q (q ^ m * u * (q ^ n * v))).mono
        (by rw [hρdef]; exact le_max_of_le_right (le_max_right _ _))
    rwa [hABmul] at h
  refine ⟨?_, ?_⟩
  · have hcx := TateCurve.chord_x_field (K := k) hA0 hA1 hB0 hB1 hAB1
    have h := congrArg (TateCurve.evalK (q : k)) hcx
    simp only [TateCurve.evalK_mul hρ ((bXA.sub bXB).pow 2) bXAB,
      TateCurve.evalK_pow hρ (bXA.sub bXB) 2,
      TateCurve.evalK_sub hρ (((bYA.sub bYB).pow 2).add ((bYA.sub bYB).mul (bXA.sub bXB)))
        ((bXA.add bXB).mul ((bXA.sub bXB).pow 2)),
      TateCurve.evalK_add hρ ((bYA.sub bYB).pow 2) ((bYA.sub bYB).mul (bXA.sub bXB)),
      TateCurve.evalK_pow hρ (bYA.sub bYB) 2,
      TateCurve.evalK_mul hρ (bYA.sub bYB) (bXA.sub bXB),
      TateCurve.evalK_mul hρ (bXA.add bXB) ((bXA.sub bXB).pow 2),
      TateCurve.evalK_sub hρ bYA bYB, TateCurve.evalK_sub hρ bXA bXB,
      TateCurve.evalK_add hρ bXA bXB,
      bridgeXA, bridgeXB, bridgeXAB, bridgeYA, bridgeYB] at h
    linear_combination h
  · have hcy := TateCurve.chord_y_field (K := k) hA0 hA1 hB0 hB1 hAB1
    have h := congrArg (TateCurve.evalK (q : k)) hcy
    simp only [TateCurve.evalK_mul hρ (bXB.sub bXA) bYAB,
      TateCurve.evalK_sub hρ bXB bXA,
      TateCurve.evalK_sub hρ (((bYB.sub bYA).add (bXB.sub bXA)).neg.mul bXAB)
        ((bYA.mul bXB).sub (bYB.mul bXA)),
      TateCurve.evalK_mul hρ ((bYB.sub bYA).add (bXB.sub bXA)).neg bXAB,
      TateCurve.evalK_neg,
      TateCurve.evalK_add hρ (bYB.sub bYA) (bXB.sub bXA),
      TateCurve.evalK_sub hρ bYB bYA,
      TateCurve.evalK_sub hρ (bYA.mul bXB) (bYB.mul bXA),
      TateCurve.evalK_mul hρ bYA bXB, TateCurve.evalK_mul hρ bYB bXA,
      bridgeXA, bridgeXB, bridgeYA, bridgeYB, bridgeXAB, bridgeYAB] at h
    linear_combination h

/-- The chord law for the `x`-coordinate of Tate's uniformisation, for a pair in general
position (`u, v, uv ∉ qᶻ` and `X(u) ≠ X(v)`): with `λ = (Y(u) - Y(v))/(X(u) - X(v))` the
slope of the chord,

`X(uv) = λ² + λ - X(u) - X(v)`,

which is mathlib's `WeierstrassCurve.Affine.addX` for `y² + xy = x³ + a₄x + a₆`
(`a₁ = 1`, `a₂ = 0`). This is the first of the two identities to which Silverman reduces
additivity of the uniformisation (proof of ATAEC V.3.1(c)).

Intended proof, mirroring `tateCurve_equation`: both sides, multiplied by
`(X(u) - X(v))²`, are values of universal power series in `q` whose coefficients are
Laurent polynomials in `u, v` over `ℤ` localised away from
`uv(1-u)(1-v)(u-v)(1-uv)`; the identity of formal series holds over `ℂ` by the addition
theorem for the Weierstrass `℘`-function (the analytic input, not yet formalised — the
`℘`-analogue of `TateCurve.Blueprint.analytic_weierstrass`), descends to the
two-variable initial ring `ℤ[t₁, t₂][(t₁t₂(1-t₁)(1-t₂)(t₁-t₂)(1-t₁t₂))⁻¹]` (the
two-variable analogue of `TateCurve.CoeffRing` in `TateCurveDescent`), and evaluates on
the annulus through the `evalK` calculus above. -/
theorem WeierstrassCurve.tateX_mul_of_ne (q : kˣ) (hq : valuation k (q : k) < 1)
    (u v : kˣ) (hu : u ∉ Subgroup.zpowers q) (hv : v ∉ Subgroup.zpowers q)
    (huv : u * v ∉ Subgroup.zpowers q)
    (hX : tateX (u : k) (q : k) ≠ tateX (v : k) (q : k)) :
    tateX ((u : k) * (v : k)) (q : k) =
      ((tateY (u : k) (q : k) - tateY (v : k) (q : k)) /
          (tateX (u : k) (q : k) - tateX (v : k) (q : k))) ^ 2 +
        (tateY (u : k) (q : k) - tateY (v : k) (q : k)) /
          (tateX (u : k) (q : k) - tateX (v : k) (q : k)) -
        tateX (u : k) (q : k) - tateX (v : k) (q : k) := by
  have hne : tateX (u : k) (q : k) - tateX (v : k) (q : k) ≠ 0 := sub_ne_zero.mpr hX
  have P1 := (chord_law_values q hq u v hu hv huv).1
  field_simp
  linear_combination P1

/-- The chord law for the `y`-coordinate of Tate's uniformisation, for a pair in general
position: with `λ` the chord slope and `X(uv)` as in `tateX_mul_of_ne`,

`Y(uv) = -(Y(u) + λ(X(uv) - X(u))) - X(uv)`,

which is mathlib's `WeierstrassCurve.Affine.addY` for `y² + xy = x³ + a₄x + a₆`
(`a₁ = 1`, `a₃ = 0`). Same intended proof (two-variable descent) as
`tateX_mul_of_ne`. -/
theorem WeierstrassCurve.tateY_mul_of_ne (q : kˣ) (hq : valuation k (q : k) < 1)
    (u v : kˣ) (hu : u ∉ Subgroup.zpowers q) (hv : v ∉ Subgroup.zpowers q)
    (huv : u * v ∉ Subgroup.zpowers q)
    (hX : tateX (u : k) (q : k) ≠ tateX (v : k) (q : k)) :
    tateY ((u : k) * (v : k)) (q : k) =
      -(tateY (u : k) (q : k) +
          (tateY (u : k) (q : k) - tateY (v : k) (q : k)) /
            (tateX (u : k) (q : k) - tateX (v : k) (q : k)) *
            (tateX ((u : k) * (v : k)) (q : k) - tateX (u : k) (q : k))) -
        tateX ((u : k) * (v : k)) (q : k) := by
  have hne : tateX (u : k) (q : k) - tateX (v : k) (q : k) ≠ 0 := sub_ne_zero.mpr hX
  have P2 := (chord_law_values q hq u v hu hv huv).2
  field_simp
  linear_combination -P2

-- `DecidableEq k` is needed for the group law on the points
variable [DecidableEq k] in
/-- **Additivity of Tate's uniformisation** (the homomorphism property in Silverman's
proof of ATAEC V.3.1(c)): `φ(uv) = φ(u) + φ(v)` for `φ = tateCurvePoint q hq`.

Proof plan, following Silverman. The degenerate pairs are handled directly: if `u ∈ qᶻ`
or `v ∈ qᶻ` this is `qᶻ`-periodicity (`tateCurvePoint_eq`), and if `uv ∈ qᶻ` then
`v ≡ u⁻¹ (mod qᶻ)` and it is Stage 1 (`tateCurvePoint_inv`). For a pair in general
position (`u, v, uv ∉ qᶻ` and `X(u) ≠ X(v)`) the chord identities `tateX_mul_of_ne`,
`tateY_mul_of_ne` are precisely mathlib's addition formulas
(`Affine.Point.add_some_of_X_ne`-shape, with slope `Affine.slope_of_X_ne`). The
remaining pairs (`u, v, uv ∉ qᶻ` but `X(u) = X(v)`) need no further identities: by
`map_mul_of_generic` (Silverman's Lemma 3.1.2) it suffices to pick an auxiliary `w`
whose value `φ(w)` avoids six values `±φ(b)`, `±φ(a) - φ(b)`, `±φ(ab)` — possible
because `φ` takes infinitely many distinct values: `|X(1 + qᵐ, q)| = |q|⁻²ᵐ` for
`m ≥ 1`, by the annulus expansion (the leading term `u/(1-u)²` dominates the tail
ultrametrically, `valuation_tsum_le`). -/
theorem WeierstrassCurve.tateCurvePoint_mul (q : kˣ) (hq : valuation k (q : k) < 1)
    (u v : kˣ) :
    tateCurvePoint q hq (u * v) = tateCurvePoint q hq u + tateCurvePoint q hq v := by
  set φ : kˣ → ((tateCurve (q : k))⁄k).Point := tateCurvePoint q hq with hφ
  -- the degenerate pairs, handled directly
  have hzl : ∀ a b : kˣ, a ∈ Subgroup.zpowers q → φ (a * b) = φ a + φ b := by
    intro a b ha
    have hab : φ (a * b) = φ b := tateCurvePoint_eq q hq (a * b) b (by
      rw [show (a * b)⁻¹ * b = a⁻¹ by rw [mul_comm a b]; group]
      exact inv_mem ha)
    rw [hab, hφ, (tateCurvePoint_eq_zero_iff q hq).mpr ha, zero_add]
  have hzr : ∀ a b : kˣ, b ∈ Subgroup.zpowers q → φ (a * b) = φ a + φ b := by
    intro a b hb
    rw [mul_comm a b, hzl b a hb, add_comm]
  have hzm : ∀ a b : kˣ, a * b ∈ Subgroup.zpowers q → φ (a * b) = φ a + φ b := by
    intro a b hab
    have hb : φ b = φ a⁻¹ := tateCurvePoint_eq q hq b a⁻¹ (by
      rw [show b⁻¹ * a⁻¹ = (a * b)⁻¹ by group]
      exact inv_mem hab)
    rw [hφ, (tateCurvePoint_eq_zero_iff q hq).mpr hab, ← hφ, hb, hφ,
      tateCurvePoint_inv q hq a, add_neg_cancel]
  -- the identity off the bad set, via the chord law
  set Bad : Set (kˣ × kˣ) := {p | p.1 ∉ Subgroup.zpowers q ∧ p.2 ∉ Subgroup.zpowers q ∧
    p.1 * p.2 ∉ Subgroup.zpowers q ∧ tateX (p.1 : k) (q : k) = tateX (p.2 : k) (q : k)}
    with hBad
  have hcurve : (tateCurve (q : k))⁄k = tateCurve (q : k) := by
    simp only [WeierstrassCurve.baseChange, Algebra.algebraMap_self, WeierstrassCurve.map_id]
  have hmul : ∀ a b : kˣ, (a, b) ∉ Bad → φ (a * b) = φ a + φ b := by
    intro a b hab
    by_cases ha : a ∈ Subgroup.zpowers q
    · exact hzl a b ha
    by_cases hb : b ∈ Subgroup.zpowers q
    · exact hzr a b hb
    by_cases hm : a * b ∈ Subgroup.zpowers q
    · exact hzm a b hm
    have hX : tateX (a : k) (q : k) ≠ tateX (b : k) (q : k) := fun h ↦
      hab ⟨ha, hb, hm, h⟩
    rw [hφ, tateCurvePoint, dif_neg hm, tateCurvePoint, dif_neg ha, tateCurvePoint,
      dif_neg hb, Affine.Point.add_of_X_ne hX]
    simp only [Affine.Point.some.injEq]
    constructor
    · rw [Units.val_mul, tateX_mul_of_ne q hq a b ha hb hm hX,
        Affine.slope_of_X_ne hX, hcurve, Affine.addX,
        show (tateCurve (q : k)).a₁ = 1 from rfl,
        show (tateCurve (q : k)).a₂ = 0 from rfl]
      ring
    · rw [Units.val_mul, tateY_mul_of_ne q hq a b ha hb hm hX,
        tateX_mul_of_ne q hq a b ha hb hm hX, Affine.slope_of_X_ne hX, hcurve,
        Affine.addY, Affine.negAddY, Affine.addX, Affine.negY,
        show (tateCurve (q : k)).a₁ = 1 from rfl,
        show (tateCurve (q : k)).a₂ = 0 from rfl,
        show (tateCurve (q : k)).a₃ = 0 from rfl]
      ring
  -- the auxiliary-element trick: every pair has a `w` making the three pairs good
  have key : ∀ x y : kˣ, φ y ≠ φ x → φ y ≠ -φ x → (x, y) ∉ Bad := by
    intro x y h1 h2 hbad
    obtain ⟨hx, hy, -, hX⟩ := hbad
    rcases tateCurvePoint_eq_or_eq_neg q hq hx hy hX with h | h
    · exact h1 h
    · exact h2 h
  have hgen : ∀ a b : kˣ, ∃ w : kˣ,
      (a * b, w) ∉ Bad ∧ (a, b * w) ∉ Bad ∧ (b, w) ∉ Bad := by
    intro a b
    obtain ⟨w, hw⟩ := exists_tateCurvePoint_notMem q hq (S := {φ (a * b), -φ (a * b),
      φ b, -φ b, φ a - φ b, -φ a - φ b}) (Set.toFinite _)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or, ← hφ] at hw
    obtain ⟨hw₁, hw₂, hw₃, hw₄, hw₅, hw₆⟩ := hw
    have hbw : φ (b * w) = φ b + φ w := hmul b w (key b w hw₃ hw₄)
    refine ⟨w, key (a * b) w hw₁ hw₂, key a (b * w) ?_ ?_, key b w hw₃ hw₄⟩
    · rw [hbw]
      intro h
      exact hw₅ (eq_sub_of_add_eq' h)
    · rw [hbw]
      intro h
      exact hw₆ (eq_sub_of_add_eq' h)
  exact map_mul_of_generic φ Bad hmul hgen u v

/-- **Injectivity of Tate's uniformisation**: `φ(u) = φ(v)` if and only if
`u ≡ v (mod qᶻ)`. Free from additivity and the definitional kernel:
`φ(u) = φ(v)` gives `φ(u⁻¹v) = -φ(u) + φ(v) = O`, so `u⁻¹v ∈ qᶻ` by
`tateCurvePoint_eq_zero_iff`. (Silverman, proof of ATAEC V.3.1(c); note that no
theta-function machinery is involved.) -/
theorem WeierstrassCurve.tateCurvePoint_eq_iff (q : kˣ) (hq : valuation k (q : k) < 1)
    (u v : kˣ) :
    tateCurvePoint q hq u = tateCurvePoint q hq v ↔ u⁻¹ * v ∈ Subgroup.zpowers q := by
  classical
  constructor
  · intro h
    rw [← tateCurvePoint_eq_zero_iff q hq (u := u⁻¹ * v), tateCurvePoint_mul q hq u⁻¹ v,
      tateCurvePoint_inv q hq u, h, neg_add_cancel]
  · exact fun h ↦ tateCurvePoint_eq q hq u v h
