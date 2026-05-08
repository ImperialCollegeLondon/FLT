/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.Order.Monotone.Union
public import Mathlib.Tactic.NormNum.NatFactorial

/-!
# Discriminant bounds for number fields

Bounds of Minkowski type for the discriminant of a number field, derived from
the comparison between root discriminants and small-degree explicit bounds.
-/

@[expose] public section

open scoped Nat
open Real

-- upstream
theorem strictMonoOn_Ici_nat_of_lt_succ {α : Type*} [Preorder α] {f : ℕ → α} {x : ℕ}
    (h : ∀ n, x ≤ n → f n < f (n + 1)) :
    StrictMonoOn f {i | x ≤ i} :=
  fun _ ha _ _ ↦ Nat.rel_of_forall_rel_succ_of_le_of_lt (· < ·) h ha

-- upstream
theorem strictMonoOn_Ioi_nat_of_lt_succ {α : Type*} [Preorder α] {f : ℕ → α} {x : ℕ}
    (h : ∀ n, x < n → f n < f (n + 1)) :
    StrictMonoOn f (Set.Ioi x) :=
  strictMonoOn_Ici_nat_of_lt_succ (x := x + 1) h

private lemma constant_approx : 9 / 5 < log (2 * π) := by
  rw [lt_log_iff_exp_lt (by positivity), ← Real.exp_one_rpow, div_eq_mul_inv,
    rpow_mul (exp_pos _).le, rpow_inv_lt_iff_of_pos (by positivity) (by positivity) (by positivity)]
  calc
    rexp 1 ^ (9 : ℝ) < 2.72 ^ (9 : ℝ) := by gcongr; linarith [exp_one_lt_d9]
    _ ≤ 6.28 ^ (5 : ℝ) := by norm_num
    _ ≤ (2 * π) ^ (5 : ℝ) := by gcongr; linarith [pi_gt_d4]

private lemma log_approx {x : ℝ} (hx : 0 < x) : (1 + x)⁻¹ ≤ log (1 + x⁻¹) := by calc
  _ ≥ 1 - (1 + x⁻¹)⁻¹ := Real.one_sub_inv_le_log_of_pos (by positivity)
  _ ≥ _ := by field_simp; simp [add_comm]

private lemma rootDiscrBound_strictMono_aux3 {x : ℝ} (hx : 1 ≤ x) :
    -0.5 ≤ log x / 2 - x / (x + 1) := by
  suffices h : StrictMonoOn (fun x ↦ log x / 2 - x / (x + 1)) (Set.Ioi 0) by
    convert h.monotoneOn (by simp) (by simp only [Set.mem_Ioi]; linarith) hx using 1
    norm_num
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioi _)
    (f' := fun x ↦ (x ^ 2 + 1) / (2 * x * (x + 1) ^ 2))
  case hf =>
    refine ((continuousOn_log.mono (by simp)).div_const _).sub
      (continuousOn_id.div (by fun_prop) ?_)
    simp only [Set.mem_Ioi, ne_eq]
    intro x hx
    positivity
  case hf'₀ =>
    simp only [interior_Ioi, Set.mem_Ioi]
    intro x hx
    positivity
  case hf' =>
    simp only [interior_Ioi, Set.mem_Ioi]
    intro x hx
    refine .congr_deriv ((((hasDerivWithinAt_id _ _).log hx.ne').div_const _).sub
      ((hasDerivWithinAt_id _ _).div ((hasDerivWithinAt_id _ _).add_const _) (by linarith))) ?_
    simp only [id_eq, one_div, one_mul, mul_one, add_sub_cancel_left]
    field_simp
    ring

private lemma rootDiscrBound_strictMono_aux2 (n : ℕ) (hn : n ≠ 0) :
    0 < n ^ 2 * (log (n + 1) - log n) + log n ! - n * log n := by
  calc
    _ > n ^ 2 * (log (n + 1) - log n) + 0.9 + log n / 2 - n := by
        linear_combination Stirling.le_log_factorial_stirling hn + constant_approx / 2
    _ ≥ n ^ 2 * log (1 + (n : ℝ)⁻¹) + 0.9 + log n / 2 - n := by
        rw [← log_div (by positivity) (by positivity)]; field_simp; rfl
    _ ≥ n ^ 2 * (1 + n : ℝ)⁻¹ + 0.9 + log n / 2 - n := by
        gcongr; exact log_approx (by positivity)
    _ = log n / 2 - n / (n + 1) + 0.9 := by
        field_simp; ring
    _ ≥ 0 := by
        linear_combination rootDiscrBound_strictMono_aux3 (x := n) (by simp; omega)

private lemma rootDiscrBound_strictMono_aux :
    StrictMonoOn (fun n : ℕ ↦ log n - (n : ℝ)⁻¹ * log n !) (Set.Ioi 0) :=
  strictMonoOn_Ioi_nat_of_lt_succ fun n hn ↦ by
    refine lt_of_mul_lt_mul_left (a := n * (n + 1 : ℝ)) ?_ (by positivity)
    calc
      _ = (n * (n + 1)) * log n - (n + 1) * log n ! := by field_simp
      _ < n * (n + 1) * log (n + 1) - n * (log (n + 1) + log n !) := by
          linear_combination rootDiscrBound_strictMono_aux2 n hn.ne'
      _ = n * (n + 1) * (log (n + 1) - (n + 1 : ℝ)⁻¹ * (log (n + 1) + log n !)) := by
          field_simp
      _ = n * (n + 1) * (log (n + 1 : ℕ) - (↑(n + 1) : ℝ)⁻¹ * log (n + 1)!) := by
          rw [Nat.factorial_succ, Nat.cast_mul, log_mul (by positivity) (by positivity),
            Nat.cast_add_one]

/--
Minkowski's lower bound for the root discriminant (that is, the `n`th root of the absolute value of
the discriminant) of a totally complex number field of degree `n`.
-/
noncomputable def rootDiscrBound (n : ℕ) : ℝ :=
  (π / 4) * (n ^ 2 / (n ! : ℝ) ^ (2 / n : ℝ))

lemma rootDiscrBound_strictMono : StrictMono rootDiscrBound := by
  refine .const_mul (StrictMonoOn.Iic_union_Ici (a := 1) ?_ ?_) (by positivity)
  next =>
    have : Set.Iic 1 = {0, 1} := by simp [Set.ext_iff]; omega
    simp [this, StrictMonoOn]
  refine ((exp_strictMono.comp (strictMono_mul_left_of_pos zero_lt_two)).comp_strictMonoOn
    rootDiscrBound_strictMono_aux).congr fun n (hn : 0 < n) ↦ ?_
  calc
    _ = exp (2 * log n) / exp (2 * ((n : ℝ)⁻¹ * log n !)) := by simp [mul_sub, exp_sub]
    _ = exp (log n * 2) / exp ((log n !) * (2 / n)) := by ring_nf
    _ = (n ^ 2 / n ! ^ (2 / n : ℝ)) := by simp (disch := positivity) [← rpow_def_of_pos]

private lemma rootDiscrBound_four_lt : rootDiscrBound 4 < 2.75 := by
  have h₁ : rootDiscrBound 4 < 2.75 := by calc
    _ = π / 4 * (4 ^ 2 / 4! ^ (2 / 4 : ℝ)) := rfl
    _ < π / 4 * (4 ^ 2 / 4.8) := by
        gcongr
        rw [div_eq_mul_inv, rpow_mul, lt_rpow_inv_iff_of_pos]
        all_goals norm_num
    _ < 2.75 := by linarith [pi_lt_d4]
  exact h₁

private lemma rootDiscrBound_five_gt : 2.75 < rootDiscrBound 5 := by
  have h₁ : 2.75 < rootDiscrBound 5 := by calc _ * _
    _ > π / 4 * (5 ^ 2 / 7) := by
        norm_cast
        gcongr
        rw [div_eq_mul_inv, rpow_mul, rpow_inv_lt_iff_of_pos]
        all_goals norm_num
    _ > 2.75 := by linarith [pi_gt_d4]
  exact h₁

private lemma rootDiscrBound_thirteen_lt :
    rootDiscrBound 13 < 2 ^ (2 / 3 : ℝ) * 3 ^ (7 / 8 : ℝ) := by
  have h₁ : rootDiscrBound 13 < 4.15 := by calc _ * _
    _ < π / 4 * (13 ^ 2 / 32) := by
        norm_cast
        gcongr
        rw [div_eq_mul_inv, rpow_mul, lt_rpow_inv_iff_of_pos]
        all_goals norm_num
    _ < 4.15 := by linarith [pi_lt_d4]
  have h₂ : (4.15 : ℝ) < 2 ^ (2 / 3 : ℝ) * 3 ^ (7 / 8 : ℝ) := by
    rw [← rpow_lt_rpow_iff (z := 24), mul_rpow, ← rpow_mul, ← rpow_mul]
    · norm_num
    all_goals positivity
  exact h₁.trans h₂

private lemma rootDiscrBound_fourteen_gt :
    2 ^ (2 / 3 : ℝ) * 3 ^ (7 / 8 : ℝ) < rootDiscrBound 14 := by
  have h₁ : 4.16 < rootDiscrBound 14 := by calc _ * _
    _ > π / 4 * (14 ^ 2 / 37) := by
        norm_cast
        gcongr
        rw [div_eq_mul_inv, rpow_mul, rpow_inv_lt_iff_of_pos]
        all_goals norm_num
    _ > 4.16 := by linarith [pi_gt_d4]
  have h₂ : 2 ^ (2 / 3 : ℝ) * 3 ^ (7 / 8 : ℝ) < (4.16 : ℝ) := by
    rw [← rpow_lt_rpow_iff (z := 24), mul_rpow, ← rpow_mul, ← rpow_mul]
    · norm_num
    all_goals positivity
  exact h₂.trans h₁

theorem rootDiscrBound_lt_iff_lt_fourteen {n : ℕ} :
    rootDiscrBound n < 2 ^ (2 / 3 : ℝ) * 3 ^ (7 / 8 : ℝ) ↔ n < 14 := by
  refine ⟨fun h ↦ ?mp, fun h ↦ ?mpr⟩
  case mp => exact rootDiscrBound_strictMono.lt_iff_lt.mp (h.trans rootDiscrBound_fourteen_gt)
  case mpr =>
    replace h : n ≤ 13 := by omega
    exact (rootDiscrBound_strictMono.le_iff_le.mpr h).trans_lt rootDiscrBound_thirteen_lt

theorem rootDiscrBound_lt_iff_lt_five {n : ℕ} :
    rootDiscrBound n < 2.75 ↔ n < 5 := by
  refine ⟨fun h ↦ ?mp, fun h ↦ ?mpr⟩
  case mp => exact rootDiscrBound_strictMono.lt_iff_lt.mp (h.trans rootDiscrBound_five_gt)
  case mpr =>
    replace h : n ≤ 4 := by omega
    exact (rootDiscrBound_strictMono.le_iff_le.mpr h).trans_lt rootDiscrBound_four_lt

theorem le_fourteen_of_rootDiscrBound {n : ℕ}
    (h : rootDiscrBound n < 2 ^ (2 / 3 : ℝ) * 3 ^ (7 / 8 : ℝ)) : n ≤ 14 :=
  (rootDiscrBound_lt_iff_lt_fourteen.mp h).le

theorem le_five_of_rootDiscrBound {n : ℕ}
    (h : (π / 4) * (n ^ 2 / (n !) ^ (2 / n : ℝ)) < 2.75) : n ≤ 5 :=
  (rootDiscrBound_lt_iff_lt_five.mp h).le
