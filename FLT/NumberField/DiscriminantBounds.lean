/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Complex.ExponentialBounds
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic.NormNum.NatFactorial

open scoped Nat
open Real

namespace Stirling

open Filter

-- upstream
theorem sqrt_pi_le_stirlingSeq {n : ℕ} (hn : n ≠ 0) : √π ≤ stirlingSeq n :=
  match n, hn with
  | n + 1, _ =>
    stirlingSeq'_antitone.le_of_tendsto (b := n) <|
      tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)

theorem semi_precise_stirling (n : ℕ) : √(2 * π * n) * (n / exp 1) ^ n ≤ n ! := by
  obtain rfl | hn := eq_or_ne n 0
  case inl => simp
  calc
    _ = (√(π * (2 * n)) * (n / exp 1) ^ n) := by congr! 2; ring
    _ = (√π * √(2 * n) * (n / exp 1) ^ n) := by congr! 1; simp [sqrt_mul']
    _ = √π * (√(2 * n) * (n / exp 1) ^ n) := by ring
  rw [← le_div_iff₀ (by positivity)]
  exact sqrt_pi_le_stirlingSeq hn

theorem semi_precise_stirling_log (n : ℕ) (hn : n ≠ 0) :
    log (2 * π) / 2 + log n / 2 + n * log n - n ≤ log n ! := by calc
      log ↑n ! ≥ log (√(2 * π * n) * (n / rexp 1) ^ n) :=
          log_le_log (by positivity) (semi_precise_stirling n)
      _ ≥ (log (2 * π) + log ↑n) / 2 + ↑n * (log ↑n - 1) := by
          rw [log_mul, log_sqrt, log_mul, log_pow, log_div, log_exp]
          all_goals positivity
      _ = _ := by ring

private lemma constant_approx : 9 / 5 < log (2 * π) := by
  rw [lt_log_iff_exp_lt (by positivity), ← Real.exp_one_rpow, div_eq_mul_inv,
    rpow_mul (exp_pos _).le, rpow_inv_lt_iff_of_pos (by positivity) (by positivity) (by positivity)]
  calc
    rexp 1 ^ (9 : ℝ) < 2.72 ^ (9 : ℝ) := by gcongr; linarith [exp_one_lt_d9]
    _ ≤ 6.28 ^ (5 : ℝ) := by norm_num
    _ ≤ (2 * π) ^ (5 : ℝ) := by gcongr; linarith [pi_gt_d4]

end Stirling

private lemma log_approx {x : ℝ} (hx : 0 < x) : (1 + x)⁻¹ ≤ log (1 + x⁻¹) := by calc
  _ ≥ 1 - (1 + x⁻¹)⁻¹ := Real.one_sub_inv_le_log_of_pos (by positivity)
  _ ≥ _ := by field_simp [add_comm]

lemma kevinsFunction_strictMono_aux3 {x : ℝ} (hx : 1 ≤ x) : -0.5 ≤ log x / 2 - x / (x + 1) := by
  set f : ℝ → ℝ := fun x ↦ log x / 2 - x / (x + 1)
  suffices h : StrictMonoOn f (Set.Ioi 0) by
    convert h.monotoneOn (by simp) (by simp; linarith) hx using 1
    norm_num [f]
  apply strictMonoOn_of_hasDerivWithinAt_pos
    (f' := fun x ↦ (x ^ 2 + 1) / (2 * x * (x + 1) ^ 2))
    (convex_Ioi _)
  case hf =>
    refine ((continuousOn_log.mono (by simp)).div_const _).sub
      (continuousOn_id.div (by fun_prop) ?_)
    simp only [Set.mem_Ioi, ne_eq, f]
    intro x hx
    linarith
  case hf'₀ =>
    simp only [interior_Ioi, Set.mem_Ioi, f]
    intro x hx
    positivity
  case hf' =>
    simp only [interior_Ioi, Set.mem_Ioi, f]
    intro x hx
    refine HasDerivWithinAt.congr_deriv ((((hasDerivWithinAt_id _ _).log hx.ne').div_const _).sub
      ((hasDerivWithinAt_id _ _).div ((hasDerivWithinAt_id _ _).add_const _) (by linarith))) ?_
    field_simp
    ring

lemma kevinsFunction_strictMono_aux2 (n : ℕ) (hn : n ≠ 0) :
    0 < n ^ 2 * (log (n + 1) - log n) + log n ! - n * log n := by
  calc
    _ > n ^ 2 * (log (n + 1) - log n) + 0.9 + log n / 2 - n := by
        linear_combination Stirling.semi_precise_stirling_log n hn + Stirling.constant_approx / 2
    _ ≥ n ^ 2 * log (1 + (n : ℝ)⁻¹) + 0.9 + log n / 2 - n := by
        rw [← log_div (by positivity) (by positivity)]; field_simp
    _ ≥ n ^ 2 * (1 + n : ℝ)⁻¹ + 0.9 + log n / 2 - n := by
        gcongr; exact log_approx (by positivity)
    _ = log n / 2 - n / (n + 1) + 0.9 := by
        field_simp; ring
    _ ≥ 0 := by
        linear_combination kevinsFunction_strictMono_aux3 (x := n) (by simp; omega)

-- upstream
theorem strictMonoOn_Ici_nat_of_lt_succ {α : Type*} [Preorder α] {f : ℕ → α} {x : ℕ}
    (h : ∀ n, x ≤ n → f n < f (n + 1)) :
    StrictMonoOn f (Set.Ici x) :=
  fun _ ha _ _ ↦ Nat.rel_of_forall_rel_succ_of_le_of_lt (· < ·) h ha

-- upstream
theorem strictMonoOn_Ioi_nat_of_lt_succ {α : Type*} [Preorder α] {f : ℕ → α} {x : ℕ}
    (h : ∀ n, x < n → f n < f (n + 1)) :
    StrictMonoOn f (Set.Ioi x) :=
  strictMonoOn_Ici_nat_of_lt_succ (x := x + 1) h

lemma kevinsFunction_strictMono_aux :
    StrictMonoOn (fun n : ℕ ↦ log ↑n - (↑n)⁻¹ * log n !) (Set.Ioi 0) :=
  strictMonoOn_Ioi_nat_of_lt_succ fun n hn ↦ by
    refine lt_of_mul_lt_mul_left (a := n * (n + 1 : ℝ)) ?_ (by positivity)
    calc
      _ = (n * (n + 1)) * log n - (n + 1) * log n ! := by field_simp; ring
      _ < n * (n + 1) * log (n + 1) - n * (log (n + 1) + log n !) := by
          linear_combination kevinsFunction_strictMono_aux2 n hn.ne'
      _ = n * (n + 1) * (log (n + 1) - (n + 1 : ℝ)⁻¹ * (log (n + 1) + log n !)) := by
          field_simp; ring
      _ = n * (n + 1) * (log (n + 1 : ℕ) - (↑(n + 1) : ℝ)⁻¹ * log (n + 1)!) := by
          rw [Nat.factorial_succ, Nat.cast_mul, log_mul (by positivity) (by positivity),
            Nat.cast_add_one]

noncomputable def kevinsFunction (n : ℕ) : ℝ :=
  (π / 4) * (n ^ 2 / (n ! : ℝ) ^ (2 / n : ℝ))

lemma kevinsFunction_strictMono :
    StrictMono kevinsFunction := by
  refine .const_mul (StrictMonoOn.Iic_union_Ici (a := 1) ?_ ?_) (by positivity)
  next =>
    have : Set.Iic 1 = {0, 1} := by simp [Set.ext_iff]; omega
    aesop (add simp StrictMonoOn)
  refine ((exp_strictMono.comp (strictMono_mul_left_of_pos zero_lt_two)).comp_strictMonoOn
    kevinsFunction_strictMono_aux).congr fun n (hn : 0 < n) ↦ ?_
  calc
    _ = rexp (2 * log n) / rexp (2 * ((n : ℝ)⁻¹ * log n !)) := by simp [mul_sub, exp_sub]
    _ = rexp (log n * 2) / rexp ((log n !) * (2 / n)) := by ring_nf
    _ = (n ^ 2 / n ! ^ (2 / n : ℝ)) := by simp (disch := positivity) [← rpow_def_of_pos]

lemma kevinsFunction_four : kevinsFunction 4 < 2.75 := by
  have h₁ : kevinsFunction 4 < 2.75 := by calc
    _ = π / 4 * (4 ^ 2 / 4! ^ (2 / 4 : ℝ)) := rfl
    _ < π / 4 * (4 ^ 2 / 4.8) := by
        gcongr
        rw [div_eq_mul_inv, rpow_mul, lt_rpow_inv_iff_of_pos]
        all_goals norm_num
    _ < 2.75 := by linarith [pi_lt_d4]
  exact h₁

lemma kevinsFunction_five : 2.75 < kevinsFunction 5 := by
  have h₁ : 2.75 < kevinsFunction 5 := by calc
    _ = π / 4 * (5 ^ 2 / 5! ^ (2 / 5 : ℝ)) := rfl
    _ > π / 4 * (5 ^ 2 / 7) := by
        gcongr
        rw [div_eq_mul_inv, rpow_mul, rpow_inv_lt_iff_of_pos]
        all_goals norm_num
    _ > 2.75 := by linarith [pi_gt_d4]
  exact h₁

lemma kevinsFunction_thirteen : kevinsFunction 13 < 2 ^ (2 / 3 : ℝ) * 3 ^ (7 / 8 : ℝ) := by
  have h₁ : kevinsFunction 13 < 4.15 := by calc
    _ = π / 4 * (13 ^ 2 / 13! ^ (2 / 13 : ℝ)) := rfl
    _ < π / 4 * (13 ^ 2 / 32) := by
        gcongr
        rw [div_eq_mul_inv, rpow_mul, lt_rpow_inv_iff_of_pos]
        all_goals norm_num
    _ < 4.15 := by linarith [pi_lt_d4]
  have h₂ : (4.15 : ℝ) < 2 ^ (2 / 3 : ℝ) * 3 ^ (7 / 8 : ℝ) := by
    rw [← rpow_lt_rpow_iff (z := 24), mul_rpow, ← rpow_mul, ← rpow_mul]
    all_goals first | positivity | norm_num
  exact h₁.trans h₂

lemma kevinsFunction_fourteen : 2 ^ (2 / 3 : ℝ) * 3 ^ (7 / 8 : ℝ) < kevinsFunction 14 := by
  have h₁ : 4.16 < kevinsFunction 14 := by calc
    _ = π / 4 * (14 ^ 2 / 14! ^ (2 / 14 : ℝ)) := rfl
    _ > π / 4 * (14 ^ 2 / 37) := by
        gcongr
        rw [div_eq_mul_inv, rpow_mul, rpow_inv_lt_iff_of_pos]
        all_goals norm_num
    _ > 4.16 := by linarith [pi_gt_d4]
  have h₂ : 2 ^ (2 / 3 : ℝ) * 3 ^ (7 / 8 : ℝ) < (4.16 : ℝ) := by
    rw [← rpow_lt_rpow_iff (z := 24), mul_rpow, ← rpow_mul, ← rpow_mul]
    all_goals first | positivity | norm_num
  exact h₂.trans h₁

theorem kevin_strong {n : ℕ} :
    (π / 4) * (n ^ 2 / (n !) ^ (2 / n : ℝ)) < 2 ^ (2 / 3 : ℝ) * 3 ^ (7 / 8 : ℝ) ↔ n < 14 := by
  change kevinsFunction n < 2 ^ (2 / 3 : ℝ) * 3 ^ (7 / 8 : ℝ) ↔ _
  refine ⟨fun h ↦ ?mp, fun h ↦ ?mpr⟩
  case mp => exact kevinsFunction_strictMono.lt_iff_lt.mp (h.trans kevinsFunction_fourteen)
  case mpr =>
    replace h : n ≤ 13 := by omega
    refine (kevinsFunction_strictMono.le_iff_le.mpr h).trans_lt kevinsFunction_thirteen

theorem kevin_strong2 {n : ℕ} :
    (π / 4) * (n ^ 2 / (n !) ^ (2 / n : ℝ)) < 2.75 ↔ n < 5 := by
  change kevinsFunction n < 2.75 ↔ _
  refine ⟨fun h ↦ ?mp, fun h ↦ ?mpr⟩
  case mp => exact kevinsFunction_strictMono.lt_iff_lt.mp (h.trans kevinsFunction_five)
  case mpr =>
    replace h : n ≤ 4 := by omega
    refine (kevinsFunction_strictMono.le_iff_le.mpr h).trans_lt kevinsFunction_four

theorem kevin {n : ℕ}
    (h : (π / 4) * (n ^ 2 / (n !) ^ (2 / n : ℝ)) < 2 ^ (2 / 3 : ℝ) * 3 ^ (7 / 8 : ℝ)) : n ≤ 14 :=
  (kevin_strong.mp h).le

theorem kevin2 {n : ℕ}
    (h : (π / 4) * (n ^ 2 / (n !) ^ (2 / n : ℝ)) < 2.75) : n ≤ 5 :=
  (kevin_strong2.mp h).le
