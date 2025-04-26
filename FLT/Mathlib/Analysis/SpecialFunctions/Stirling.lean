/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/

import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Lemmas for Stirling's approximation

This file adds some _global_ bounds on the factorial function and the Stirling sequence, in contrast
to the existing ones which are either not explicit in the bounds, or are explicit but only hold
for large `n`.
-/
namespace Stirling

open Filter Real
open scoped Nat

/--
The Stirling sequence is bounded below by `√π`, for all positive naturals. Note that this bound
holds for all `n > 0`, rather than for sufficiently large `n`: it is effective.
-/
theorem sqrt_pi_le_stirlingSeq {n : ℕ} (hn : n ≠ 0) : √π ≤ stirlingSeq n :=
  match n, hn with
  | n + 1, _ =>
    stirlingSeq'_antitone.le_of_tendsto (b := n) <|
      tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1)

/--
Stirling's approximation gives a lower bound for `n!` for all `n`.
The left hand side is formulated to mimic the usual informal description of the approxmation.
See also `factorial_isEquivalent_stirling` which says these are asymptotically equivalent. That
statement gives an upper bound also, but requires sufficiently large `n`. In contrast, this one is
only a lower bound, but holds for all `n`.
Sharper bounds due to Robbins are available, but are not yet formalised.
-/
theorem le_factorial_stirling (n : ℕ) : √(2 * π * n) * (n / exp 1) ^ n ≤ n ! := by
  obtain rfl | hn := eq_or_ne n 0
  case inl => simp
  calc
    _ = (√(π * (2 * n)) * (n / exp 1) ^ n) := by congr! 2; ring
    _ = (√π * √(2 * n) * (n / exp 1) ^ n) := by congr! 1; simp [sqrt_mul']
    _ = √π * (√(2 * n) * (n / exp 1) ^ n) := by ring
  rw [← le_div_iff₀ (by positivity)]
  exact sqrt_pi_le_stirlingSeq hn

/--
Stirling's approximation gives a lower bound for `log n!` for all positive `n`.
The left hand side is formulated in decreasing order in `n`: the higher order terms are first.
This is a consequence of `le_factorial_stirling`, but is stated separately since the logarithmic
version is sometimes more practical, and having this version eases algebraic calculations for
applications.
Sharper bounds due to Robbins are available, but are not yet formalised. These would add
lower order terms (beginning with `(12 * n)⁻¹`) to the left hand side.
-/
theorem le_log_factorial_stirling (n : ℕ) (hn : n ≠ 0) :
    n * log n - n + log n / 2 + log (2 * π) / 2 ≤ log n ! := by
  calc
    _ ≥ log (√(2 * π * n) * (n / rexp 1) ^ n) :=
        log_le_log (by positivity) (le_factorial_stirling n)
    _ ≥ (log (2 * π) + log ↑n) / 2 + ↑n * (log ↑n - 1) := by
        rw [log_mul, log_sqrt, log_mul, log_pow, log_div, log_exp]
        all_goals positivity
    _ = _ := by ring

end Stirling
