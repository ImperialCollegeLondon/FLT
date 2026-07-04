/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Data.Nat.Factors
public import Mathlib.NumberTheory.FLT.Four
public import Mathlib.NumberTheory.FLT.Three

/-!

 # The reduction of FLT to the p>=5 prime case.

-/

@[expose] public section

namespace Nat

theorem three_dvd_or_four_dvd_or_prime_dvd {n : ℕ} (hn : 3 ≤ n) :
    3 ∣ n ∨ 4 ∣ n ∨ ∃ p, (p.Prime ∧ 5 ≤ p ∧ p ∣ n) := by
  -- a result in Lean's library says that either 4 divides n or some odd prime divides n
  obtain h4 | ⟨p, hp, hdvd, hodd⟩ := Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn
  · -- if 4 divides n we're done
    grind
  · -- in the odd prime case, if the prime is 3 we're done
    rcases eq_or_ne p 3 with rfl | hp3; · grind
    -- and if it isn't 3 then it's at least 5
    refine Or.inr (Or.inr ⟨p, hp, ?_, hdvd⟩)
    -- because it's odd, and 1 isn't prime.
    grind [not_prime_one]

end Nat

/-- If Fermat's Last Theorem is true for primes `p ≥ 5`, then FLT is true. -/
lemma FermatLastTheorem.of_p_ge_5 (H : ∀ p ≥ 5, p.Prime → FermatLastTheoremFor p) :
    FermatLastTheorem := by
  -- let n ≥ 3 and let's prove a^n + b^n ≠ c^n for positive
  -- integers a, b, c.
  intro n hn
  -- we split into three cases 3|n, 4|n and p|n with p>=5 prime
  obtain h3 | h4 | ⟨p, hpp, hp5, hpn⟩ := Nat.three_dvd_or_four_dvd_or_prime_dvd hn
  · -- Case 1: if 3|n then FLT for n follows from FLT for n=3
    apply FermatLastTheoremFor.mono h3
    -- but FLT for n=3 is a theorem of Euler
    exact fermatLastTheoremThree
  · -- Case 2: if 4|n then FLT for n follows from FLT for n=4
    apply FermatLastTheoremFor.mono h4
    -- but FLT for n=4 is a theorem of Fermat.
    exact fermatLastTheoremFour
  · -- Case 3: Finally if p>=5 divides n then FLT for n follows from FLT for p
    apply FermatLastTheoremFor.mono hpn
    -- and this is our assumption
    exact H _ hp5 hpp

/-- Fermat's Last Theorem as stated in mathlib (a statement `FermatLastTheorem` about naturals)
implies Fermat's Last Theorem stated in terms of positive integers. -/
theorem PNat.pow_add_pow_ne_pow_of_FermatLastTheorem :
    FermatLastTheorem → ∀ (a b c : ℕ+) (n : ℕ) (_ : n > 2),
    a ^ n + b ^ n ≠ c ^ n := by
  intro h₁ a b c n h₂
  specialize h₁ n h₂ a b c (by simp) (by simp) (by simp)
  assumption_mod_cast
