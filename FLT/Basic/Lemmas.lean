/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Data.Nat.Factors
/-!

# A key lemma for reduction of FLT to the p>=5 prime case.

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
    rcases eq_or_ne p 3 with rfl | hp3; grind
    -- and if it isn't 3 then it's at least 5
    refine Or.inr (Or.inr ⟨p, hp, ?_, hdvd⟩)
    -- because it's odd, and 1 isn't prime.
    grind [not_prime_one]
