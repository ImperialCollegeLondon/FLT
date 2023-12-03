import Mathlib.Data.PNat.Basic
import Mathlib.NumberTheory.FLT.Basic

/-!
In this file we show that Fermat's Last Theorem for positive integers,
as formulated in the main `FLT.lean` file, follows from the mathlib
formalisation of Fermat's Last Theorem.
-/

theorem PNat.pow_add_pow_ne_pow_of_FermatLastTheorem :
    FermatLastTheorem → ∀ (a b c : ℕ+) (n : ℕ) (_ : 3 ≤ n),
    a ^ n + b ^ n ≠ c ^ n := by
  intro h₁ a b c n h₂
  specialize h₁ n h₂ a b c (by simp) (by simp) (by simp)
  assumption_mod_cast
