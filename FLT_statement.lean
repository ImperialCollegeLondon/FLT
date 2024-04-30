import Mathlib.Tactic
import FLT.Basic.Reductions

/-!

# Fermat's Last Theorem

There are many ways of stating Fermat's Last Theorem.
In this file, we give the traditional statement using
the positive integers `ℕ+`, and deduce it from
a proof of Mathlib's version `FermatLastTheorem`
of the statement (which is a statement about the
nonnegative integers `ℕ`.)

-/

/-- Fermat's Last Theorem for positive naturals. -/
theorem PNat.pow_add_pow_ne_pow
    (x y z : ℕ+)
    (n : ℕ) (hn : n > 2) :
    x^n + y^n ≠ z^n :=
  PNat.pow_add_pow_ne_pow_of_FermatLastTheorem FLT.Wiles_Taylor_Wiles x y z n hn

