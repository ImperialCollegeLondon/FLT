import FLT -- import the project files

/-!

# Fermat's Last Theorem

There are many ways of stating Fermat's Last Theorem.
In this file, we give the traditional statement using
the positive integers `ℕ+`, and deduce it from
a proof of Mathlib's version `FermatLastTheorem`
of the statement (which is a statement about the
nonnegative integers `ℕ`.)

Note that many of the files imported by this file contain
"sorried" theorems, that is, theorems whose proofs
are not yet complete. So whilst the below looks
like a complete proof of Fermat's Last Theorem, it
currently relies on many incomplete proofs along the way,
and is likely to do so for several years.

-/

/-- Fermat's Last Theorem for positive naturals. -/
theorem PNat.pow_add_pow_ne_pow
    (x y z : ℕ+)
    (n : ℕ) (hn : n > 2) :
    x^n + y^n ≠ z^n :=
  PNat.pow_add_pow_ne_pow_of_FermatLastTheorem FLT.Wiles_Taylor_Wiles x y z n hn

#print axioms PNat.pow_add_pow_ne_pow
/-
'PNat.pow_add_pow_ne_pow' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/

-- The project will be complete when `sorryAx` is no longer
-- mentioned in the output of this last command.
