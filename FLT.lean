import Mathlib.Tactic
import FLT.Basic.Reductions

-- assume the mathlib formalisation of Fermat's Last Theorem
theorem flt_proof : FermatLastTheorem := sorry

-- now check it implies the theorem for positive naturals
/-- Fermat's Last Theorem for positive naturals. -/
theorem PNat.pow_add_pow_ne_pow
    (x y z : ℕ+)
    (n : ℕ) (hn : n > 2) :
    x^n + y^n ≠ z^n := by
  apply PNat.pow_add_pow_ne_pow_of_FermatLastTheorem
  · exact flt_proof
  · linarith
