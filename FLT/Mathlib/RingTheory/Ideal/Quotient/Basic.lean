import Mathlib.RingTheory.Ideal.Quotient.Basic

variable {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]

theorem Ideal.Quotient.out_sub (x : R) : (Ideal.Quotient.mk I x).out - x ∈ I := by
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
