import Mathlib.Algebra.Quaternion
import Mathlib.RingTheory.SimpleModule
variable (K : Type) [Field K]
variable (A : Type) [Ring A] [IsSimpleOrder (RingCon A)] [Algebra K A] 
  (h : FiniteDimensional K A)

-- TODO : define 
variable {A} in
abbrev f : (RingCon A) → (RingCon (Aᵐᵒᵖ)) := sorry


lemma op_simple : IsSimpleOrder (RingCon (Aᵐᵒᵖ)) := by 
  -- have eq: Function.Bijective (f A) := sorry should be order isomorphism???
  sorry

lemma op_iso_end : Nonempty (Aᵐᵒᵖ ≃+* (Module.End A A)) := by
  sorry

lemma matrixop_iso_op (n : ℕ) (D :Type) (h : DivisionRing D) : Nonempty 
  ((Matrix (Fin n) (Fin n) D) ≃+* (Matrix (Fin n) (Fin n) D)ᵐᵒᵖ) := by
  sorry

theorem Wedderburn_Artin : ∃(n : ℕ) (S : Type) (h : DivisionRing S), 
  Nonempty (A ≃+* (Matrix (Fin n) (Fin n) (S))) := by
  sorry
