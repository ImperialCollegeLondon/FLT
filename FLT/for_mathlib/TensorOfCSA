import FLT.for_mathlib.IsCentralSimple

variable (K : Type*) [Field K]
variable (A B : Type*)[Ring A][Ring B][Algebra K A][Algebra K B]

open scoped TensorProduct
theorem tensor_CSA_is_CSA (hA: IsCentralSimple K A) (hB: IsCentralSimple K B):
    IsCentralSimple K (A ⊗[K] B) where
   is_central := sorry
   is_simple := sorry

def tensor_self_op (hA: IsCentralSimple K A) [FiniteDimensional K A]
    (n : ℕ) (hn : n = FiniteDimensional.finrank K A):
    A ⊗[K] Aᵐᵒᵖ ≃ₐ[K] (Matrix (Fin n) (Fin n) K) := sorry

/-
## TODO:
  1. Define a Brauer equivalence relation on the set of All Central Simple
     K-Algebras, namely A ~ B if A ≃ₐ[K] Mₙ(D) and B ≃ₐ[K] Mₘ(D) for some
     m,n ∈ ℕ and D a division algebra over K.
  2. Prove the set of All Central Simple K-Algebras under this equivalence relation
     forms a group with mul := ⊗[K] and inv A := Aᵒᵖ.

-/


