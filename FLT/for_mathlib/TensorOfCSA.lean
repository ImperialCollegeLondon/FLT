import FLT.for_mathlib.IsCentralSimple

universe u v w
variable (K : Type u) [Field K]
variable (A B : Type v)[Ring A][Ring B][Algebra K A][Algebra K B]

open scoped TensorProduct
theorem tensor_CSA_is_CSA [Small.{v, u} K ](hA: IsCentralSimple K A) (hB: IsCentralSimple K B):
    IsCentralSimple K (A ⊗[K] B) where
   is_central := IsCentralSimple.TensorProduct.isCentral K A B hA.is_central hB.is_central
   is_simple := by haveI := hA.is_simple; exact IsCentralSimple.TensorProduct.simple K A B 

lemma CSA_op_is_CSA (hA: IsCentralSimple K A):
    IsCentralSimple K Aᵐᵒᵖ where
   is_central z hz:= by 
      let z': A := z.unop
      have hz' : ∀ (x : A), x * z' = z' * x := by 
         rw [Subalgebra.mem_center_iff] at hz
         intros x
         specialize hz (MulOpposite.op x)
         have z'_eq : MulOpposite.op z'= z := rfl
         rw [← z'_eq, ← MulOpposite.op_mul, ← MulOpposite.op_mul] at hz
         have : (MulOpposite.op (z' * x)).unop = (MulOpposite.op (x * z')).unop := by 
            exact congrArg MulOpposite.unop hz
         have : (MulOpposite.op (z' * x)).unop = z' * x := by 
            exact rfl
         simp_all only [MulOpposite.op_mul, MulOpposite.op_unop, MulOpposite.unop_mul,
         MulOpposite.unop_op, z']
      obtain ⟨k, hk⟩ := hA.is_central (show z' ∈ _ by
         simp only [Subalgebra.mem_center_iff] at hz ⊢
         exact fun b ↦ hz' b)
      use k
      exact MulOpposite.unop_inj.mp hk
   is_simple := by haveI := hA.is_simple; exact op_simple A

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


