import FLT.PGL2.FiniteSubgroups.TameClassification
import FLT.PGL2.FiniteSubgroups.WildClassification

open scoped Classical

namespace Dickson

variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]

theorem dickson_classification (G : Subgroup (PGL p)) [Finite G] :
    (IsCyclic G) ∨
    (∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n)) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 4))) ∨
    (Nonempty (G ≃* Equiv.Perm (Fin 4))) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 5))) ∨
    (∃ (m t : ℕ) (_ : m ≥ 1) (_ : Nat.Coprime t p) (_ : t ∣ p ^ m - 1)
      (φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p))),
      Nonempty (G ≃* (Multiplicative (Fin m → ZMod p)) ⋊[φ] Multiplicative (ZMod t))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p m))) ∨
    (∃ m : ℕ, m ≥ 1 ∧
      Nonempty (G ≃* (GL (Fin 2) (GaloisField p m) ⧸
        Subgroup.center (GL (Fin 2) (GaloisField p m))))) := by
  by_cases hG_nontrivial : Nontrivial G
  · by_cases h_div : p ∣ Nat.card G
    · rcases classification_wild p G h_div with h1 | h2 | h3 | ⟨_, h4⟩
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h1
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h2
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr h3
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h4
    · haveI : Fintype G := Fintype.ofFinite G
      rcases classification_tame p G h_div hG_nontrivial with h1 | h2 | h3 | h4 | h5
      · exact Or.inl h1
      · exact Or.inr <| Or.inl h2
      · exact Or.inr <| Or.inr <| Or.inl h3
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl h4
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h5
  · haveI : Subsingleton G := not_nontrivial_iff_subsingleton.mp hG_nontrivial
    exact Or.inl ⟨⟨1, fun x ↦ by rw [Subsingleton.elim x 1]; exact Subgroup.mem_zpowers 1⟩⟩

end Dickson
