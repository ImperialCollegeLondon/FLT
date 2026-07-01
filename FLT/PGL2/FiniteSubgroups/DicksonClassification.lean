/-
Copyright (c) 2026 Dokying Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dokying Yang
-/
module

public import FLT.PGL2.FiniteSubgroups.TameClassification
public import FLT.PGL2.FiniteSubgroups.WildClassification

/-!
# Dickson's Classification of Finite Subgroups of PGL₂

This file assembles the complete classification of finite subgroups
of `PGL(2, K)` over an algebraically closed field `K` of odd
characteristic `p`. The proof combines verbatim the tame case
(`classification_tame`) which handles subgroups of coprime order via
the class equation and cyclic partition analysis, along with the wild case
(`classification_wild`) which handles subgroups of order divisible by `p` via
Sylow geometry and field reconstruction.

## Main results

- `dickson_classification`: every finite subgroup of `PGL(2, K)` is
  isomorphic to a cyclic group, a dihedral group, `A₄`, `S₄`, `A₅`,
  a semidirect product of an elementary abelian `p`-group and a
  cyclic group, `PSL(2, F_q)`, or `PGL(2, F_q)`.
-/

@[expose] public section

namespace Dickson

variable (p : ℕ) [Fact (Nat.Prime p)] [h_odd : Fact (p > 2)]

open Classical in
/-- **Dickson's classification theorem.** Every finite subgroup of `PGL(2, K)`,
where `K` is an algebraically closed field of odd characteristic `p`, is
isomorphic to one of: a cyclic group, a dihedral group `D_n`, `A₄`, `S₄`,
`A₅`, a semidirect product `(Z/p)^m ⋊ Z/t`, `PSL(2, F_{p^m})`, or
`PGL(2, F_{p^m})`. -/
theorem dickson_classification (G : Subgroup (PGL p)) [Finite G] :
    (IsCyclic G) ∨
    (∃ n : ℕ, n ≥ 2 ∧ Nonempty (G ≃* DihedralGroup n)) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 4))) ∨
    (Nonempty (G ≃* Equiv.Perm (Fin 4))) ∨
    (Nonempty (G ≃* alternatingGroup (Fin 5))) ∨
    (∃ m t : ℕ, m ≥ 1 ∧ Nat.Coprime t p ∧ t ∣ p ^ m - 1 ∧
      ∃ φ : Multiplicative (ZMod t) →* MulAut (Multiplicative (Fin m → ZMod p)),
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
