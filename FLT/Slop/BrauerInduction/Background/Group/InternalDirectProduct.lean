/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.Group.Basic

/-!
If two subgroups form an internal direct product, then multiplication gives a
multiplicative equivalence from their product to the ambient group.
-/

@[expose] public section

namespace Slop
open Slop
open _root_.Subgroup

variable {G} [Group G]
variable {H : Type*} [Group H]

namespace Subgroup

/--
If `C, P ≤ H` commute elementwise, intersect trivially, and every `h ∈ H` decomposes
as `c * p` with `c ∈ C`, `p ∈ P`, then `(C × P) ≃* H`.
This is the standard “internal direct product gives product” equivalence.
-/
noncomputable def mulEquivProdOfInternalDirect
    (C P H : Subgroup G)
    (C_le : C ≤ H) (P_le : P ≤ H)
    (comm : ∀ {c p : G}, c ∈ C → p ∈ P → Commute c p)
    (disjoint : C ⊓ P = ⊥)
    (decompose : ∀ {h : G}, h ∈ H → ∃ c ∈ C, ∃ p ∈ P, c * p = h)
  : (C × P) ≃* H :=
by
  let φ : (C × P) →* H :=
  { toFun := fun cp =>
      ⟨(cp.1 : G) * (cp.2 : G),
       H.mul_mem (C_le cp.1.property) (P_le cp.2.property)⟩
    map_one' := by ext; simp
    map_mul' := by
      rintro ⟨c₁, p₁⟩ ⟨c₂, p₂⟩
      have swap : (↑c₂ : G) * (↑p₁ * ↑p₂) = (↑p₁ : G) * (↑c₂ * ↑p₂) := by
        rw [← mul_assoc, comm c₂.property p₁.property, mul_assoc]
      simp[mul_assoc, swap]
    }
  -- Surjectivity from the `decompose` hypothesis
  have hsurj : Function.Surjective φ := by
    intro hH
    rcases decompose hH.property with ⟨c, cC, p, pP, hcp⟩
    refine ⟨⟨⟨c, cC⟩, ⟨p, pP⟩⟩, ?_⟩
    exact SetLike.coe_eq_coe.mp hcp
 -- Injectivity from trivial intersection C ⊓ P = ⊥
  have hinj : Function.Injective φ := by
    rintro ⟨c1, p1⟩ ⟨c2, p2⟩ h
    have hG : (c1 : G) * (p1 : G) = (c2 : G) * (p2 : G) :=
      congrArg Subtype.val h
    have hrel : (c1 : G)⁻¹ * (c2 : G) = (p1 : G) * (p2 : G)⁻¹ := by
      have := congrArg (fun g => (c1 : G)⁻¹ * g * (p2 : G)⁻¹) hG
      simpa [mul_assoc] using this.symm
    have hc_mem : (c1 : G)⁻¹ * (c2 : G) ∈ C :=
      C.mul_mem (C.inv_mem c1.property) c2.property
    have hp_mem : (p1 : G) * (p2 : G)⁻¹ ∈ P :=
      P.mul_mem p1.property (P.inv_mem p2.property)
    have hC1 : (c1 : G)⁻¹ * (c2 : G) = 1 := by
      haveI hinter: (c1 : G)⁻¹ * (c2 : G) ∈ C ⊓ P := by
        simp only [mem_inf, hc_mem, true_and]
        rw [hrel]
        exact mem_carrier.mp hp_mem
      rw[disjoint] at hinter
      apply Subgroup.mem_bot.mp hinter
  -- Recover c1 = c2 (as elements of C)
    have hc_eq : c1 = c2 := Subtype.ext (by
      have := congrArg (fun g => (c1 : G) * g) hC1
      simpa [mul_one, mul_assoc] using this.symm)
  -- Recover p1 = p2 (as elements of P)
    have hp_eq : p1 = p2 := Subtype.ext (by
      have hP1 : (p1 : G) * (p2 : G)⁻¹ = 1 := by simpa [hrel] using hC1
      have := congrArg (fun g => g * (p2 : G)) hP1
      simpa [one_mul, mul_assoc] using this)
    simp [hc_eq, hp_eq]
  exact MulEquiv.ofBijective φ ⟨hinj, hsurj⟩

end Subgroup

end Slop
