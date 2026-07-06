/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.FDRep.CoindBasis
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.FDRep.Induced
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.ClassFun.Induced
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.FDRep.Character.Basic
public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.ClassFun.Character.Basic

@[expose] public section

/-!

# Characters of induced and coinduced representations

This file relates representation-theoretic induction and coinduction to
induction of class functions.

The main representation-theoretic calculation computes the character of a
coinduced representation as a sum over right cosets, using the explicit basis
from `FDRep.CoindBasis`. Together with the induction/coinduction isomorphism,
this proves that induction of the character of a representation agrees with
the character of the induced representation.

-/

universe u v

namespace FDRep

open CategoryTheory

section Coinduced

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

open Classical in
/--
Character formula for a coinduced representation, written as a sum over right
cosets.

The summand attached to a right coset `q` is evaluated at the chosen
representative `q.out`; it is zero unless `q.out * g * q.out⁻¹` lies in the
subgroup.
-/
lemma char_coind_over_right_cosets
    [Fintype G] (I : Subgroup G) (σ : FDRep k I) (g : G) :
    (FDRep.coind I σ).character g =
    ∑ q : Quotient (QuotientGroup.rightRel I),
      if h : q.out * g * q.out⁻¹ ∈ I
      then σ.character ⟨q.out * g * q.out⁻¹, h⟩
      else 0 := by
  let bV : Module.Basis (Fin (Module.finrank k σ)) k σ :=
    Module.finBasis k σ
  let B := FDRep.coindBasis I σ bV
  rw [FDRep.character, LinearMap.trace_eq_matrix_trace k B, Matrix.trace]
  change (∑ p : Quotient (QuotientGroup.rightRel I) × Fin (Module.finrank k σ),
      (LinearMap.toMatrix B B ((FDRep.coind I σ).ρ g)) p p) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hmem : q.out * g * q.out⁻¹ ∈ I
  · rw [dif_pos hmem]
    rw [FDRep.character, LinearMap.trace_eq_matrix_trace k bV, Matrix.trace]
    apply Finset.sum_congr rfl
    intro i _
    rw [LinearMap.toMatrix_apply]
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    have hB : B (q, i) = FDRep.coindBasisVector I σ bV q i := by
      exact FDRep.coindBasis_apply I σ bV q i
    rw [hB]
    change bV.repr ((FDRep.coindBasisVector I σ bV q i).1 (q.out * g)) i =
      bV.repr (σ.ρ ⟨q.out * g * q.out⁻¹, hmem⟩ (bV i)) i
    have hq : Quotient.mk (QuotientGroup.rightRel I) (q.out * g) = q := by
      apply Eq.trans _ (Quotient.out_eq q)
      apply Quotient.sound
      change QuotientGroup.rightRel I (q.out * g) q.out
      rw [QuotientGroup.rightRel_apply]
      have h_inv := I.inv_mem hmem
      simpa [mul_assoc] using h_inv
    dsimp [FDRep.coindBasisVector]
    rw [dif_pos hq]
  · rw [dif_neg hmem]
    apply Finset.sum_eq_zero
    intro i _
    rw [LinearMap.toMatrix_apply]
    have hB : B (q, i) = FDRep.coindBasisVector I σ bV q i := by
      exact FDRep.coindBasis_apply I σ bV q i
    rw [hB]
    change bV.repr ((FDRep.coindBasisVector I σ bV q i).1 (q.out * g)) i = 0
    have hq_not : Quotient.mk (QuotientGroup.rightRel I) (q.out * g) ≠ q := by
      intro hq
      apply hmem
      have h_rel := Quotient.exact (hq.trans (Quotient.out_eq q).symm)
      change QuotientGroup.rightRel I (q.out * g) q.out at h_rel
      rw [QuotientGroup.rightRel_apply] at h_rel
      have h_inv := I.inv_mem h_rel
      simpa [mul_assoc] using h_inv
    dsimp [FDRep.coindBasisVector]
    rw [dif_neg hq_not]
    have hzero : bV.repr 0 = 0 := map_zero bV.repr
    exact congrArg (fun f => f i) hzero

end Coinduced
end FDRep


namespace FDRep

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

open Classical in
/--
Character formula for an induced representation, written using conjugates
`x * g * x⁻¹`.
-/
lemma char_ind_as_avg_mul_inv
    [Fintype G]
    (I : Subgroup G)
    [CharZero k]
    (σ : FDRep k I)
    (g : G) :
    (FDRep.ind I σ).character g =
      (Nat.card I : k)⁻¹ *
        ∑ x : G,
          if h : x * g * x⁻¹ ∈ I then
            σ.character ⟨x * g * x⁻¹, h⟩
          else
            0 := by
  have hχ :
      (FDRep.ind I σ).character g =
        (FDRep.coind I σ).character g :=
    congrFun (FDRep.char_eq_of_iso (FDRep.indIsoCoind I σ)) g
  calc
    (FDRep.ind I σ).character g
        = (FDRep.coind I σ).character g := hχ
    _ =
        ∑ q : Quotient (QuotientGroup.rightRel I),
          if h : q.out * g * q.out⁻¹ ∈ I then
            σ.character ⟨q.out * g * q.out⁻¹, h⟩
          else
            0 := by
          exact FDRep.char_coind_over_right_cosets I σ g
    _ =
        ClassFun.ind I (ClassFun.character σ) g := by
          rw [ClassFun.ind_apply_rightCosets]
          simp only [ClassFun.char_apply]
    _ =
      (Nat.card I : k)⁻¹ *
        ∑ x : G,
          if h : x * g * x⁻¹ ∈ I then
            σ.character ⟨x * g * x⁻¹, h⟩
          else
            0 := by
          change
            ClassFun.ind I (ClassFun.character σ) g =
              (Nat.card I : k)⁻¹ *
                ∑ x : G,
                  if h : x * g * x⁻¹ ∈ I then
                    (ClassFun.character σ).toFun
                      ⟨x * g * x⁻¹, h⟩
                  else
                    0
          exact ClassFun.ind_apply_eq_inv_mul_sum_mul_inv
            I (ClassFun.character σ) g



open Classical in
/--
Character formula for a coinduced representation over a characteristic-zero
field, written as an average over the ambient group.
-/
lemma char_coind
    [Fintype G] (I : Subgroup G) [CharZero k]
    (σ : FDRep k I) (g : G) :
    (FDRep.coind I σ).character g =
      (Nat.card I : k)⁻¹ *
        ∑ x : G,
          if h : x * g * x⁻¹ ∈ I then
            σ.character ⟨x * g * x⁻¹, h⟩
          else
            0 := by
  calc
    (FDRep.coind I σ).character g
        =
      (FDRep.ind I σ).character g := by
        exact
          (congrFun
            (FDRep.char_eq_of_iso (FDRep.indIsoCoind I σ))
            g).symm
    _ =
      (Nat.card I : k)⁻¹ *
        ∑ x : G,
          if h : x * g * x⁻¹ ∈ I then
            σ.character ⟨x * g * x⁻¹, h⟩
          else
            0 :=
      FDRep.char_ind_as_avg_mul_inv I σ g


open Classical in
/--
The usual induced-character formula.

The value of the character of `Ind_H^G V` at `g` is the average, over `x : G`,
of the character of `V` at `x⁻¹ * g * x`, with the summand interpreted as zero
when this conjugate does not lie in `H`.
-/
lemma char_ind_apply
    [Fintype G] [CharZero k]
    (H : Subgroup G)
    (V : FDRep k H)
    (g : G) :
    (FDRep.ind H V).character g =
      (Nat.card H : k)⁻¹ *
        ∑ x : G,
          if hx : x⁻¹ * g * x ∈ H then
            V.character ⟨x⁻¹ * g * x, hx⟩
          else
            0 := by
  rw [FDRep.char_ind_as_avg_mul_inv H V g]
  congr 1
  refine
    Fintype.sum_equiv
      (Equiv.inv G)
      (fun x : G =>
        if h : x * g * x⁻¹ ∈ H then
          V.character ⟨x * g * x⁻¹, h⟩
        else
          0)
      (fun x : G =>
        if hx : x⁻¹ * g * x ∈ H then
          V.character ⟨x⁻¹ * g * x, hx⟩
        else
          0)
      ?_
  intro x
  simp only [Equiv.inv_apply, inv_inv]

end FDRep
