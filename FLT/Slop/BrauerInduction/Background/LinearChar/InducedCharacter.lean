/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.LinearChar.Induced
public import FLT.Slop.BrauerInduction.Background.ClassFun.Character.Induced

@[expose] public section

/-!
# Character formulas for induced linear characters

This file gives character formulas for `FDRep.indLin` and `FDRep.coindLin`.
The proofs are consequences of the generic character formula for induced
representations.
-/

universe u v

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

namespace FDRep

open BigOperators

open Classical in
/--
The character of an induced linear representation, written as an average
over conjugates `x * g * x⁻¹`.
-/
lemma indLin_character
    [Fintype G] [CharZero k]
    (H : Subgroup G) (ψ : H →* kˣ) (g : G) :
    (FDRep.indLin H ψ).character g =
      (Fintype.card H : k)⁻¹ * ∑ x : G,
        if h : x * g * x⁻¹ ∈ H then
          (ψ ⟨x * g * x⁻¹, h⟩ : k)
        else 0 := by
  change
    (FDRep.ind H (FDRep.ofLinearChar ψ)).character g
      =
    (Fintype.card H : k)⁻¹ * ∑ x : G,
      if h : x * g * x⁻¹ ∈ H then
        (ψ ⟨x * g * x⁻¹, h⟩ : k)
      else 0
  simpa only [FDRep.char_ofLinearChar, Nat.card_eq_fintype_card] using
    (FDRep.char_ind_as_avg_mul_inv
      (I := H)
      (σ := FDRep.ofLinearChar ψ)
      (g := g))

/--
Induced and coinduced linear representations have the same character.
-/
lemma char_indLin_eq_char_coindLin
    (H : Subgroup G) (ψ : H →* kˣ) :
    (FDRep.indLin H ψ).character =
      (FDRep.coindLin H ψ).character := by
  exact FDRep.char_eq_of_iso
    (FDRep.indLinCoindLinIso H ψ)

open Classical in
/--
The character of a coinduced linear representation, written using the same
average formula as for induction.
-/
lemma coindLin_character [Fintype G] [CharZero k]
    (H : Subgroup G) (ψ : H →* kˣ) (g : G) :
    (FDRep.coindLin H ψ).character g =
      (Fintype.card H : k)⁻¹ * ∑ x : G,
        if h : x * g * x⁻¹ ∈ H then
          (ψ ⟨x * g * x⁻¹, h⟩ : k)
        else 0 := by
  rw [← congrFun (FDRep.char_indLin_eq_char_coindLin H ψ) g]
  exact FDRep.indLin_character H ψ g

end FDRep

namespace ClassFun

/--
The character of an induced linear representation is the induced class function
of the corresponding linear character.
-/
lemma character_indLin
    {k : Type u} [Field k]
    {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) (ψ : H →* kˣ) :
    ClassFun.character (FDRep.indLin (G := G) H ψ) =
      ClassFun.ind (G := G) (k := k) H
        (ClassFun.character (FDRep.ofLinearChar ψ)) := by
  change
    ClassFun.character
      (FDRep.ind (G := G) H
        (FDRep.ofLinearChar ψ))
      =
    ClassFun.ind (G := G) H
      (ClassFun.character (FDRep.ofLinearChar ψ))
  exact ClassFun.char_ind (G := G) H (FDRep.ofLinearChar ψ)

end ClassFun
