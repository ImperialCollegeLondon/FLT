/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.FDRep.Character.Basic
public import FLT.Slop.BrauerInduction.Background.ClassFun.Maps

@[expose] public section

/-!
# Basic character identities for finite-dimensional representations

This file defines the character of a finite-dimensional representation as a
class function and proves its basic identities: evaluation, invariance under
isomorphism, and compatibility with standard constructions such as sums, tensor
products, duals, internal Homs, biproducts, and restriction.
-/

universe u v

namespace ClassFun

open CategoryTheory

section character_def

variable {k : Type u} {G : Type v}
variable [Field k] [Group G]

/--
The character of a finite-dimensional representation, bundled as a class function.
-/
noncomputable def character (V : FDRep k G) : ClassFun k G where
  toFun := V.character
  map_conj := by
    intro x y h
    exact FDRep.char_eq_of_isConj V h

@[simp]
theorem char_apply (V : FDRep k G) (g : G) :
    ClassFun.character V g = V.character g :=
  rfl

end character_def

variable {k : Type u} {G : Type v} [Field k] [Group G]

/--
Character value on a product is unchanged when the two factors are swapped:
`χ(hg) = χ(gh)`.
-/
theorem char_mul_comm (V : FDRep k G) (g : G) (h : G) :
    ClassFun.character V (h * g) = ClassFun.character V (g * h) :=
      Representation.char_mul_comm V.ρ g h

@[simp]
lemma char_one (V : FDRep k G) :
    ClassFun.character V 1 = Module.finrank k V := by
  simp only [character, coe_mk, FDRep.char_one]

/--
Isomorphic representations have equal characters.
-/
lemma char_eq_of_iso
    {V W : FDRep k G} (e : V ≅ W) :
    ClassFun.character V = ClassFun.character W := by
  ext g
  exact congrFun (FDRep.char_eq_of_iso e) g

/--
The trivial representation has constant character `1`.
-/
@[simp]
lemma char_trivial
    (k : Type u) (G : Type v)
    [Field k] [Group G] :
    ClassFun.character (FDRep.trivial k G) = (1 : ClassFun k G) := by
  ext g
  simp only [character, FDRep.char_trivial, coe_mk, Pi.one_apply, one_apply]

/--
The character of a binary product is the sum of the characters.
-/
@[simp]
lemma char_prod (V W : FDRep k G) :
    ClassFun.character (V.prod W) = ClassFun.character V + ClassFun.character W := by
  simp only [character, FDRep.char_prod]
  rfl
/--
The character of a tensor product is the product of the characters.
-/
@[simp]
theorem char_tensor
    (V W : FDRep k G) :
    ClassFun.character (FDRep.tensor V W)
      =
    ClassFun.character V * ClassFun.character W := by
  ext g
  exact congrFun (FDRep.char_tensor V W) g

/--
The character of the dual representation is the involution of the character.
-/
@[simp]
lemma char_dual (V : FDRep k G) :
    ClassFun.character (V.dual) = ClassFun.involution (ClassFun.character V) := by
  ext g
  change V.dual.character g = V.character g⁻¹
  exact FDRep.char_dual V g

/--
The character of the internal Hom representation is `χ_V(g⁻¹) * χ_W(g)`.
-/
@[simp]
lemma char_linHom (V W : FDRep k G) (g : G) :
    ClassFun.character (FDRep.linHom V W) g =
      V.character g⁻¹ * W.character g  := by
  simp only [character, coe_mk, FDRep.char_linHom_apply]

/--
The character of a finite biproduct is the sum of the characters.
-/
@[simp]
lemma char_biproduct
    {ι : Type} [Fintype ι]
    (V : ι → FDRep k G) :
    ClassFun.character (Limits.biproduct V)
      =
    ∑ i, ClassFun.character (V i) := by
  ext g
  change (Limits.biproduct V).character g =
    (∑ i, ClassFun.character (V i)) g
  rw [FDRep.char_biproduct]
  calc
    (∑ i, (V i).character) g
        = ∑ i, (V i).character g := by
            simp
    _   = ∑ i, ClassFun.character (V i) g := by
            rfl
    _   = (∑ i, ClassFun.character (V i)) g := by
            exact Eq.symm (sum_apply (fun i ↦ character (V i)) g)

section res

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/--
Restricting the character of a representation agrees with the character of
the restricted representation.
-/
@[simp] theorem res_ofChar
    {H : Subgroup G} (V : FDRep k G) :
    ClassFun.res (G := G) (k := k) H (ClassFun.character V)
      =
    ClassFun.character (FDRep.res (k := k) (G := G) V H) := by
  ext h
  rfl

end res

end ClassFun
