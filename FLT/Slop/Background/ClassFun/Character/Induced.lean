/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.Background.FDRep.CoindBasis
public import FLT.Slop.Background.FDRep.Character.Induced
public import FLT.Slop.Background.ClassFun.Induced
public import FLT.Slop.Background.ClassFun.Character.Basic

@[expose] public section

universe u

namespace ClassFun

section InducedCharacter

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Fintype G]

/--
Class-function induction of the character of a representation is the
character of the induced representation.
-/
@[simp]
theorem ind_ofChar
    (H : Subgroup G)
    (V : FDRep k H) :
    ClassFun.ind H (ClassFun.character V) =
      ClassFun.character (FDRep.ind H V) := by
  ext g
  rw [ClassFun.ind_apply_rightCosets]
  simp only [ClassFun.char_apply]
  have hχ :
      (FDRep.ind H V).character g =
        (FDRep.coind H V).character g :=
    congrFun (FDRep.char_eq_of_iso (FDRep.indIsoCoind H V)) g
  rw [hχ, FDRep.char_coind_over_right_cosets]

/--
The character of an induced representation is the induced class function
of the original character.
-/
theorem char_ind
    (H : Subgroup G)
    (V : FDRep k H) :
    ClassFun.character (FDRep.ind H V) =
      ClassFun.ind H (ClassFun.character V) :=
  (ClassFun.ind_ofChar H V).symm

end InducedCharacter

end ClassFun
