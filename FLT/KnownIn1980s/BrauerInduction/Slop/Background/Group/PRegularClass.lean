/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.KnownIn1980s.BrauerInduction.Slop.Background.Group.PDecomposition

@[expose] public section

/-!
# `p`-regular conjugacy classes

This file defines the subtype of conjugacy classes consisting of `p`-regular
elements. It also provides a chosen representative for such a class and proves
that every `p`-regular element lies in a unique `p`-regular conjugacy class.
-/

universe u
variable {G : Type u} [Group G]
variable (p : ℕ)

namespace ConjClass

/--
A conjugacy class is `p`-regular if its chosen representative is `p`-regular.

This is independent of the chosen representative, since `p`-regularity is
invariant under conjugacy.
-/
def isPRegular (C : ConjClasses G) : Prop := IsPRegular p (C.out)

/--
The conjugacy class of an element is `p`-regular iff the element itself is
`p`-regular.
-/
@[simp] lemma mk_isPRegular (p : ℕ) (g : G) :
  ConjClass.isPRegular p ⟦g⟧ ↔ IsPRegular p g :=
by
  unfold ConjClass.isPRegular
  apply IsPRegular.iff_isConj
  have h := Quot.out_eq (⟦g⟧ : ConjClasses G)
  exact ConjClasses.mk_eq_mk_iff_isConj.mp h

end ConjClass

/-- The type of `p`-regular conjugacy classes of `G`. -/
def PRegularClass (G : Type u) [Group G] := { C : ConjClasses G // ConjClass.isPRegular p C }

namespace PRegularClass

/-- A chosen representative of a `p`-regular conjugacy class. -/
noncomputable def repr {p : ℕ} (C : PRegularClass p G) : G :=
  C.1.out

/-- The chosen representative of a `p`-regular conjugacy class is `p`-regular. -/
lemma repr_isPRegular {p : ℕ} (C : PRegularClass p G) :
    IsPRegular p (repr C) := by
  dsimp [repr, PRegularClass, ConjClass.isPRegular] at C
  exact C.2

@[ext] lemma ext {C₁ C₂ : PRegularClass p G} (h : C₁.val = C₂.val) : C₁ = C₂ :=
  Subtype.ext h

/--
Every `p`-regular element belongs to a unique `p`-regular conjugacy class.

The class is characterized by the condition that its chosen representative is
conjugate to the given element.
-/
lemma unique_of_isPRegular
  (g : G) (hg : IsPRegular p g) :
  ∃! C : PRegularClass p G, IsConj (repr C) g := by
  let C0 : PRegularClass p G :=
    ⟨ConjClasses.mk g, by
      simpa [ConjClasses.quotient_mk_eq_mk] using
        (ConjClass.mk_isPRegular p g).2 hg⟩
  refine ⟨C0, ?_, ?_⟩
  · have hm : ConjClasses.mk ((ConjClasses.mk g).out) = ConjClasses.mk g := by
      exact Quotient.out_eq (ConjClasses.mk g)
    simpa [C0, repr] using (ConjClasses.mk_eq_mk_iff_isConj).1 hm
  · intro C hC
    apply ext p (G := G)
    have hmk : ConjClasses.mk (repr C) = ConjClasses.mk g :=
      (ConjClasses.mk_eq_mk_iff_isConj).2 (by
        simpa using hC)
    have hmk_out :
        ConjClasses.mk (repr C) = C.1 := by
      change ConjClasses.mk C.1.out = C.1
      exact Quotient.out_eq C.1
    have : C.1 = ConjClasses.mk g := by
      calc
        C.1 = ConjClasses.mk (repr C) := by
                symm; exact hmk_out
        _   = ConjClasses.mk g := hmk
    simpa [C0] using this

noncomputable instance [Finite G] : Fintype (PRegularClass p G) := by
  letI : Finite (ConjClasses G) := Quotient.finite (IsConj.setoid G)
  letI : Finite (PRegularClass p G) := Subtype.finite
  exact Fintype.ofFinite (PRegularClass p G)

end PRegularClass
