/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.Background.FDRep.Character.Basic
public import FLT.Slop.Background.FDRep.SimpleDecomposition
public import FLT.Slop.Background.Fintype.Basic

@[expose] public section

universe u v w

namespace FDRep

variable {k : Type u} {G : Type u}
variable [Field k] [Group G]

/--
The character of any finite-dimensional representation lies in the `ℤ`-span of
the characters of simple representations.

This is proved by decomposing the representation as a finite biproduct of simple
representations and using additivity of characters over finite biproducts.
-/
theorem character_mem_span_simple_characters
    [Finite G] [CharZero k] [IsAlgClosed k]
    (V : FDRep k G) :
    V.character ∈
      Submodule.span ℤ
        { χ : G → k |
            ∃ (S : FDRep k G)
              (_ : CategoryTheory.Simple S),
              χ = S.character } := by
  haveI : NeZero (Nat.card G : k) := ⟨One.natCast_natCard_ne_zero_of_finite G k⟩
  obtain ⟨ι, f, hι, hsimple, ⟨e⟩⟩ :=
    FDRep.exists_simple_decomposition V
  letI : Fintype ι := hι
  rw [FDRep.char_eq_of_iso e]
  rw [FDRep.char_biproduct]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.subset_span
      ⟨f i, hsimple i, rfl⟩

/--
A family of finite-dimensional representations containing exactly one
representative of every simple isomorphism class.
-/
structure IsCompleteSetOfSimples
    {k : Type u} [Field k]
    {G : Type v} [Group G]
    {ι : Type*}
    (S : ι → FDRep k G) : Prop where
  is_simple : ∀ i, CategoryTheory.Simple (S i)
  is_distinct : ∀ i j, Nonempty (S i ≅ S j) → i = j
  is_exhaustive :
    ∀ T : FDRep k G,
      CategoryTheory.Simple T → ∃ i, Nonempty (T ≅ S i)

namespace IsCompleteSetOfSimples

/-- Distinct members of a complete set of simples are not isomorphic. -/
lemma isEmpty_iso_of_ne
    {k : Type u} [Field k]
    {G : Type v} [Group G]
    {ι : Type*}
    {S : ι → FDRep k G}
    (hS : FDRep.IsCompleteSetOfSimples S)
    {i j : ι}
    (hij : i ≠ j) :
    IsEmpty (S i ≅ S j) := by
  refine ⟨?_⟩
  intro e
  exact hij (hS.is_distinct i j ⟨e⟩)

/--
For a complete set of simple representatives, two indexed simples are
isomorphic iff their indices are equal.
-/
lemma iso_iff_eq
    {k : Type u} [Field k]
    {G : Type v} [Group G]
    {ι : Type*}
    {S : ι → FDRep k G}
    (hS : FDRep.IsCompleteSetOfSimples S)
    (i j : ι) :
    Nonempty (S i ≅ S j) ↔ i = j := by
  constructor
  · exact hS.is_distinct i j
  · rintro rfl
    exact ⟨CategoryTheory.Iso.refl (S i)⟩

end IsCompleteSetOfSimples

end FDRep
