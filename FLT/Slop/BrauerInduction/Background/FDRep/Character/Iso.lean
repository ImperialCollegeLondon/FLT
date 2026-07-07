/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import FLT.Slop.BrauerInduction.Background.FDRep.Character.Orthogonality
public import FLT.Slop.BrauerInduction.Background.FDRep.SimpleDecomposition

/-!
# Characters determine finite-dimensional representations

Over an algebraically closed field of characteristic zero, two finite-dimensional
representations of a finite group are isomorphic if and only if their characters
are equal.

The proof decomposes both representations into finite biproducts of simple
representations, uses Schur orthogonality to compare the multiplicities of each
simple summand, and then reindexes the resulting biproducts.
-/

@[expose] public section

namespace Slop
open Slop

open CategoryTheory
open CategoryTheory.Limits

namespace FDRep

universe u v

variable {k : Type u} {G : Type u} [Field k] [Group G]

open Classical in
/--
Over an algebraically closed field of characteristic zero, characters determine
finite-dimensional representations of a finite group up to isomorphism.

More precisely, two objects of `FDRep k G` have equal characters if and only if
they are isomorphic.
-/
theorem char_eq_iff_iso
    [Finite G] [CharZero k] [IsAlgClosed k]
    (V W : FDRep k G) :
    V.character = W.character ↔ Nonempty (V ≅ W) := by
  constructor
  · intro hchar
    haveI : NeZero (Nat.card G : k) := by
      refine ⟨?_⟩
      have hNat : Nat.card G ≠ 0 := by
        exact (Nat.card_ne_zero).mpr ⟨⟨1⟩, inferInstance⟩
      exact_mod_cast hNat
    rcases exists_simple_decomposition V with
      ⟨ι, f, instι, hf, ⟨eV⟩⟩
    rcases exists_simple_decomposition W with
      ⟨κ, g, instκ, hg, ⟨eW⟩⟩
    letI : Fintype ι := instι
    letI : Fintype κ := instκ
    have hcount :
        ∀ (S : FDRep k G) [Simple S],
          (∑ i, if Nonempty (S ≅ f i) then 1 else 0)
            =
          (∑ j, if Nonempty (S ≅ g j) then 1 else 0) := by
      intro S hS
      have hHomVW :
          Module.finrank k (S ⟶ V) =
            Module.finrank k (S ⟶ W) :=
        finrank_hom_eq_of_char_eq S V W hchar
      have hHomV :
          Module.finrank k (S ⟶ V) =
            Module.finrank k (S ⟶ ⨁ f) :=
              Eq.symm (finrank_hom_eq_of_char_eq S (⨁ f) V (FDRep.char_iso (id eV.symm)))
      have hHomW :
          Module.finrank k (S ⟶ W) =
            Module.finrank k (S ⟶ ⨁ g) := finrank_hom_eq_of_char_eq S W (⨁ g) (FDRep.char_iso eW)
      have hsumf :
          Module.finrank k (S ⟶ ⨁ f) =
            ∑ i, (if Nonempty (S ≅ f i) then 1 else 0) :=
        finrank_hom_to_biproduct_simple
          (S := S) (f := f) hf
      have hsumg :
          Module.finrank k (S ⟶ ⨁ g) =
            ∑ j, (if Nonempty (S ≅ g j) then 1 else 0) :=
        finrank_hom_to_biproduct_simple
          (S := S) (f := g) hg
      calc
        (∑ i, if Nonempty (S ≅ f i) then 1 else 0)
            = Module.finrank k (S ⟶ ⨁ f) := hsumf.symm
        _ = Module.finrank k (S ⟶ V) := hHomV.symm
        _ = Module.finrank k (S ⟶ W) := hHomVW
        _ = Module.finrank k (S ⟶ ⨁ g) := hHomW
        _ = ∑ j, if Nonempty (S ≅ g j) then 1 else 0 := hsumg
    have hcount_f :
        ∀ i₀ : ι,
          (∑ i, if Nonempty (f i₀ ≅ f i) then 1 else 0)
            =
          (∑ j, if Nonempty (f i₀ ≅ g j) then 1 else 0) := by
      intro i₀
      haveI : Simple (f i₀) := hf i₀
      exact hcount (f i₀)
    have hcount_g :
        ∀ j₀ : κ,
          (∑ i, if Nonempty (g j₀ ≅ f i) then 1 else 0)
            =
          (∑ j, if Nonempty (g j₀ ≅ g j) then 1 else 0) := by
      intro j₀
      haveI : Simple (g j₀) := hg j₀
      exact hcount (g j₀)
    rcases FDRep.biproduct_iso_of_iso_counts
        (k := k) (G := G) (f := f) (g := g)
        hcount_f hcount_g with ⟨eFG⟩
    exact ⟨eV ≪≫ eFG ≪≫ eW.symm⟩
  · rintro ⟨e⟩
    exact char_eq_of_iso e

/--
Construct an isomorphism between two representations if their characters are equal.
Uses choice to pick one of the existing isomorphisms.
-/
noncomputable def iso_of_char_eq
  [Finite G] [CharZero k] [IsAlgClosed k]
  {V W : FDRep k G} (h : V.character = W.character) : V ≅ W :=
  Classical.choice ((char_eq_iff_iso V W).mp h)

end FDRep

end Slop
