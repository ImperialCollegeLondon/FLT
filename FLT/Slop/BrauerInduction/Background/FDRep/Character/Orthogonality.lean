/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib.RingTheory.SimpleModule.Basic
public import FLT.Slop.BrauerInduction.Background.Rep.Invariants
public import FLT.Slop.BrauerInduction.Background.FDRep.Character.Basic
public import FLT.Slop.BrauerInduction.Background.FDRep.Simple

@[expose] public section

/-!
# Orthogonality of irreducible characters

This file proves the Schur orthogonality relation for characters of simple
objects of `FDRep`.

The scalar product is written algebraically as

`|G|⁻¹ * ∑ g, χ_V(g) * χ_W(g⁻¹)`,

which avoids complex conjugation and works over an algebraically closed field of
characteristic zero.
-/

open CategoryTheory CategoryTheory.Limits BigOperators

namespace FDRep

universe u v w

variable {k : Type u} {G : Type v} [Field k] [Group G]

/--
The character scalar product computes the dimension of the equivariant Hom
space.

With the convention
`⟪χ_V, χ_W⟫ = |G|⁻¹ ∑ g, χ_V(g) * χ_W(g⁻¹)`, this scalar product is
`finrank k (W ⟶ V)`.
-/
theorem char_scalarProduct_eq_finrank_hom
    [Fintype G] [CharZero k]
    (V W : FDRep k G) :
    ((Fintype.card G : k)⁻¹) *
        (∑ g : G, V.character g * W.character g⁻¹)
      =
    (Module.finrank k (W ⟶ V) : k) := by
  haveI : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  let τ := Representation.linHom W.ρ V.ρ
  have hsum :
      (∑ g : G, V.character g * W.character g⁻¹) =
        ∑ g : G, τ.character g := by
    apply Finset.sum_congr rfl
    intro g _
    rw [mul_comm]
    simp only [character, Representation.char_linHom, τ]
    rfl
  rw [hsum]
  rw [Representation.average_char_eq_finrank_invariants τ]
  have hfin :
      Module.finrank k τ.invariants =
        Module.finrank k (W ⟶ V) := by
    let U : FDRep k G ⥤ Rep k G :=
      forget₂ (FDRep k G) (Rep k G)
    calc
      Module.finrank k τ.invariants
          = Module.finrank k ((U.obj W) ⟶ (U.obj V)) := by
              have h :=
                LinearEquiv.finrank_eq
                  (Rep.linHomInvariantsEquivHom (U.obj W) (U.obj V))
              convert h using 2 <;> simp [τ, U, FDRep.forget₂_ρ] <;> rfl
      _ = Module.finrank k (W ⟶ V) := by
              exact LinearEquiv.finrank_eq
                (FDRep.forget₂HomLinearEquiv W V)
  exact Nat.cast_inj.mpr hfin

/--
Representations with equal characters have equal dimensions of Hom spaces from
any fixed source representation.
-/
lemma finrank_hom_eq_of_char_eq
    [Finite G] [CharZero k]
    (S V W : FDRep k G)
    (h : V.character = W.character) :
    Module.finrank k (S ⟶ V) = Module.finrank k (S ⟶ W) := by
  letI : Fintype G := Fintype.ofFinite G
  have hV :
      ((Fintype.card G : k)⁻¹) *
          (∑ g : G, V.character g * S.character g⁻¹)
        =
      (Module.finrank k (S ⟶ V) : k) :=
    char_scalarProduct_eq_finrank_hom (k := k) (G := G) V S
  have hW :
      ((Fintype.card G : k)⁻¹) *
          (∑ g : G, W.character g * S.character g⁻¹)
        =
      (Module.finrank k (S ⟶ W) : k) :=
    char_scalarProduct_eq_finrank_hom (k := k) (G := G) W S
  have hcast :
      (Module.finrank k (S ⟶ V) : k) =
        (Module.finrank k (S ⟶ W) : k) := by
    calc
      (Module.finrank k (S ⟶ V) : k)
          =
        ((Fintype.card G : k)⁻¹) *
          (∑ g : G, V.character g * S.character g⁻¹) := hV.symm
      _ =
        ((Fintype.card G : k)⁻¹) *
          (∑ g : G, W.character g * S.character g⁻¹) := by
            rw [h]
      _ =
        (Module.finrank k (S ⟶ W) : k) := hW
  exact Nat.cast_injective hcast


end FDRep
