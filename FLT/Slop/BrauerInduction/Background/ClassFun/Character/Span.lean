/-
Copyright (c) 2025 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module


public import FLT.Slop.BrauerInduction.Background.ClassFun.Character.Basic
public import FLT.Slop.BrauerInduction.Background.FDRep.SimpleDecomposition

/-!
# Spans of irreducible characters

This file proves that characters of finite-dimensional representations are
integer linear combinations of characters of simple representations.

Under the hypothesis that the order of the finite group is nonzero in the
coefficient field, Maschke's theorem decomposes every representation as a
finite biproduct of simple representations. Taking characters gives the
corresponding decomposition into a finite sum of irreducible characters.
Consequently, every virtual character lies in their `ℤ`-linear span.
-/

@[expose] public section

namespace Slop
open Slop

universe u v

namespace ClassFun

open CategoryTheory CategoryTheory.Limits
open scoped BigOperators

variable {k : Type u} {G : Type u}
variable [Field k] [Group G]

/--
The character of a finite-dimensional representation is a finite sum of
characters of simple representations.
-/
theorem char_eq_sum_simples
    [Finite G] [NeZero (Nat.card G : k)]
    (V : FDRep k G) :
    ∃ (ι : Type) (S : ι → FDRep k G)
      (_ : Fintype ι) (_ : ∀ i, Simple (S i)),
      ClassFun.character V =
        ∑ i : ι, ClassFun.character (S i) := by
  obtain ⟨ι, S, hι, hSimple, ⟨e⟩⟩ :=
    FDRep.exists_simple_decomposition V
  letI : Fintype ι := hι
  refine ⟨ι, S, inferInstance, hSimple, ?_⟩
  calc
    ClassFun.character V
        = ClassFun.character (Limits.biproduct S) :=
          ClassFun.char_eq_of_iso e
    _ = ∑ i : ι, ClassFun.character (S i) :=
          ClassFun.char_biproduct S

/--
The set of characters of simple finite-dimensional representations of `G`
over `k`.
-/
def irreducibleCharacterSet
    (k : Type u) [Field k]
    (G : Type v) [Group G] :
    Set (ClassFun k G) :=
  { ψ : ClassFun k G |
    ∃ (S : FDRep k G)
      (_ : Simple S),
      ψ = ClassFun.character S }

/--
The character of a finite-dimensional representation belongs to the
`ℤ`-linear span of the characters of simple representations.
-/
theorem character_mem_span_irreducibles
    [Finite G] [NeZero (Nat.card G : k)]
    (V : FDRep k G) :
    ClassFun.character V ∈
      Submodule.span ℤ
        (irreducibleCharacterSet k G) := by
  obtain ⟨ι, S, hι, hSimple, hchar⟩ :=
    char_eq_sum_simples (k := k) (G := G) V
  letI : Fintype ι := hι
  rw [hchar]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.subset_span
      ⟨S i, hSimple i, rfl⟩

theorem character_mem_span_irreducibles_of_eq
    [Finite G] [NeZero (Nat.card G : k)]
    (φ : ClassFun k G)
    (h_rep : ∃ V : FDRep k G,
      φ = ClassFun.character V) :
    φ ∈
      Submodule.span ℤ
        (irreducibleCharacterSet k G) := by
  obtain ⟨V, rfl⟩ := h_rep
  exact character_mem_span_irreducibles V

/--
The virtual character group of `G`: the `ℤ`-span of irreducible characters
inside the group of `k`-valued class functions.
-/
def virtualCharacterSubmodule
    (k : Type u) [Field k]
    (G : Type v) [Group G] :
    Submodule ℤ (ClassFun k G) :=
  Submodule.span ℤ (ClassFun.irreducibleCharacterSet k G)


end ClassFun

end Slop
