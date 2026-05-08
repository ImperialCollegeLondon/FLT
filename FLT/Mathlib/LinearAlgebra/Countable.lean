/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.LinearAlgebra.Countable
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Data.Rat.Encodable

/-!
# Countable

Material destined for Mathlib.
-/

@[expose] public section

-- TODO upstream
lemma Countable.of_module_finite (R M : Type*) [Semiring R] [Countable R]
    [AddCommMonoid M] [Module R M] [Module.Finite R M] : Countable M := by
  obtain ⟨n, s, h⟩ := Module.Finite.exists_fin (R := R) (M := M)
  rw [← Set.countable_univ_iff]
  have : Countable (Submodule.span R (Set.range s)) := inferInstance
  rwa [h] at this

instance (K : Type*) [Field K] [NumberField K] : Countable K :=
  Countable.of_module_finite ℚ K
