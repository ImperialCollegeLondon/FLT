/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Basic

Material destined for Mathlib.
-/

@[expose] public section

variable {R : Type*} [Ring R] (I : Ideal R) [I.IsTwoSided]

theorem Ideal.Quotient.out_sub (x : R) : (Ideal.Quotient.mk I x).out - x ∈ I := by
  rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
