/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kevin Buzzard, Matthew Jasper
-/
module

public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Basic

Material destined for Mathlib.
-/

@[expose] public section

variable {R S : Type*} [Ring R]

/-- If `S` is a subring of `R`, then `S` can be viewed as an `S`-submodule of `R`. -/
def Subring.toSubmodule (S : Subring R) : Submodule S R where
  __ := S
  smul_mem' x y h := by
    rw [smul_def, smul_eq_mul]
    apply S.mul_mem (SetLike.coe_mem x) h
