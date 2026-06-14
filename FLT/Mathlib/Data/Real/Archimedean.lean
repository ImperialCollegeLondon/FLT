/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
/-!
# Archimedean

Material destined for Mathlib.
-/

@[expose] public section

-- The file this was destined for (Mathlib.Data.Real.Archimedean) no longer
-- exists -- it was moved to Mathlib.Algebra.Order.Archimedean.Real.Basic
lemma Int.eq_floor {a : ℝ} {b : ℤ} (h1 : 0 ≤ a - b) (h2 : a - b < 1) : b = ⌊a⌋ := by
  rw [eq_comm, Int.floor_eq_iff]
  grind
