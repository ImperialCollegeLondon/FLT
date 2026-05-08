/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.NumberTheory.NumberField.Basic
public import FLT.Mathlib.Topology.Algebra.UniformRing

/-!
# With Abs

Material destined for Mathlib.
-/

@[expose] public section

namespace WithAbs

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [Field L] [Algebra K L] {w : AbsoluteValue L ℝ}

instance [NumberField K] : NumberField (WithAbs v) :=
  NumberField.of_ringEquiv K (WithAbs v) (equiv v).symm

end WithAbs
