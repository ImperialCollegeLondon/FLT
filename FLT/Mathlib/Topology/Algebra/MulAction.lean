/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper, Kevin Buzzard
-/
module

public import Mathlib.Topology.Algebra.MulAction

/-!
# Mul Action

Material destined for Mathlib.
-/

@[expose] public section

variable {ι A : Type*}
variable {R : ι → Type*} [Π i, Ring (R i)]
variable {M : ι → Type*} [Π i, AddCommGroup (M i)] [Π i, Module (R i) (M i)]
variable [Π i, TopologicalSpace (R i)] [Π i, TopologicalSpace (M i)]
variable [∀ i, ContinuousSMul (R i) (M i)]

instance : ContinuousSMul ((i : ι) → R i) ((i : ι) → M i) :=
  ⟨continuous_pi fun i ↦
    (Continuous.smul ((continuous_apply i).comp (Continuous.fst continuous_id'))
      ((continuous_apply i).comp (Continuous.snd continuous_id')))⟩
