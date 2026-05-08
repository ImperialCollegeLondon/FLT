/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix

/-!
# Finite Dimension

Material destined for Mathlib.
-/

@[expose] public section

theorem Basis.toMatrix_continuous {ι R M : Type*} [AddCommGroup M]
    [Finite ι] [TopologicalSpace M] [NontriviallyNormedField R] [Module R M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [CompleteSpace R] [T2Space M]
    [FiniteDimensional R M] (B : Module.Basis ι R M) :
    Continuous fun (v : ι → M) => B.toMatrix v :=
  let := Fintype.ofFinite ι
  LinearMap.continuous_of_finiteDimensional B.toMatrixEquiv.toLinearMap
