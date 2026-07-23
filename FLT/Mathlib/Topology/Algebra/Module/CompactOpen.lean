/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The compact-open topology on continuous linear maps

This file endows `M1 →L[k] M2` with the topology induced from the compact-open topology on
`C(M1, M2)`, as scoped instances in the `ContinuousLinearMap.CompactOpen` namespace, and shows
that it makes `M1 →L[k] M2` a topological `k`-module.

These instances are scoped since they may differ from the topology of bounded convergence used
elsewhere in Mathlib for continuous linear maps between uniform modules.

Material destined for a new file `Mathlib.Topology.Algebra.Module.CompactOpen`.
-/

@[expose] public section

universe u w

namespace ContinuousLinearMap.CompactOpen

variable {k : Type u} {M1 M2 : Type w} [CommRing k] [TopologicalSpace k]
  [AddCommGroup M1] [Module k M1] [TopologicalSpace M1] [IsTopologicalAddGroup M1]
  [AddCommGroup M2] [Module k M2] [TopologicalSpace M2] [IsTopologicalAddGroup M2]

/-- The topology on `M1 →L[k] M2` induced from the compact-open topology on `C(M1, M2)`. -/
scoped instance topologicalSpace : TopologicalSpace (M1 →L[k] M2) :=
  TopologicalSpace.induced (fun f ↦ ⟨f.toFun, f.cont⟩ : (M1 →L[k] M2) → C(M1, M2)) inferInstance

scoped instance isTopologicalAddGroup : IsTopologicalAddGroup (M1 →L[k] M2) :=
  Topology.IsInducing.topologicalAddGroup
    ({ toFun f := ⟨f, f.cont⟩
       map_zero' := rfl
       map_add' _ _ := rfl } : (M1 →L[k] M2) →+ C(M1, M2)) ⟨rfl⟩

scoped instance continuousSMul [ContinuousSMul k M2] :
    ContinuousSMul k (M1 →L[k] M2) :=
  Topology.IsInducing.continuousSMul (X := C(M1, M2)) ⟨rfl⟩ continuous_id rfl

end ContinuousLinearMap.CompactOpen
