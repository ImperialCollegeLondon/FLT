module

public import Mathlib.Topology.Instances.Matrix
-- needs additional import so maybe Mathlib.Topology.Instances.Matrix not
-- the right place for it?
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

instance (R : Type*) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (m n : Type*) [Finite m] [Finite n] :
  IsModuleTopology R (Matrix m n R) := IsModuleTopology.instPi
