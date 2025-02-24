import Mathlib.Topology.Algebra.Ring.Basic

class IsTopologicalModule
    (R : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [TopologicalSpace M]
    extends ContinuousSMul R M, ContinuousAdd M

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]


-- Changing "def" by
--    see Note [lower instance priority]
--    instance (priority := 50)
-- makes something break in InverseLimit.Topology. I don't understand this
def DiscreteTopology.isTopologicalModule [DiscreteTopology R] [DiscreteTopology M] :
    IsTopologicalModule R M := by
  exact {
    continuous_smul := by continuity
    continuous_add := by continuity
  }
