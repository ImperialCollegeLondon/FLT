import Mathlib.Topology.Algebra.Ring.Basic

class IsTopologicalModule
    (R : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [TopologicalSpace M]
    extends ContinuousSMul R M, ContinuousAdd M
