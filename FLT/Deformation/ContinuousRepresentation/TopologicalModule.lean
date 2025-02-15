import Mathlib.Topology.Algebra.Ring.Basic

class TopologicalModule
    (R : Type*) [Ring R] [TopologicalSpace R] [TopologicalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [TopologicalSpace M]
    extends ContinuousSMul R M, ContinuousAdd M
