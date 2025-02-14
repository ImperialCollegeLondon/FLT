import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Monoid

class TopologicalModule
    (R : Type*) [Ring R] [TopologicalSpace R] [TopologicalRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [TopologicalSpace M]
    extends ContinuousSMul R M, ContinuousAdd M
