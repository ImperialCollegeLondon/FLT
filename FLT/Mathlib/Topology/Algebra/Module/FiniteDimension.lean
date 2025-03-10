import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix

theorem Basis.toMatrix_continuous {ι R M : Type*}  [AddCommGroup M]
    [Fintype ι] [TopologicalSpace M] [NontriviallyNormedField R] [Module R M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [CompleteSpace R] [T2Space M]
    [FiniteDimensional R M] (B : Basis ι R M) :
    Continuous fun (v : ι → M) => B.toMatrix v :=
  LinearMap.continuous_of_finiteDimensional B.toMatrixEquiv.toLinearMap
