import FLT.AutomorphicForm.QuaternionAlgebra.Defs
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

namespace TotallyDefiniteQuaternionAlgebra

open IsDedekindDomain NumberField IsQuaternionAlgebra
open scoped TensorProduct TensorProduct.RightActions

variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
    {D : Type*} [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]
    (hD : IsTotallyDefinite F D)

variable (K : Type*) [Field K]
    (U : Subgroup (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ)
    (hU : IsOpen (U : Set (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ))

open TotallyDefiniteQuaternionAlgebra

theorem WeightTwoAutomorphicForm.finiteDimensional :
    FiniteDimensional K (WeightTwoAutomorphicFormOfLevel U K) :=
  sorry

end TotallyDefiniteQuaternionAlgebra
