import FLT.AutomorphicForm.QuaternionAlgebra.Defs
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

namespace TotallyDefiniteQuaternionAlgebra

open IsDedekindDomain NumberField IsQuaternionAlgebra
open scoped TensorProduct TensorProduct.RightActions

-- let F be a totally real field
variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
    -- and let D be a totally definite quaternion algebra over F
    {D : Type*} [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]
    (hD : IsTotallyDefinite F D)

-- Let K be a coefficient field
variable (K : Type*) [Field K]
    -- and let U, the level, be a (compact) open subgroup of `(D ⊗ 𝔸_F^∞)ˣ`
    (U : Subgroup (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ)
    (hU : IsOpen (U : Set (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ))

open TotallyDefiniteQuaternionAlgebra

-- Then the space of K-valued weight 2 level U modular forms for Dˣ is finite-dimensional over K.
/-- The space of `K`-valued weight 2 level `U` quaternionic automorphic forms
for `Dˣ` is finite-dimensional over `K`.
-/
theorem WeightTwoAutomorphicForm.finiteDimensional :
    FiniteDimensional K (WeightTwoAutomorphicFormOfLevel U K) :=
  sorry

end TotallyDefiniteQuaternionAlgebra
