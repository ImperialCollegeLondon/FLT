import FLT.AutomorphicForm.QuaternionAlgebra.Defs

namespace TotallyDefiniteQuaternionAlgebra

open DedekindDomain
open scoped TensorProduct NumberField

variable (F : Type*) [Field F] [NumberField F]
    [NumberField.IsTotallyReal F]
    (D : Type*) [Ring D] [Algebra F D]
    -- D has to be totally definite

variable  (R : Type*) [Field R]
  -- weight
  (W : Type*) [AddCommGroup W] [Module R W] [DistribMulAction Dˣ W] [SMulCommClass R Dˣ W]
  -- level
  (U : Subgroup (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ)
  -- subgroup should be open (and in practice will be compact)
  --(oU : IsOpen (U : Set (D ⊗[F] (FiniteAdeleRing (𝓞 F) F))ˣ))
  -- character
  (χ : (FiniteAdeleRing (𝓞 F) F)ˣ →* R)

-- false as stated
theorem AutomorphicForm.finiteDimensional [FiniteDimensional R W] :
    FiniteDimensional R (WeightTwoAutomorphicForm F D R) := sorry

end TotallyDefiniteQuaternionAlgebra
