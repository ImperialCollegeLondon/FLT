import Mathlib.Algebra.Central.Defs
import Mathlib.Algebra.Quaternion
import Mathlib.Analysis.Quaternion -- for *notation* ℍ only!
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

class IsQuaternionAlgebra (F : Type*) [Field F] (D : Type*) [Ring D] [Algebra F D] : Prop where
  isSimpleRing : IsSimpleRing D
  isCentral : Algebra.IsCentral F D
  dim_four : Module.rank F D = 4

namespace IsQuaternionAlgebra

attribute [instance] isSimpleRing isCentral

variable (F : Type*) [Field F] (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]

instance : Module.Finite F D := FiniteDimensional.of_rank_eq_nat dim_four

variable [NumberField F]

open NumberField InfinitePlace

open scoped TensorProduct Quaternion

/-- A quaternion algebra `D` over a number field `F` is totally definite if
`D ⊗[F, v] ℝ` is isomorphic to the Hamilton quaternions ℍ for all real places `v` (that is,
for all ring homomorphisms) `F → ℝ`). -/
def IsTotallyDefinite : Prop := ∀ (v : InfinitePlace F) (hv : v.IsReal),
  letI : Algebra F ℝ := (embedding_of_isReal hv).toAlgebra
  Nonempty (ℝ ⊗[F] D ≃ₐ[ℝ] ℍ)

end IsQuaternionAlgebra
