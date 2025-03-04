import Mathlib.Algebra.Central.Defs
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.LinearAlgebra.FiniteDimensional

class IsQuaternionAlgebra (F : Type*) [Field F] (D : Type*) [Ring D] [Algebra F D] : Prop where
  isSimpleRing : IsSimpleRing D
  isCentral : Algebra.IsCentral F D
  dim_four : Module.rank F D = 4

namespace IsQuaternionAlgebra

attribute [instance] isSimpleRing isCentral

variable (F : Type*) [Field F] (D : Type*) [Ring D] [Algebra F D] [IsQuaternionAlgebra F D]

instance : Module.Finite F D := FiniteDimensional.of_rank_eq_nat dim_four
