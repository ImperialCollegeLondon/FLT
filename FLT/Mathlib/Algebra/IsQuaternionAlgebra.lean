import Mathlib.Algebra.Central.Defs
import Mathlib.LinearAlgebra.Dimension.Basic

class IsQuaternionAlgebra (F : Type*) [Field F] (D : Type*) [Ring D] [Algebra F D] : Prop where
  isSimpleRing : IsSimpleRing D
  isCentral : Algebra.IsCentral F D
  dim_four : Module.rank F D = 4
