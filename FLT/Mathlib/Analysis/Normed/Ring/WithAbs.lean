import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.NumberTheory.NumberField.Basic
import FLT.Mathlib.Topology.Algebra.UniformRing

namespace WithAbs

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [Field L] [Algebra K L] {w : AbsoluteValue L ℝ}

instance [NumberField K] : NumberField (WithAbs v) :=
  NumberField.of_ringEquiv K (WithAbs v) (equiv v).symm

end WithAbs
