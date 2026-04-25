module

public import Mathlib.Analysis.Normed.Field.WithAbs
public import Mathlib.NumberTheory.NumberField.Basic
public import FLT.Mathlib.Topology.Algebra.UniformRing

@[expose] public section

namespace WithAbs

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [Field L] [Algebra K L] {w : AbsoluteValue L ℝ}

instance [NumberField K] : NumberField (WithAbs v) :=
  NumberField.of_ringEquiv K (WithAbs v) (equiv v).symm

end WithAbs
