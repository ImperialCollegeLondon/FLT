import Mathlib.Analysis.Normed.Ring.WithAbs
import Mathlib.NumberTheory.NumberField.Basic

namespace WithAbs

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [Field L] [Algebra K L] {w : AbsoluteValue L ℝ}

instance : Algebra (WithAbs v) (WithAbs w) := ‹Algebra K L›

instance : Algebra K (WithAbs w) := ‹Algebra K L›

instance [NumberField K] : NumberField (WithAbs v) := ‹NumberField K›

theorem norm_eq_abs (x : WithAbs v) : ‖x‖ = v x := rfl

end WithAbs
