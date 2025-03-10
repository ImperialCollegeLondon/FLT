import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.NumberTheory.NumberField.Basic

namespace WithAbs

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [Field L] [Algebra K L] {w : AbsoluteValue L ℝ}

instance : Algebra (WithAbs v) (WithAbs w) := ‹Algebra K L›

instance : Algebra K (WithAbs w) := ‹Algebra K L›

instance [NumberField K] : NumberField (WithAbs v) := ‹NumberField K›

theorem norm_eq_abs (x : WithAbs v) : ‖x‖ = v x := rfl

theorem uniformContinuous_algebraMap {v : AbsoluteValue K ℝ} {w : AbsoluteValue L ℝ}
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v x) :
    UniformContinuous (algebraMap (WithAbs v) (WithAbs w)) :=
  isUniformInducing_of_comp h |>.uniformContinuous

end WithAbs
