import Mathlib.Analysis.Normed.Ring.WithAbs
import FLT.Mathlib.Topology.Algebra.UniformRing

/-!
# `WithAbs`
-/

noncomputable section

namespace WithAbs

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

instance {v : AbsoluteValue K ℝ} {w : AbsoluteValue L ℝ} :
    Algebra (WithAbs v) (WithAbs w) :=
  ‹Algebra K L›

theorem uniformContinuous_algebraMap {v : AbsoluteValue K ℝ} {w : AbsoluteValue L ℝ}
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v x) :
    UniformContinuous (algebraMap (WithAbs v) (WithAbs w)) :=
  isUniformInducing_of_comp h |>.uniformContinuous

end WithAbs
