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

instance {w : AbsoluteValue L ℝ} [Algebra K L] :
    Algebra K (WithAbs w) :=
  ‹Algebra K L›

instance {w : AbsoluteValue L ℝ} : UniformContinuousConstSMul K (WithAbs w) :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

instance {w : AbsoluteValue L ℝ}  : IsScalarTower K L (WithAbs w) :=
  inferInstanceAs (IsScalarTower K L L)

theorem uniformContinuous_algebraMap {v : AbsoluteValue K ℝ} {w : AbsoluteValue L ℝ}
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v x) :
    UniformContinuous (algebraMap (WithAbs v) (WithAbs w)) :=
  isUniformInducing_of_comp h |>.uniformContinuous

end WithAbs

namespace AbsoluteValue.Completion

variable {K L : Type*} [Field K] [Field L] {v : AbsoluteValue K ℝ}
  {w : AbsoluteValue L ℝ}

abbrev mapOfComp {g : WithAbs v →+* WithAbs w} (h : ∀ x, w (g x) = v x) :
    v.Completion →+* w.Completion :=
  UniformSpace.Completion.mapRingHom g
    (WithAbs.isUniformInducing_of_comp h).uniformContinuous.continuous

theorem mapOfComp_coe {g : WithAbs v →+* WithAbs w} (h : ∀ x, w (g x) = v x) (x : K) :
    mapOfComp h x = g x :=
  UniformSpace.Completion.mapRingHom_coe
    (WithAbs.isUniformInducing_of_comp h).uniformContinuous x

end AbsoluteValue.Completion
