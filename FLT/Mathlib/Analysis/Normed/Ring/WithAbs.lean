import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.NumberTheory.NumberField.Basic
import FLT.Mathlib.Topology.Algebra.UniformRing

namespace WithAbs

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [Field L] [Algebra K L] {w : AbsoluteValue L ℝ}

instance : Algebra (WithAbs v) (WithAbs w) := ‹Algebra K L›

instance : Algebra K (WithAbs w) := ‹Algebra K L›

instance [NumberField K] : NumberField (WithAbs v) := ‹NumberField K›

theorem norm_eq_abs (x : WithAbs v) : ‖x‖ = v x := rfl

theorem uniformContinuous_algebraMap {v : AbsoluteValue K ℝ} {w : AbsoluteValue L ℝ}
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v (WithAbs.equiv v x)) :
    UniformContinuous (algebraMap (WithAbs v) (WithAbs w)) :=
  isUniformInducing_of_comp h |>.uniformContinuous

instance : UniformContinuousConstSMul K (WithAbs w) :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

instance : IsScalarTower K L (WithAbs w) := inferInstanceAs (IsScalarTower K L L)

end WithAbs

namespace AbsoluteValue.Completion

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [Field L] [Algebra K L] {w : AbsoluteValue L ℝ}

noncomputable abbrev semialgHomOfComp
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v (WithAbs.equiv v x)) :
    v.Completion →ₛₐ[algebraMap (WithAbs v) (WithAbs w)] w.Completion :=
  UniformSpace.Completion.mapSemialgHom _
    (WithAbs.isUniformInducing_of_comp h).uniformContinuous.continuous

theorem semialgHomOfComp_coe
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v (WithAbs.equiv v x))
    (x : WithAbs v) :
    semialgHomOfComp h x = algebraMap (WithAbs v) (WithAbs w) x :=
  UniformSpace.Completion.mapSemialgHom_coe
    (WithAbs.isUniformInducing_of_comp h).uniformContinuous x

theorem semiAlgHomOfComp_dist_eq
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v (WithAbs.equiv v x))
    (x y : v.Completion) :
    dist (semialgHomOfComp h x) (semialgHomOfComp h y) = dist x y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ (fun x y => ?_)
  · refine isClosed_eq ?_ continuous_dist
    exact continuous_iff_continuous_dist.1 UniformSpace.Completion.continuous_extension
  · rw [semialgHomOfComp_coe, semialgHomOfComp_coe, UniformSpace.Completion.dist_eq]
    exact UniformSpace.Completion.dist_eq x y ▸
      (WithAbs.isometry_of_comp (L := WithAbs w) h).dist_eq x y

theorem isometry_semiAlgHomOfComp
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v (WithAbs.equiv v x)) :
    Isometry (semialgHomOfComp h) :=
  Isometry.of_dist_eq <| semiAlgHomOfComp_dist_eq h

end AbsoluteValue.Completion
