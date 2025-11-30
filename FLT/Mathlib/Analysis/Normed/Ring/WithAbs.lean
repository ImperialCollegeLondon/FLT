import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.NumberTheory.NumberField.Basic
import FLT.Mathlib.Topology.Algebra.UniformRing

namespace WithAbs

variable {R S : Type*} [Semiring S] [Field R] [PartialOrder S] (v : AbsoluteValue R S)

instance : Field (WithAbs v) := ‹Field R›

variable {R' : Type*} [Field R'] [Module R R']

instance [Module R R'] [FiniteDimensional R R'] : FiniteDimensional (WithAbs v) R' :=
  ‹FiniteDimensional R R'›

instance [Algebra R R'] [Algebra.IsSeparable R R'] : Algebra.IsSeparable (WithAbs v) R' :=
  ‹Algebra.IsSeparable R R'›

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [Field L] [Algebra K L] {w : AbsoluteValue L ℝ}

instance : Algebra (WithAbs v) (WithAbs w) := ‹Algebra K L›

instance : Algebra K (WithAbs w) := ‹Algebra K L›

instance [NumberField K] : NumberField (WithAbs v) := ‹NumberField K›

theorem norm_eq_abs (x : WithAbs v) : ‖x‖ = v x := rfl

theorem uniformContinuous_algebraMap {v : AbsoluteValue K ℝ} {w : AbsoluteValue L ℝ}
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v (WithAbs.equiv v x)) :
    UniformContinuous (algebraMap (WithAbs v) (WithAbs w)) :=
  AddMonoidHomClass.isometry_of_norm _ h |>.uniformContinuous

instance : UniformContinuousConstSMul K (WithAbs w) :=
  uniformContinuousConstSMul_of_continuousConstSMul _ _

instance : IsScalarTower K L (WithAbs w) := inferInstanceAs (IsScalarTower K L L)

end WithAbs

namespace AbsoluteValue.Completion

variable {K : Type*} [Field K] {v : AbsoluteValue K ℝ}
  {L : Type*} [Field L] [Algebra K L] {w : AbsoluteValue L ℝ}

/-- If $K/L$ are fields, $v$ and $w$ are absolute values of $K$ and $L$ respectively, such that
$w|_K = v$, then this is the natural semi-algebra map from the completion $K_v$ of $K$ at $v$
to the completion $L_w$ at $w$. -/
noncomputable abbrev semialgHomOfComp
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v (WithAbs.equiv v x)) :
    v.Completion →ₛₐ[algebraMap (WithAbs v) (WithAbs w)] w.Completion :=
  UniformSpace.Completion.mapSemialgHom _
    (AddMonoidHomClass.isometry_of_norm _  h).uniformContinuous.continuous

theorem semialgHomOfComp_coe
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v (WithAbs.equiv v x))
    (x : WithAbs v) :
    semialgHomOfComp h x = algebraMap (WithAbs v) (WithAbs w) x :=
  UniformSpace.Completion.mapSemialgHom_coe
    (AddMonoidHomClass.isometry_of_norm _  h).uniformContinuous x

theorem semiAlgHomOfComp_dist_eq
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v (WithAbs.equiv v x))
    (x y : v.Completion) :
    dist (semialgHomOfComp h x) (semialgHomOfComp h y) = dist x y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ (fun x y => ?_)
  · refine isClosed_eq ?_ continuous_dist
    exact continuous_iff_continuous_dist.1 UniformSpace.Completion.continuous_extension
  · rw [semialgHomOfComp_coe, semialgHomOfComp_coe, UniformSpace.Completion.dist_eq]
    exact UniformSpace.Completion.dist_eq x y ▸
      (AddMonoidHomClass.isometry_of_norm _ h).dist_eq x y

theorem isometry_semiAlgHomOfComp
    (h : ∀ x, w (algebraMap (WithAbs v) (WithAbs w) x) = v (WithAbs.equiv v x)) :
    Isometry (semialgHomOfComp h) :=
  Isometry.of_dist_eq <| semiAlgHomOfComp_dist_eq h

end AbsoluteValue.Completion
