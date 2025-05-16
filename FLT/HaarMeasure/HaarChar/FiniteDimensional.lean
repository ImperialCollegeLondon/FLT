import FLT.HaarMeasure.HaarChar.Ring
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.LinearAlgebra.Determinant

namespace MeasureTheory

open Measure


variable {F : Type*} [Field F] [MeasurableSpace F] [TopologicalSpace F] [BorelSpace F]
  [IsTopologicalRing F] [LocallyCompactSpace F]

section addequiv

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [Module F V] [FiniteDimensional F V] [IsModuleTopology F V]
    [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] -- this can be proved from the preceding hypos
                            -- but typeclass inference can't find it because it
                            -- can't find V


lemma addEquivAddHaarChar_eq_ringHaarChar_det (ρ : V ≃L[F] V) :
    addEquivAddHaarChar ρ.toContinuousAddEquiv = ringHaarChar ρ.toLinearEquiv.det :=
  sorry -- FLT#task009

end addequiv

section ring

variable (F)

variable {A : Type*} [Ring A] [TopologicalSpace A]
    [Algebra F A] [FiniteDimensional F A] [IsModuleTopology F A]
    [IsTopologicalRing A] -- can be deduced from previous assumptions but only using F
    [LocallyCompactSpace A] -- can also be proved but only using F
    [MeasurableSpace A] [BorelSpace A]

-- needs PRing
def _root_.ContinuousLinearEquiv.mulLeft (u : Aˣ) : A ≃L[F] A where
  __ := LinearEquiv.mulLeft F u
  continuous_toFun := continuous_mul_left _
  continuous_invFun := continuous_mul_left _

-- needs PRing
def _root_.ContinuousLinearEquiv.mulRight (u : Aˣ) : A ≃L[F] A where
  __ := LinearEquiv.mulRight F u
  continuous_toFun := continuous_mul_right _
  continuous_invFun := continuous_mul_right _

lemma ringAddHaarChar_eq_ringHaarChar_det (u : Aˣ) :
    ringHaarChar u = ringHaarChar (LinearEquiv.mulLeft F u).det :=
  addEquivAddHaarChar_eq_ringHaarChar_det (ContinuousLinearEquiv.mulLeft F u)

end ring

section issimplering

variable {D : Type*} [Ring D] [TopologicalSpace D]
    [Algebra F D] [FiniteDimensional F D] [IsSimpleRing D]
    [IsModuleTopology F D]
    [IsTopologicalRing D] -- can be deduced from previous assumptions but only using F
    [LocallyCompactSpace D] -- can also be proved but only using F
    [MeasurableSpace D] [BorelSpace D]

#check ContinuousLinearEquiv.mulLeft

include F in
lemma _root_.IsSimpleRing.ringHaarChar_eq_addEquivAddHaarChar_mulRight (u : Dˣ) :
    ringHaarChar u = addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  rw [ringAddHaarChar_eq_ringHaarChar_det F u]
  rw [IsSimpleRing.mulLeft_det_eq_mulRight_det']
  -- convert addEquivAddHaarChar_eq_ringHaarChar_det (ContinuousLinearEquiv.mulRight F u)
  sorry -- this should be easy

end issimplering
