import FLT.HaarMeasure.HaarChar.Ring
import FLT.Mathlib.Topology.Algebra.Module.Equiv
import FLT.Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Algebra.Module.ModuleTopology

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
  sorry -- FLT#517

end addequiv

section needs_PRing

variable (R : Type*) [CommSemiring R]

variable {A : Type*} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]

variable [Algebra R A]

-- needs PRing
/--
Multiplication on the left by a unit of an F-algebra which is a topological
ring, is a continuous F-linear homeomorphism.
-/
def _root_.ContinuousLinearEquiv.mulLeft (u : Aˣ) : A ≃L[R] A where
  __ := LinearEquiv.mulLeft R u
  continuous_toFun := continuous_mul_left _
  continuous_invFun := continuous_mul_left _

-- needs PRing
/--
Multiplication on the right by a unit of an F-algebra which is a topological
ring, is a continuous F-linear homeomorphism.
-/
def _root_.ContinuousLinearEquiv.mulRight (u : Aˣ) : A ≃L[R] A where
  __ := LinearEquiv.mulRight R u
  continuous_toFun := continuous_mul_right _
  continuous_invFun := continuous_mul_right _

end needs_PRing

section ring

variable {A : Type*} [Ring A] [TopologicalSpace A]
    [Algebra F A] [FiniteDimensional F A] [IsModuleTopology F A]
    [IsTopologicalRing A] -- can be deduced from previous assumptions but only using F
    [LocallyCompactSpace A] -- can also be proved but only using F
    [MeasurableSpace A] [BorelSpace A]

variable (F) in
lemma algebra_ringHaarChar_eq_ringHaarChar_det (u : Aˣ) :
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

include F in
lemma _root_.IsSimpleRing.ringHaarChar_eq_addEquivAddHaarChar_mulRight (u : Dˣ) :
    ringHaarChar u = addEquivAddHaarChar (ContinuousAddEquiv.mulRight u) := by
  rw [algebra_ringHaarChar_eq_ringHaarChar_det F u]
  rw [IsSimpleRing.mulLeft_det_eq_mulRight_det']
  symm
  exact addEquivAddHaarChar_eq_ringHaarChar_det (ContinuousLinearEquiv.mulRight F u)

end issimplering

end MeasureTheory
