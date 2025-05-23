/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.LinearAlgebra.Determinant
import FLT.Mathlib.Algebra.Algebra.Bilinear

variable (k : Type*) [Field k] {D : Type*} [Ring D] [Algebra k D]
variable [IsSimpleRing D] [FiniteDimensional k D]

-- left det = right det
lemma IsSimpleRing.mulLeft_det_eq_mulRight_det (d : D) :
    (LinearMap.mulLeft k d).det = (LinearMap.mulRight k d).det :=
  sorry --FLT#518 -- this is a little tricky. Proof in blueprint.

lemma IsSimpleRing.mulLeft_det_eq_mulRight_det' (d : Dˣ) :
    (LinearEquiv.mulLeft k d).det = (LinearEquiv.mulRight k d).det := by
  ext
  simp [mulLeft_det_eq_mulRight_det]
