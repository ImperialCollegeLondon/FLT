/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib.LinearAlgebra.Determinant


variable (k D : Type*) [Field k] [Ring D] [Algebra k D]
variable [IsSimpleRing D] [FiniteDimensional k D]

-- left det = right det
#check LinearMap.mulLeft

lemma IsSimpleRing.mulLeft_det_eq_mulRight_det (d : D) :
    (LinearMap.mulLeft k d).det = (LinearMap.mulRight k d).det :=
  sorry --FLT#task010
