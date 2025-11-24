/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]

/-- The invertible diagonal matrix associated to a vector of units (the diagonal entries).
-/
def diagonal (d : n → Rˣ) : GL n R :=
  ⟨.diagonal <| fun i ↦ d i, .diagonal <| fun i ↦ ((d i)⁻¹ : Rˣ),
    by simp, by simp⟩

namespace GL2

-- **TODO** This might have just landed in mathlib as an AddChar?
/-- The unipotent matrix element `!![1, t; 0, 1]`. -/
noncomputable def unipotent (t : R) : GL (Fin 2) R :=
  letI detInv : Invertible !![1, t; 0, 1].det :=
  { invOf := 1,
    invOf_mul_self :=
      by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero],
    mul_invOf_self :=
      by simp only [Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero] }
  Matrix.unitOfDetInvertible !![1, t; 0, 1]

lemma unipotent_def (t : R) :
    (unipotent t : Matrix (Fin 2) (Fin 2) R) = !![1, t; 0, 1] := by
  simp [unipotent, Matrix.unitOfDetInvertible]

lemma unipotent_inv (t : R) :
    (unipotent t)⁻¹ = unipotent (-t) := by
  ext; simp [unipotent_def, Matrix.inv_def]

lemma unipotent_mul (t₁ t₂ : R) :
    (unipotent t₂) * (unipotent t₁) = unipotent (t₁ + t₂) := by
  ext i j; fin_cases i; all_goals fin_cases j
  all_goals simp [unipotent_def]

end GL2

end Matrix.GeneralLinearGroup
