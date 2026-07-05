/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Defs

Material destined for Mathlib.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]

/-- The invertible diagonal matrix associated to a vector of units (the diagonal entries).
-/
def diagonal (d : n → Rˣ) : GL n R :=
  ⟨.diagonal (d ·), .diagonal <| fun i ↦ ((d i)⁻¹ : Rˣ),
    by simp, by simp⟩

@[simp]
lemma val_diagonal (d : n → Rˣ) :
    (diagonal d).1 = .diagonal (d ·) := rfl

@[simp]
lemma diagonal_one : diagonal (n := n) (R := R) 1 = 1 := by
  ext; simp [Matrix.GeneralLinearGroup.diagonal]

namespace GL2

-- **TODO** This might have just landed in mathlib as an AddChar?
/-- The unipotent matrix element `!![1, t; 0, 1]`. -/
noncomputable def unipotent (t : R) : GL (Fin 2) R :=
  ⟨!![1, t; 0, 1], !![1, -t; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

lemma unipotent_def (t : R) :
    (unipotent t : Matrix (Fin 2) (Fin 2) R) = !![1, t; 0, 1] := rfl

@[simp] lemma unipotent_zero_zero (t : R) : unipotent t 0 0 = 1 := rfl
@[simp] lemma unipotent_zero_one (t : R) : unipotent t 0 1 = t := rfl
@[simp] lemma unipotent_one_zero (t : R) : unipotent t 1 0 = 0 := rfl
@[simp] lemma unipotent_one_one (t : R) : unipotent t 1 1 = 1 := rfl

@[simp]
lemma unipotent_inv (t : R) :
    (unipotent t)⁻¹ = unipotent (-t) := by ext1; rfl

lemma unipotent_mul (t₁ t₂ : R) :
    unipotent t₂ * unipotent t₁ = unipotent (t₁ + t₂) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [unipotent_def]

end GL2

end Matrix.GeneralLinearGroup
