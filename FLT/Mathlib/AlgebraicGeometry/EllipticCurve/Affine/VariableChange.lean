/-
Copyright (c) 2026 Samuel Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram, Samuel Yin
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import FLT.KnownIn1980s.EllipticCurves.MaybeMathlib

/-!
# Admissible changes of variables on affine points

This file transports affine points and their group law along an admissible change of
Weierstrass coordinates. The coordinate formulas are those of
`WeierstrassCurve.variableChange_def`.
-/

@[expose] public section

namespace WeierstrassCurve.VariableChange

open WeierstrassCurve Affine

universe u

variable {R : Type u} [CommRing R]

/-- The transformed `x`-coordinate under an admissible change of variables. -/
def mapX (C : VariableChange R) (x : R) : R :=
  C.u ^ 2 * x + C.r

/-- The transformed `y`-coordinate under an admissible change of variables. -/
def mapY (C : VariableChange R) (x y : R) : R :=
  C.u ^ 3 * y + C.s * C.u ^ 2 * x + C.t

@[simp]
theorem one_mapX (x : R) : mapX (1 : VariableChange R) x = x := by
  simp [mapX, VariableChange.one_def]

@[simp]
theorem one_mapY (x y : R) : mapY (1 : VariableChange R) x y = y := by
  simp [mapY, VariableChange.one_def]

theorem mul_mapX (C C' : VariableChange R) (x : R) :
    mapX (C * C') x = C'.mapX (C.mapX x) := by
  simp only [mapX, VariableChange.mul_def, Units.val_mul]
  ring

theorem mul_mapY (C C' : VariableChange R) (x y : R) :
    mapY (C * C') x y = C'.mapY (C.mapX x) (C.mapY x y) := by
  simp only [mapX, mapY, VariableChange.mul_def, Units.val_mul]
  ring

theorem mapX_injective (C : VariableChange R) : Function.Injective C.mapX := by
  intro x y h
  let v : Rˣ := C.u ^ 2
  have h' : (v : R) * x = v * y := by
    simp only [mapX] at h
    simpa only [v, Units.val_pow_eq_pow_val] using add_right_cancel h
  calc
    x = (↑(v⁻¹) : R) * (v * x) := (Units.inv_mul_cancel_left v x).symm
    _ = (↑(v⁻¹) : R) * (v * y) := congrArg ((↑(v⁻¹) : R) * ·) h'
    _ = y := Units.inv_mul_cancel_left v y

theorem mapY_left_injective (C : VariableChange R) (x : R) : Function.Injective (C.mapY x) := by
  intro y z h
  let v : Rˣ := C.u ^ 3
  have h' : (v : R) * y = v * z := by
    simp only [mapY] at h
    rw [add_right_cancel_iff, add_right_cancel_iff] at h
    simpa only [v, Units.val_pow_eq_pow_val] using h
  calc
    y = (↑(v⁻¹) : R) * (v * y) := (Units.inv_mul_cancel_left v y).symm
    _ = (↑(v⁻¹) : R) * (v * z) := congrArg ((↑(v⁻¹) : R) * ·) h'
    _ = z := Units.inv_mul_cancel_left v z

@[simp]
theorem inv_mapX_mapX (C : VariableChange R) (x : R) : C⁻¹.mapX (C.mapX x) = x := by
  rw [← C.mul_mapX C⁻¹ x]
  simp

@[simp]
theorem inv_mapY_mapY (C : VariableChange R) (x y : R) :
    C⁻¹.mapY (C.mapX x) (C.mapY x y) = y := by
  rw [← C.mul_mapY C⁻¹ x y]
  simp

@[simp]
theorem mapX_inv_mapX (C : VariableChange R) (x : R) : C.mapX (C⁻¹.mapX x) = x := by
  rw [← C⁻¹.mul_mapX C x]
  simp

@[simp]
theorem mapY_inv_mapY (C : VariableChange R) (x y : R) :
    C.mapY (C⁻¹.mapX x) (C⁻¹.mapY x y) = y := by
  rw [← C⁻¹.mul_mapY C x y]
  simp

variable {F : Type u} [Field F] (C : VariableChange F) (W : WeierstrassCurve F)

/-- The Weierstrass equation is preserved by an admissible change of variables. -/
theorem equation_iff (x y : F) :
    (C • W).toAffine.Equation x y ↔ W.toAffine.Equation (C.mapX x) (C.mapY x y) := by
  rw [Affine.equation_iff', Affine.equation_iff']
  have h : (C.u : F) ^ 6 *
        (y ^ 2 + (C • W).a₁ * x * y + (C • W).a₃ * y -
          (x ^ 3 + (C • W).a₂ * x ^ 2 + (C • W).a₄ * x + (C • W).a₆)) =
      C.mapY x y ^ 2 + W.a₁ * C.mapX x * C.mapY x y + W.a₃ * C.mapY x y -
        (C.mapX x ^ 3 + W.a₂ * C.mapX x ^ 2 + W.a₄ * C.mapX x + W.a₆) := by
    simp only [mapX, mapY, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [← h, mul_eq_zero]
  simp [C.u.ne_zero]

theorem polynomialX_add_smul_polynomialY (x y : F) :
    W.toAffine.polynomialX.evalEval (C.mapX x) (C.mapY x y) +
        C.s * W.toAffine.polynomialY.evalEval (C.mapX x) (C.mapY x y) =
      C.u ^ 4 * (C • W).toAffine.polynomialX.evalEval x y := by
  simp only [Affine.evalEval_polynomialX, Affine.evalEval_polynomialY, mapX, mapY,
    variableChange_a₁, variableChange_a₂, variableChange_a₄, Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem polynomialY_apply (x y : F) :
    W.toAffine.polynomialY.evalEval (C.mapX x) (C.mapY x y) =
      C.u ^ 3 * (C • W).toAffine.polynomialY.evalEval x y := by
  simp only [Affine.evalEval_polynomialY, mapX, mapY, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

/-- Nonsingularity is preserved by an admissible change of variables. -/
theorem nonsingular_iff (x y : F) :
    (C • W).toAffine.Nonsingular x y ↔
      W.toAffine.Nonsingular (C.mapX x) (C.mapY x y) := by
  rw [Affine.Nonsingular, Affine.Nonsingular, C.equation_iff W]
  refine and_congr_right' ?_
  constructor
  · intro h
    by_cases hoY : W.toAffine.polynomialY.evalEval (C.mapX x) (C.mapY x y) ≠ 0
    · exact Or.inr hoY
    · left
      intro hoX
      have hnY : (C • W).toAffine.polynomialY.evalEval x y = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 3 C.u.ne_zero)
        rw [← C.polynomialY_apply W x y]
        exact not_ne_iff.mp hoY
      have hnX : (C • W).toAffine.polynomialX.evalEval x y = 0 := by
        apply (mul_eq_zero.mp ?_).resolve_left (pow_ne_zero 4 C.u.ne_zero)
        rw [← C.polynomialX_add_smul_polynomialY W x y, hoX, not_ne_iff.mp hoY]
        simp
      exact h.elim (· hnX) (· hnY)
  · intro h
    by_cases hnY : (C • W).toAffine.polynomialY.evalEval x y ≠ 0
    · exact Or.inr hnY
    · left
      intro hnX
      have hoY : W.toAffine.polynomialY.evalEval (C.mapX x) (C.mapY x y) = 0 := by
        rw [C.polynomialY_apply W x y, not_ne_iff.mp hnY, mul_zero]
      have hoX : W.toAffine.polynomialX.evalEval (C.mapX x) (C.mapY x y) = 0 := by
        have hrel := C.polynomialX_add_smul_polynomialY W x y
        rw [hoY, mul_zero, add_zero, hnX, mul_zero] at hrel
        exact hrel
      exact h.elim (· hoX) (· hoY)

theorem negY_apply (x y : F) :
    W.toAffine.negY (C.mapX x) (C.mapY x y) =
      C.mapY x ((C • W).toAffine.negY x y) := by
  simp only [Affine.negY, mapX, mapY, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

private theorem slope_apply_of_X_ne_aux [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (hx : x₁ ≠ x₂) :
    W.toAffine.slope (C.mapX x₁) (C.mapX x₂) (C.mapY x₁ y₁) (C.mapY x₂ y₂) =
      C.u * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hx' : C.mapX x₁ ≠ C.mapX x₂ := C.mapX_injective.ne hx
  rw [Affine.slope_of_X_ne hx', Affine.slope_of_X_ne hx]
  have hx₀ : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
  have hx₀' : C.mapX x₁ - C.mapX x₂ ≠ 0 := sub_ne_zero.mpr hx'
  have hx₀'' : (C.u : F) ^ 2 * x₁ - C.u ^ 2 * x₂ ≠ 0 := by
    simpa only [mapX, add_sub_add_right_eq_sub] using hx₀'
  simp only [mapX, mapY]
  field_simp [hx₀, hx₀'']
  ring

private theorem slope_apply_of_X_eq_aux [DecidableEq F] {x y : F}
    (hy : y ≠ (C • W).toAffine.negY x y) :
    W.toAffine.slope (C.mapX x) (C.mapX x) (C.mapY x y) (C.mapY x y) =
      C.u * (C • W).toAffine.slope x x y y + C.s := by
  have hy' : C.mapY x y ≠ W.toAffine.negY (C.mapX x) (C.mapY x y) := by
    intro h
    rw [C.negY_apply W x y] at h
    exact hy (C.mapY_left_injective x h)
  rw [Affine.slope_of_Y_ne_eq_evalEval rfl hy',
    Affine.slope_of_Y_ne_eq_evalEval rfl hy]
  have hnew : (C • W).toAffine.polynomialY.evalEval x y ≠ 0 := by
    rw [Affine.evalEval_polynomialY]
    contrapose! hy
    rw [Affine.negY]
    linear_combination hy
  have hold : W.toAffine.polynomialY.evalEval (C.mapX x) (C.mapY x y) ≠ 0 := by
    rw [C.polynomialY_apply W x y]
    exact mul_ne_zero (pow_ne_zero 3 C.u.ne_zero) hnew
  rw [C.polynomialY_apply W x y]
  field_simp [hnew, hold]
  calc
    -W.toAffine.polynomialX.evalEval (C.mapX x) (C.mapY x y) =
        -(C.u ^ 4 * (C • W).toAffine.polynomialX.evalEval x y -
          C.s * W.toAffine.polynomialY.evalEval (C.mapX x) (C.mapY x y)) := by
      congr 1
      linear_combination C.polynomialX_add_smul_polynomialY W x y
    _ = C.u ^ 3 * (-(C.u * (C • W).toAffine.polynomialX.evalEval x y) +
        (C • W).toAffine.polynomialY.evalEval x y * C.s) := by
      linear_combination C.s * C.polynomialY_apply W x y

theorem slope_apply [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope (C.mapX x₁) (C.mapX x₂) (C.mapY x₁ y₁) (C.mapY x₂ y₂) =
      C.u * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ (C • W).toAffine.negY x₂ y₂ := fun h ↦ hxy ⟨hx, h⟩
    have hyy := Affine.Y_eq_of_Y_ne h₁ h₂ hx hy
    subst x₂
    subst y₂
    exact slope_apply_of_X_eq_aux C W hy
  · exact slope_apply_of_X_ne_aux C W hx

theorem addX_apply (x₁ x₂ ℓ : F) :
    W.toAffine.addX (C.mapX x₁) (C.mapX x₂) (C.u * ℓ + C.s) =
      C.mapX ((C • W).toAffine.addX x₁ x₂ ℓ) := by
  simp only [Affine.addX, mapX, variableChange_a₁, variableChange_a₂,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

theorem addY_apply (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.addY (C.mapX x₁) (C.mapX x₂) (C.mapY x₁ y₁) (C.u * ℓ + C.s) =
      C.mapY ((C • W).toAffine.addX x₁ x₂ ℓ)
        ((C • W).toAffine.addY x₁ x₂ y₁ ℓ) := by
  simp only [Affine.addY, Affine.negY, Affine.negAddY, Affine.addX, mapX, mapY,
    variableChange_a₁, variableChange_a₂, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field_simp
  ring

/-- The equivalence on affine points induced by an admissible change of variables. -/
noncomputable def pointEquiv : (C • W).toAffine.Point ≃ W.toAffine.Point where
  toFun
    | .zero => .zero
    | .some x y h => .some (C.mapX x) (C.mapY x y) ((C.nonsingular_iff W x y).mp h)
  invFun
    | .zero => .zero
    | .some x y h => .some (C⁻¹.mapX x) (C⁻¹.mapY x y) <| by
        have h' : (C⁻¹ • (C • W)).toAffine.Nonsingular x y := by
          simpa using h
        exact (C⁻¹.nonsingular_iff (C • W) x y).mp h'
  left_inv := by
    intro P
    cases P with
    | zero => rfl
    | some x y h => simp
  right_inv := by
    intro P
    cases P with
    | zero => rfl
    | some x y h => simp

@[simp]
theorem pointEquiv_zero : C.pointEquiv W 0 = 0 := by
  rfl

@[simp]
theorem pointEquiv_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    C.pointEquiv W (.some x y h) =
      .some (C.mapX x) (C.mapY x y) ((C.nonsingular_iff W x y).mp h) := by
  rfl

theorem pointEquiv_map_add [DecidableEq F] (P Q : (C • W).toAffine.Point) :
    C.pointEquiv W (P + Q) = C.pointEquiv W P + C.pointEquiv W Q := by
  have hvertical (x₁ x₂ y₁ y₂ : F) :
      (C.mapX x₁ = C.mapX x₂ ∧
          C.mapY x₁ y₁ = W.toAffine.negY (C.mapX x₂) (C.mapY x₂ y₂)) ↔
        (x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂) := by
    constructor
    · rintro ⟨hx, hy⟩
      obtain rfl := C.mapX_injective hx
      rw [C.negY_apply W x₁ y₂] at hy
      exact ⟨rfl, C.mapY_left_injective x₁ hy⟩
    · rintro ⟨rfl, hy⟩
      refine ⟨rfl, ?_⟩
      rw [C.negY_apply W x₁ y₂]
      exact congrArg (C.mapY x₁) hy
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => rfl
    | some x₂ y₂ h₂ =>
      by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
      · have hxy' := (hvertical x₁ x₂ y₁ y₂).mpr hxy
        rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, C.pointEquiv_zero W]
        simp only [C.pointEquiv_some W]
        rw [Affine.Point.add_of_Y_eq hxy'.1 hxy'.2]
      · rw [Affine.Point.add_some hxy]
        simp only [C.pointEquiv_some W]
        rw [Affine.Point.add_some (mt (hvertical x₁ x₂ y₁ y₂).mp hxy),
          Affine.Point.some.injEq]
        have hslope := C.slope_apply W h₁.1 h₂.1 hxy
        constructor <;> rw [hslope]
        · exact (C.addX_apply W _ _ _).symm
        · exact (C.addY_apply W _ _ _ _).symm

/-- The additive equivalence on affine points induced by an admissible change of variables. -/
noncomputable def pointAddEquiv [DecidableEq F] : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  AddEquiv.mk' (C.pointEquiv W) (C.pointEquiv_map_add W)

@[simp]
theorem pointAddEquiv_apply [DecidableEq F] (P : (C • W).toAffine.Point) :
    C.pointAddEquiv W P = C.pointEquiv W P := by
  rfl

@[simp]
theorem pointAddEquiv_symm_apply [DecidableEq F] (P : W.toAffine.Point) :
    (C.pointAddEquiv W).symm P = (C.pointEquiv W).symm P := by
  rfl

@[simp]
theorem pointEquiv_symm_zero : (C.pointEquiv W).symm 0 = 0 := by
  rfl

@[simp]
theorem pointEquiv_symm_some {x y : F} (h : W.toAffine.Nonsingular x y)
    (h' : (C • W).toAffine.Nonsingular (C⁻¹.mapX x) (C⁻¹.mapY x y)) :
    (C.pointEquiv W).symm (.some x y h) = .some (C⁻¹.mapX x) (C⁻¹.mapY x y) h' := by
  rfl

end WeierstrassCurve.VariableChange

namespace WeierstrassCurve

open VariableChange

variable {R : Type*} [CommRing R]

/-- The transformed `x`-coordinate commutes with any ring homomorphism. -/
theorem map_mapX {A : Type*} [CommRing A] (C : VariableChange R) (φ : R →+* A) (x : R) :
    φ (C.mapX x) = (C.map φ).mapX (φ x) := by
  simp [VariableChange.mapX, VariableChange.map]

/-- The transformed `y`-coordinate commutes with any ring homomorphism. -/
theorem map_mapY {A : Type*} [CommRing A] (C : VariableChange R) (φ : R →+* A) (x y : R) :
    φ (C.mapY x y) = (C.map φ).mapY (φ x) (φ y) := by
  simp [VariableChange.mapY, VariableChange.map]

/-- The negation change of variables fixes the `x`-coordinate. -/
@[simp]
theorem negVariableChange_mapX (W : WeierstrassCurve R) (x : R) :
    W.negVariableChange.mapX x = x := by
  simp [VariableChange.mapX, negVariableChange]

/-- The negation change of variables acts on the `y`-coordinate as the negation
`Affine.negY` of the curve: it induces negation on affine points. -/
@[simp]
theorem negVariableChange_mapY (W : WeierstrassCurve R) (x y : R) :
    W.negVariableChange.mapY x y = W.toAffine.negY x y := by
  simp [VariableChange.mapY, negVariableChange, Affine.negY]
  ring

end WeierstrassCurve
