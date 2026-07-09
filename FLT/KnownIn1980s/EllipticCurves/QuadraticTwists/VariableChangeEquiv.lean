/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!

# Isomorphism of point groups induced by a change of variables

Mathlib's affine `Point` API provides the group homomorphism `WeierstrassCurve.Affine.Point.map`
induced by a change of the base field (for a *fixed* Weierstrass curve), but not the isomorphism of
Mordell–Weil groups induced by an admissible change of variables between two *different* curves.
This file supplies that: for `C : VariableChange F` and an elliptic curve `W` over a field `F`, the
admissible change of variables `(x, y) ↦ (u²x + r, u³y + u²sx + t)` gives a group isomorphism
`WeierstrassCurve.Affine.pointEquivVariableChange : (C • W).Point ≃+ W.Point`.

## Main definitions

* `WeierstrassCurve.Affine.Point.mapVariableChange` : the group homomorphism `(C • W).Point →+
  W.Point`, `(x, y) ↦ (u²x + r, u³y + u²sx + t)`.
* `WeierstrassCurve.Affine.pointEquivVariableChange` : the group isomorphism `(C • W).Point ≃+
  W.Point`, with inverse coming from `C⁻¹`.

-/

@[expose] public section

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-! ### Transformation of the group-law formulae under a change of variables

Throughout, the change of variables carries a point `(x, y)` of `C • W` to the point
`(u²x + r, u³y + u²sx + t)` of `W`. -/

lemma variableChange_negY (x y : F) :
    W.toAffine.negY ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) ^ 3 * (C • W).toAffine.negY x y + (C.u : F) ^ 2 * C.s * x + C.t := by
  simp only [negY, variableChange_a₁, variableChange_a₃, Units.val_inv_eq_inv_val]
  field

lemma variableChange_addX (x₁ x₂ ℓ : F) :
    W.toAffine.addX ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  simp only [addX, variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
  field

lemma variableChange_negAddY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.negAddY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.negAddY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [negAddY, addX, variableChange_a₁, variableChange_a₂, Units.val_inv_eq_inv_val]
  field

lemma variableChange_addY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.addY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  rw [addY, addY, variableChange_negAddY, variableChange_addX, variableChange_negY]

lemma variableChange_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  by_cases hx : x₁ = x₂
  · have hy : y₁ ≠ (C • W).toAffine.negY x₂ y₂ := fun h ↦ hxy ⟨hx, h⟩
    obtain rfl := hx
    obtain rfl := Y_eq_of_Y_ne h₁ h₂ rfl hy
    have hΦy : (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t
        ≠ W.toAffine.negY ((C.u : F) ^ 2 * x₁ + C.r)
            ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) := by
      rw [variableChange_negY]
      intro h
      exact hy (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination h))
    rw [W.toAffine.slope_of_Y_ne rfl hΦy, (C • W).toAffine.slope_of_Y_ne rfl hy,
      ← mul_div_assoc, div_add' _ _ _ (sub_ne_zero.mpr hy),
      div_eq_div_iff (sub_ne_zero.mpr hΦy) (sub_ne_zero.mpr hy)]
    simp only [negY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      Units.val_inv_eq_inv_val]
    field
  · have hΦx : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r := by
      simp only [ne_eq, add_left_inj, mul_right_inj' (pow_ne_zero 2 hu)]
      exact hx
    rw [W.toAffine.slope_of_X_ne hΦx, (C • W).toAffine.slope_of_X_ne hx]
    have h1 := sub_ne_zero.mpr hΦx
    have h2 := sub_ne_zero.mpr hx
    field

/-- A point `(x, y)` lies on `C • W` if and only if `(u²x + r, u³y + u²sx + t)` lies on `W`: the
change of variables scales the Weierstrass polynomial by `u⁶`. -/
lemma variableChange_equation (x y : F) :
    W.toAffine.Equation ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Equation x y := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rw [equation_iff', equation_iff']
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, Units.val_inv_eq_inv_val]
  field_simp
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> linear_combination h

/-! ### The induced isomorphism of point groups -/

variable [W.IsElliptic]

/-- The underlying map `(C • W).Point → W.Point` of the change of variables, sending `0` to `0` and
`(x, y)` to `(u²x + r, u³y + u²sx + t)`. -/
noncomputable def Point.mapVariableChangeFun :
    (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some ((C.u : F) ^ 2 * x + C.r)
      ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      (equation_iff_nonsingular.mp
        ((variableChange_equation W C x y).mpr (equation_iff_nonsingular.mpr h)))

@[simp] lemma Point.mapVariableChangeFun_zero :
    Point.mapVariableChangeFun W C 0 = 0 := rfl

lemma Point.mapVariableChangeFun_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    Point.mapVariableChangeFun W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          (equation_iff_nonsingular.mp
            ((variableChange_equation W C x y).mpr (equation_iff_nonsingular.mpr h))) := rfl

lemma Point.some_eq_some (V : WeierstrassCurve F) {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : V.toAffine.Nonsingular x₁ y₁} {h₂ : V.toAffine.Nonsingular x₂ y₂} :
    (Point.some x₁ y₁ h₁ : V.toAffine.Point) = Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

lemma Point.mapVariableChangeFun_injective :
    Function.Injective (Point.mapVariableChangeFun W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [Point.mapVariableChangeFun] at h
  · simp [Point.mapVariableChangeFun] at h
  · rw [Point.mapVariableChangeFun_some, Point.mapVariableChangeFun_some] at h
    injection h with hX hY
    have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
    exact Point.some_eq_some (C • W) hx
      (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx))

lemma Point.mapVariableChangeFun_surjective :
    Function.Surjective (Point.mapVariableChangeFun W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨X, Y, h⟩)
  · exact ⟨0, rfl⟩
  · have hX : (C.u : F) ^ 2 * ((C.u : F)⁻¹ ^ 2 * (X - C.r)) + C.r = X := by field
    have hY : (C.u : F) ^ 3 * ((C.u : F)⁻¹ ^ 3 * (Y - C.s * (X - C.r) - C.t))
        + (C.u : F) ^ 2 * C.s * ((C.u : F)⁻¹ ^ 2 * (X - C.r)) + C.t = Y := by field
    refine ⟨.some ((C.u : F)⁻¹ ^ 2 * (X - C.r)) ((C.u : F)⁻¹ ^ 3 * (Y - C.s * (X - C.r) - C.t))
      (equation_iff_nonsingular.mp ((variableChange_equation W C _ _).mp
        (by rw [hX, hY]; exact equation_iff_nonsingular.mpr h))), ?_⟩
    rw [Point.mapVariableChangeFun_some]
    exact Point.some_eq_some W hX hY

variable [DecidableEq F]

/-- The group homomorphism `(C • W).Point →+ W.Point` induced by the admissible change of variables
`(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
noncomputable def Point.mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := Point.mapVariableChangeFun W C
  map_zero' := rfl
  map_add' := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [Point.mapVariableChangeFun_some]
    have e₁ : (C • W).toAffine.Equation x₁ y₁ := equation_iff_nonsingular.mpr h₁
    have e₂ : (C • W).toAffine.Equation x₂ y₂ := equation_iff_nonsingular.mpr h₂
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [Point.add_of_Y_eq hxy.1 hxy.2, Point.mapVariableChangeFun_zero]
      refine (Point.add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · have hxy' : ¬((C.u : F) ^ 2 * x₁ + C.r = (C.u : F) ^ 2 * x₂ + C.r ∧
          (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t = W.toAffine.negY
            ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)) := by
        rintro ⟨hX, hY⟩
        have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
        subst hx
        rw [variableChange_negY] at hY
        exact hxy ⟨rfl, mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY)⟩
      rw [Point.add_some hxy, Point.mapVariableChangeFun_some, Point.add_some hxy']
      simp only [variableChange_slope W C e₁ e₂ hxy, variableChange_addX, variableChange_addY]

/-- The group isomorphism `(C • W).Point ≃+ W.Point` induced by the admissible change of
variables `(x, y) ↦ (u²x + r, u³y + u²sx + t)`. -/
noncomputable def pointEquivVariableChange :
    (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  AddEquiv.ofBijective (Point.mapVariableChange W C)
    ⟨Point.mapVariableChangeFun_injective W C, Point.mapVariableChangeFun_surjective W C⟩

lemma pointEquivVariableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    pointEquivVariableChange W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          (equation_iff_nonsingular.mp
            ((variableChange_equation W C x y).mpr (equation_iff_nonsingular.mpr h))) := rfl

/-- Transport of the affine point group along an equality of Weierstrass curves. -/
def Point.equivOfEq {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.Point ≃+ V'.toAffine.Point := by
  subst h; exact AddEquiv.refl _

@[simp] lemma Point.equivOfEq_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    Point.equivOfEq h (Point.some x y hns) = Point.some x y (h ▸ hns) := by
  subst h; rfl

end WeierstrassCurve.Affine

end
