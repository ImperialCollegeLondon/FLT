/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.FieldTheory.Separable
public import FLT.Mathlib.Algebra.Polynomial.Splits

/-!
# Separability and splitting criteria for quadratic polynomials

Proposed new Mathlib file `Mathlib.Algebra.Polynomial.QuadraticDiscriminant`: a quadratic
over a field is separable iff its discriminant is nonzero, and splits iff its discriminant is a square (in
characteristic 2: iff its Artin–Schreier invariant is in the image of `z ↦ z² + z`).
-/

@[expose] public section

namespace Polynomial

/-- The derivative of the quadratic `a X² + b X + c` is `2 a X + b`. -/
theorem derivative_quadratic {R : Type*} [CommSemiring R] (a b c : R) :
    derivative (C a * X ^ 2 + C b * X + C c) = 2 * C a * X + C b := by
  simp only [derivative_add, derivative_mul, derivative_C, derivative_X_pow, derivative_X,
    zero_mul, zero_add, add_zero, mul_one, Nat.cast_ofNat, map_ofNat]
  ring

/-- The Bézout-type identity `(P')² - 4 a · P = C (b² - 4 a c)` for the quadratic
`P = a X² + b X + c`: the discriminant is an explicit combination of `P` and its derivative. -/
theorem sq_derivative_quadratic_sub_mul {R : Type*} [CommRing R] (a b c : R) :
    derivative (C a * X ^ 2 + C b * X + C c) ^ 2
      - 4 * C a * (C a * X ^ 2 + C b * X + C c) = C (b ^ 2 - 4 * a * c) := by
  rw [derivative_quadratic]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- A quadratic polynomial `a X² + b X + c` (with `a ≠ 0`) over a field is separable exactly when
its discriminant `b² - 4 a c` is nonzero. The `←` direction holds in every characteristic: by the
Bézout identity `sq_derivative_quadratic_sub_mul`, a nonzero (hence invertible) discriminant
exhibits `P` and `P'` as coprime. The `→` direction argues that if the discriminant vanishes then
`P ∣ (P')²`, forcing the coprimality witness `P` to be a unit, contradicting `deg P = 2`. -/
theorem separable_quadratic_iff {k : Type*} [Field k] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Separable ↔ b ^ 2 - 4 * a * c ≠ 0 := by
  set P := C a * X ^ 2 + C b * X + C c with hP
  have hid : derivative P ^ 2 - 4 * C a * P = C (b ^ 2 - 4 * a * c) :=
    sq_derivative_quadratic_sub_mul a b c
  constructor
  · intro hsep hdisc
    rw [hdisc, map_zero] at hid
    have hdvd : P ∣ derivative P ^ 2 := ⟨4 * C a, by linear_combination hid⟩
    exact not_isUnit_of_natDegree_pos P (by rw [hP, natDegree_quadratic ha]; norm_num)
      (((separable_def P).mp hsep).pow_right.isUnit_of_dvd' dvd_rfl hdvd)
  · intro hdisc
    rw [separable_def]
    have hdinv : C (b ^ 2 - 4 * a * c)⁻¹ * C (b ^ 2 - 4 * a * c) = 1 := by
      rw [← C_mul, inv_mul_cancel₀ hdisc, C_1]
    exact ⟨-(C (b ^ 2 - 4 * a * c)⁻¹ * 4 * C a), C (b ^ 2 - 4 * a * c)⁻¹ * derivative P,
      by linear_combination C (b ^ 2 - 4 * a * c)⁻¹ * hid + hdinv⟩

/-- A quadratic `a X² + b X + c` (`a ≠ 0`) over a field splits exactly when it has a root
(`Splits.of_natDegree_le_two_of_isRoot`). This is the characteristic-free core of the split
criterion. -/
theorem splits_quadratic_iff_exists_root {k : Type*} [Field k] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ ∃ x, a * x ^ 2 + b * x + c = 0 := by
  set p := C a * X ^ 2 + C b * X + C c with hp
  have hdeg : p.natDegree = 2 := natDegree_quadratic ha
  have hp0 : p ≠ 0 := fun h ↦ by simp [h] at hdeg
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := hs.exists_eval_eq_zero (by simp [degree_eq_natDegree hp0, hdeg])
    exact ⟨x, by simpa [hp] using hx⟩
  · rintro ⟨x, hx⟩
    refine Splits.of_natDegree_le_two_of_isRoot hdeg.le (x := x) ?_
    simp [hp, IsRoot]
    linear_combination hx

/-- Over a field of characteristic `≠ 2`, a quadratic `a X² + b X + c` (with `a ≠ 0`) *splits*
exactly when its discriminant `b² - 4 a c` is a square: it splits iff it has a root
(`splits_quadratic_iff_exists_root`), and completing the square
(`discrim_eq_sq_of_quadratic_eq_zero` / `exists_quadratic_eq_zero`) matches roots with square roots
of the discriminant. This is the split-multiplicative-reduction criterion; compare
`separable_quadratic_iff` (separable ↔ discriminant nonzero). -/
theorem splits_quadratic_iff {k : Type*} [Field k] [NeZero (2 : k)] {a b c : k} (ha : a ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ IsSquare (discrim a b c) := by
  rw [splits_quadratic_iff_exists_root ha]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨2 * a * x + b, by rw [discrim_eq_sq_of_quadratic_eq_zero (a := a) (b := b) (c := c)
      (x := x) (by linear_combination hx)]; ring⟩
  · rintro ⟨s, hs⟩
    obtain ⟨x, hx⟩ := exists_quadratic_eq_zero ha ⟨s, by rw [hs]⟩
    exact ⟨x, by linear_combination hx⟩

/-- Over a field of characteristic `2`, a *separable* quadratic `a X² + b X + c` (`a, b ≠ 0`)
splits exactly when its Artin–Schreier invariant `a c / b²` lies in the image of `z ↦ z² + z`,
written division-free as `∃ z, b² (z² + z) = a c`. (Substitute `z = a x / b` in a root `x`.) In
residue characteristic `2` this replaces the square-class criterion `splits_quadratic_iff`, since
there `b² - 4 a c = b²`, so separability already forces `b ≠ 0`. -/
theorem splits_quadratic_iff_of_two_eq_zero {k : Type*} [Field k] (h2 : (2 : k) = 0)
    {a b c : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    (C a * X ^ 2 + C b * X + C c).Splits ↔ ∃ z, b ^ 2 * (z ^ 2 + z) = a * c := by
  rw [splits_quadratic_iff_exists_root ha]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨a * x / b, ?_⟩
    field_simp
    linear_combination hx - c * h2
  · rintro ⟨z, hz⟩
    refine ⟨b * z / a, ?_⟩
    field_simp
    linear_combination hz + a * c * h2

end Polynomial

end
