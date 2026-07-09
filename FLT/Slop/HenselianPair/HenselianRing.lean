/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import FLT.Slop.HenselianPair.Polynomial

/-!
# Uniqueness of root lifts for `HenselianRing`

Mathlib's `HenselianRing R I` asserts that a simple root of a monic polynomial over `R ⧸ I`
lifts to a root over `R`. This file records that the lift is *unique* in its congruence class,
and specialises the statement to the shape used in Stacks Tag 09XI(5).

## Main results

* `HenselianRing.existsUnique_root_lift_of_isUnit_derivative` — the simple-root lift is unique
  in its congruence class.
* `HenselianRing.existsUnique_root_one_mod_of_sum_range_coeff_mem_X_pow_mul_X_sub_C_one` — the
  Tag 09XI(5) root condition, stated at the `HenselianRing` level of generality.

## References

* [Stacks Project, Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)
-/

@[expose] public section

open Polynomial

variable {R : Type*} [CommRing R]

namespace HenselianRing

/-- A simple root lift for a `HenselianRing` is unique in its congruence class.

This is the Jacobson-radical uniqueness argument for simple roots: if two roots
of `f` are congruent to the same `a₀` modulo `I`, and `f' a₀` is a unit modulo
`I`, then the two roots are equal. No monicity is needed for this uniqueness
statement. -/
theorem root_lift_unique_of_isUnit_derivative {I : Ideal R} [HenselianRing R I]
    {f : R[X]} {a₀ a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b)
    (haI : a - a₀ ∈ I) (hbI : b - a₀ ∈ I)
    (hderiv : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    a = b := by
  exact Polynomial.root_lift_unique_of_isUnit_derivative_of_le_jacobson
    (HenselianRing.jac (R := R) (I := I)) ha hb haI hbI hderiv

/-- A `HenselianRing` has a unique lift of a simple root in the prescribed
congruence class. This is the `∃!` form of `HenselianRing.is_henselian`. -/
theorem existsUnique_root_lift_of_isUnit_derivative {I : Ideal R} [HenselianRing R I]
    {f : R[X]} (hf : f.Monic) (a₀ : R) (hroot : f.eval a₀ ∈ I)
    (hderiv : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    ∃! a : R, f.IsRoot a ∧ a - a₀ ∈ I := by
  obtain ⟨a, ha, haI⟩ := HenselianRing.is_henselian f hf a₀ hroot hderiv
  refine ⟨a, ⟨ha, haI⟩, ?_⟩
  intro b hb
  exact root_lift_unique_of_isUnit_derivative hb.1 ha hb.2 haI hderiv

/-- Uniqueness in the quotient form of the Stacks Tag 09XI root condition for
any `HenselianRing`.

No monicity or existence/lifting hypothesis is needed for this uniqueness
statement; it is just the Jacobson-radical argument bundled with
`HenselianRing.jac`. -/
theorem root_one_mod_unique_of_map_eq_X_pow_mul_X_sub_C_one {I : Ideal R}
    [HenselianRing R I] {f : R[X]} (n : ℕ)
    (hmod : f.map (Ideal.Quotient.mk I) = X ^ n * (X - C (1 : R ⧸ I)))
    {a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b) (haI : a - 1 ∈ I)
    (hbI : b - 1 ∈ I) :
    a = b :=
  Polynomial.root_one_mod_unique_of_map_eq_X_pow_mul_X_sub_C_one_of_le_jacobson
    (HenselianRing.jac (R := R) (I := I)) n hmod ha hb haI hbI

/-- Uniqueness in the coefficientwise-congruence form of the Stacks Tag 09XI
root condition for any `HenselianRing`. -/
theorem root_one_mod_unique_of_forall_coeff_sub_mem_X_pow_mul_X_sub_C_one
    {I : Ideal R} [HenselianRing R I] {f : R[X]} (n : ℕ)
    (hcoeff : ∀ k, (f - X ^ n * (X - C (1 : R))).coeff k ∈ I)
    {a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b) (haI : a - 1 ∈ I)
    (hbI : b - 1 ∈ I) :
    a = b :=
  Polynomial.root_one_mod_unique_of_forall_coeff_sub_mem_X_pow_mul_X_sub_C_one_of_le_jacobson
    (HenselianRing.jac (R := R) (I := I)) n hcoeff ha hb haI hbI

/-- Uniqueness in the perturbation form of the Stacks Tag 09XI root condition
for any `HenselianRing`. -/
theorem root_one_mod_unique_of_forall_coeff_mem_add_X_pow_mul_X_sub_C_one
    {I : Ideal R} [HenselianRing R I] (n : ℕ) {p : R[X]}
    (hp : ∀ k, p.coeff k ∈ I) {a b : R}
    (ha : (X ^ n * (X - C (1 : R)) + p).IsRoot a)
    (hb : (X ^ n * (X - C (1 : R)) + p).IsRoot b) (haI : a - 1 ∈ I)
    (hbI : b - 1 ∈ I) :
    a = b :=
  Polynomial.root_one_mod_unique_of_forall_coeff_mem_add_X_pow_mul_X_sub_C_one_of_le_jacobson
    (HenselianRing.jac (R := R) (I := I)) n hp ha hb haI hbI

/-- Uniqueness in the literal finite-coefficient form of the Stacks Tag 09XI
root condition for any `HenselianRing`. -/
theorem root_one_mod_unique_of_sum_range_coeff_mem_X_pow_mul_X_sub_C_one
    {I : Ideal R} [HenselianRing R I] (n : ℕ) (a : ℕ → R)
    (ha_coeff : ∀ i ≤ n, a i ∈ I) {x y : R}
    (hx : (X ^ n * (X - C (1 : R)) +
      ∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i).IsRoot x)
    (hy : (X ^ n * (X - C (1 : R)) +
      ∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i).IsRoot y)
    (hxI : x - 1 ∈ I) (hyI : y - 1 ∈ I) :
    x = y :=
  Polynomial.root_one_mod_unique_of_sum_range_coeff_mem_X_pow_mul_X_sub_C_one_of_le_jacobson
    (HenselianRing.jac (R := R) (I := I)) n a ha_coeff hx hy hxI hyI

/-- The Stacks Tag 09XI root condition in quotient form for any
`HenselianRing`.

If `f` is monic and `f mod I = X ^ n * (X - 1)`, then `f` has a unique root
congruent to `1` modulo `I`. -/
theorem existsUnique_root_one_mod_of_map_eq_X_pow_mul_X_sub_C_one {I : Ideal R}
    [HenselianRing R I] {f : R[X]} (hf : f.Monic) (n : ℕ)
    (hmod : f.map (Ideal.Quotient.mk I) = X ^ n * (X - C (1 : R ⧸ I))) :
    ∃! a : R, f.IsRoot a ∧ a - 1 ∈ I := by
  apply HenselianRing.existsUnique_root_lift_of_isUnit_derivative hf 1
  · rw [← Ideal.Quotient.eq_zero_iff_mem, ← eval_map_apply, hmod]
    simp [eval_mul, eval_sub]
  · have hderiv : Ideal.Quotient.mk I (f.derivative.eval 1) = (1 : R ⧸ I) := by
      rw [← eval_map_apply, ← derivative_map, hmod]
      simp [derivative_mul, eval_mul, eval_add, eval_sub, eval_X]
    rw [hderiv]
    exact isUnit_one

/-- Coefficientwise-congruence form of the Stacks Tag 09XI root condition for
any `HenselianRing`. -/
theorem existsUnique_root_one_mod_of_forall_coeff_sub_mem_X_pow_mul_X_sub_C_one
    {I : Ideal R} [HenselianRing R I] {f : R[X]} (hf : f.Monic) (n : ℕ)
    (hcoeff : ∀ k, (f - X ^ n * (X - C (1 : R))).coeff k ∈ I) :
    ∃! a : R, f.IsRoot a ∧ a - 1 ∈ I :=
  existsUnique_root_one_mod_of_map_eq_X_pow_mul_X_sub_C_one hf n
    (Polynomial.map_eq_X_pow_mul_X_sub_C_one_of_forall_coeff_sub_mem n hcoeff)

/-- Perturbation form of the Stacks Tag 09XI root condition for any
`HenselianRing`. -/
theorem existsUnique_root_one_mod_of_forall_coeff_mem_add_X_pow_mul_X_sub_C_one
    {I : Ideal R} [HenselianRing R I] (n : ℕ) {p : R[X]}
    (hp : ∀ k, p.coeff k ∈ I) (hf : (X ^ n * (X - C (1 : R)) + p).Monic) :
    ∃! a : R, (X ^ n * (X - C (1 : R)) + p).IsRoot a ∧ a - 1 ∈ I := by
  apply existsUnique_root_one_mod_of_forall_coeff_sub_mem_X_pow_mul_X_sub_C_one hf n
  intro k
  simpa [coeff_sub, coeff_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hp k

/-- Literal finite-coefficient form of the Stacks Tag 09XI root condition for
any `HenselianRing`. -/
theorem existsUnique_root_one_mod_of_sum_range_coeff_mem_X_pow_mul_X_sub_C_one
    {I : Ideal R} [HenselianRing R I] (n : ℕ) (a : ℕ → R)
    (ha : ∀ i ≤ n, a i ∈ I) :
    ∃! x : R,
      (X ^ n * (X - C (1 : R)) +
        ∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i).IsRoot x ∧ x - 1 ∈ I := by
  have hf :
      (X ^ n * (X - C (1 : R)) +
        ∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i : R[X]).Monic :=
    Polynomial.monic_X_pow_mul_X_sub_C_one_add_sum_range_C_mul_X_pow n a
  apply existsUnique_root_one_mod_of_forall_coeff_mem_add_X_pow_mul_X_sub_C_one n ?_ hf
  intro k
  rw [Polynomial.coeff_sum_range_C_mul_X_pow n a k]
  split_ifs with hk
  · exact ha k hk
  · exact I.zero_mem

end HenselianRing
