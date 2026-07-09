/-
Copyright (c) 2026 Akhil Mathew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Akhil Mathew
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Algebra.Polynomial.Identities
public import Mathlib.RingTheory.Henselian

/-!
# Polynomial helpers for Henselian pairs

Uniqueness of simple-root lifts under only the Jacobson-radical hypothesis, together with
small computational lemmas about the polynomial
`X ^ n * (X - 1) + ∑ i ∈ range (n + 1), a i * X ^ i` appearing in Stacks Tag 09XI(5).

## Main results

* `Polynomial.root_lift_unique_of_isUnit_derivative_of_le_jacobson` — uniqueness of a simple
  root in its congruence class, using only `I ≤ Jac(R)`.
* `Polynomial.coeff_sum_range_C_mul_X_pow`, `Polynomial.natDegree_sum_range_C_mul_X_pow_le`,
  `Polynomial.monic_X_pow_mul_X_sub_C_one_add_sum_range_C_mul_X_pow` — coefficient, degree and
  monicity of the Tag 09XI(5) polynomial.
* `Polynomial.root_one_mod_unique_of_sum_range_coeff_mem_X_pow_mul_X_sub_C_one_of_le_jacobson`
  and variants — uniqueness of the root congruent to `1` modulo `I`.

## References

* [Stacks Project, Tag 09XI](https://stacks.math.columbia.edu/tag/09XI)
-/

@[expose] public section

open Polynomial

variable {R : Type*} [CommRing R]

namespace Polynomial

/-- If two roots of a polynomial are congruent to the same element modulo an
ideal contained in the Jacobson radical, and the derivative at that element is a
unit modulo the ideal, then the roots are equal.

This is the Jacobson-radical uniqueness argument for simple roots. It is the
uniqueness half of Hensel's lemma and does not use the existence/lifting
property. -/
theorem root_lift_unique_of_isUnit_derivative_of_le_jacobson {I : Ideal R}
    (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) {f : R[X]} {a₀ a b : R}
    (ha : f.IsRoot a) (hb : f.IsRoot b) (haI : a - a₀ ∈ I) (hbI : b - a₀ ∈ I)
    (hderiv : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀))) :
    a = b := by
  let d : R := a - b
  have hdI : d ∈ I := by
    have hsum : d = (a - a₀) - (b - a₀) := by ring
    rw [hsum]
    exact I.sub_mem haI hbI
  obtain ⟨k, hk⟩ := binomExpansion f b d
  have hroot_eq : f.eval (b + d) = 0 := by
    have hbd : b + d = a := by simp [d]
    rw [hbd]
    exact ha
  have hmul : (f.derivative.eval b + k * d) * d = 0 := by
    have hk0 := hk
    rw [hroot_eq, hb, zero_add] at hk0
    have : f.derivative.eval b * d + k * d ^ 2 = 0 := hk0.symm
    convert this using 1
    ring
  have hbcong : b ≡ a₀ [SMOD I] := SModEq.sub_mem.mpr hbI
  have hderivdiff : f.derivative.eval b - f.derivative.eval a₀ ∈ I :=
    SModEq.sub_mem.mp (hbcong.eval f.derivative)
  have hunit_factor : IsUnit (f.derivative.eval b + k * d) := by
    haveI : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I hI
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    have heq_deriv :
        Ideal.Quotient.mk I (f.derivative.eval b) =
          Ideal.Quotient.mk I (f.derivative.eval a₀) :=
      Ideal.Quotient.eq.mpr hderivdiff
    have hkd : Ideal.Quotient.mk I (k * d) = 0 := by
      have hdq : Ideal.Quotient.mk I d = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hdI
      rw [map_mul, hdq, mul_zero]
    rw [map_add, heq_deriv, hkd, add_zero]
    exact hderiv
  have hd0 : d = 0 := (IsUnit.mul_right_eq_zero hunit_factor).mp hmul
  exact sub_eq_zero.mp hd0

/-- If the coefficients of `f - X ^ n * (X - 1)` all lie in `I`, then `f`
reduces modulo `I` to `X ^ n * (X - 1)`. -/
theorem map_eq_X_pow_mul_X_sub_C_one_of_forall_coeff_sub_mem {I : Ideal R}
    {f : R[X]} (n : ℕ)
    (hcoeff : ∀ k, (f - X ^ n * (X - C (1 : R))).coeff k ∈ I) :
    f.map (Ideal.Quotient.mk I) = X ^ n * (X - C (1 : R ⧸ I)) := by
  have hmap :
      f.map (Ideal.Quotient.mk I) =
        (X ^ n * (X - C (1 : R))).map (Ideal.Quotient.mk I) := by
    ext k
    have hk : Ideal.Quotient.mk I
        ((f - X ^ n * (X - C (1 : R))).coeff k) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (hcoeff k)
    have hk' : Ideal.Quotient.mk I (f.coeff k) -
        Ideal.Quotient.mk I ((X ^ n * (X - C (1 : R))).coeff k) = 0 := by
      simpa [coeff_sub, map_sub] using hk
    rw [coeff_map, coeff_map]
    exact sub_eq_zero.mp hk'
  simpa using hmap

/-- Coefficients of the finite polynomial `∑ i = 0..n, aᵢ X^i`. -/
theorem coeff_sum_range_C_mul_X_pow (n : ℕ) (a : ℕ → R) (k : ℕ) :
    (∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i : R[X]).coeff k =
      if k ≤ n then a k else 0 := by
  by_cases hk : k ≤ n
  · have hcoeff :
        (∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i : R[X]).coeff k = a k := by
      rw [finsetSum_coeff]
      simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range,
        Nat.lt_succ_iff]
      simp [hk]
    rw [hcoeff, if_pos hk]
  · have hcoeff :
        (∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i : R[X]).coeff k = 0 := by
      rw [finsetSum_coeff]
      simp only [coeff_C_mul_X_pow]
      apply Finset.sum_eq_zero
      intro i hi
      have hi_le : i ≤ n := Nat.lt_succ_iff.mp (by simpa [Finset.mem_range] using hi)
      have hki : k ≠ i :=
        ne_of_gt (lt_of_le_of_lt hi_le (Nat.lt_of_not_ge hk))
      simp [hki]
    rw [hcoeff, if_neg hk]

/-- The finite polynomial `∑ i = 0..n, aᵢ X^i` has degree at most `n`. -/
theorem natDegree_sum_range_C_mul_X_pow_le (n : ℕ) (a : ℕ → R) :
    (∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i : R[X]).natDegree ≤ n := by
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro i hi
  exact (natDegree_C_mul_X_pow_le (a i) i).trans
    (Nat.lt_succ_iff.mp (by simpa [Finset.mem_range] using hi))

/-- The literal Stacks Tag 09XI(5) polynomial
`X ^ n * (X - 1) + aₙ X ^ n + ... + a₀` is monic. -/
theorem monic_X_pow_mul_X_sub_C_one_add_sum_range_C_mul_X_pow (n : ℕ) (a : ℕ → R) :
    (X ^ n * (X - C (1 : R)) +
      ∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i : R[X]).Monic := by
  rcases subsingleton_or_nontrivial R with _ | _
  · rw [Monic.def]
    exact Subsingleton.elim _ _
  · have hbase :
        IsMonicOfDegree (X ^ n * (X - C (1 : R)) : R[X]) (n + 1) := by
      simpa [sub_eq_add_neg, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (isMonicOfDegree_X_pow R n).mul (isMonicOfDegree_X_add_one (-1 : R))
    exact (hbase.add_right
      (Nat.lt_succ_iff.mpr (natDegree_sum_range_C_mul_X_pow_le n a))).monic

/-- Jacobson-only uniqueness in the quotient form of the Stacks Tag 09XI root
condition.

If `I ≤ Jac(R)`, `f ≡ X ^ n * (X - 1) mod I`, and two roots of `f` are
congruent to `1` modulo `I`, then the roots are equal. -/
theorem root_one_mod_unique_of_map_eq_X_pow_mul_X_sub_C_one_of_le_jacobson
    {I : Ideal R} (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) {f : R[X]} (n : ℕ)
    (hmod : f.map (Ideal.Quotient.mk I) = X ^ n * (X - C (1 : R ⧸ I)))
    {a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b) (haI : a - 1 ∈ I)
    (hbI : b - 1 ∈ I) :
    a = b := by
  apply root_lift_unique_of_isUnit_derivative_of_le_jacobson hI ha hb haI hbI
  rw [← eval_map_apply, ← derivative_map, hmod]
  simp [derivative_mul, eval_mul, eval_add, eval_sub, eval_X]

/-- Jacobson-only uniqueness in the coefficientwise-congruence form of the
Stacks Tag 09XI root condition. -/
theorem root_one_mod_unique_of_forall_coeff_sub_mem_X_pow_mul_X_sub_C_one_of_le_jacobson
    {I : Ideal R} (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) {f : R[X]} (n : ℕ)
    (hcoeff : ∀ k, (f - X ^ n * (X - C (1 : R))).coeff k ∈ I)
    {a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b) (haI : a - 1 ∈ I)
    (hbI : b - 1 ∈ I) :
    a = b :=
  root_one_mod_unique_of_map_eq_X_pow_mul_X_sub_C_one_of_le_jacobson hI n
    (map_eq_X_pow_mul_X_sub_C_one_of_forall_coeff_sub_mem n hcoeff) ha hb haI hbI

/-- Jacobson-only uniqueness in the perturbation form of the Stacks Tag 09XI
root condition. -/
theorem root_one_mod_unique_of_forall_coeff_mem_add_X_pow_mul_X_sub_C_one_of_le_jacobson
    {I : Ideal R} (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) (n : ℕ) {p : R[X]}
    (hp : ∀ k, p.coeff k ∈ I) {a b : R}
    (ha : (X ^ n * (X - C (1 : R)) + p).IsRoot a)
    (hb : (X ^ n * (X - C (1 : R)) + p).IsRoot b) (haI : a - 1 ∈ I)
    (hbI : b - 1 ∈ I) :
    a = b := by
  apply root_one_mod_unique_of_forall_coeff_sub_mem_X_pow_mul_X_sub_C_one_of_le_jacobson
    hI n ?_ ha hb haI hbI
  intro k
  simpa [coeff_sub, coeff_add, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hp k

/-- Jacobson-only uniqueness in the literal finite-coefficient form of the
Stacks Tag 09XI root condition.

This is the uniqueness assertion in Stacks Tag 09XI(5): if
`f = X ^ n * (X - 1) + aₙ X ^ n + ... + a₀` with all `aᵢ ∈ I`, then any two
roots of `f` in `1 + I` are equal. -/
theorem root_one_mod_unique_of_sum_range_coeff_mem_X_pow_mul_X_sub_C_one_of_le_jacobson
    {I : Ideal R} (hI : I ≤ Ideal.jacobson (⊥ : Ideal R)) (n : ℕ) (a : ℕ → R)
    (ha_coeff : ∀ i ≤ n, a i ∈ I) {x y : R}
    (hx : (X ^ n * (X - C (1 : R)) +
      ∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i).IsRoot x)
    (hy : (X ^ n * (X - C (1 : R)) +
      ∑ i ∈ Finset.range (n + 1), C (a i) * X ^ i).IsRoot y)
    (hxI : x - 1 ∈ I) (hyI : y - 1 ∈ I) :
    x = y := by
  apply root_one_mod_unique_of_forall_coeff_mem_add_X_pow_mul_X_sub_C_one_of_le_jacobson
    hI n ?_ hx hy hxI hyI
  intro k
  rw [coeff_sum_range_C_mul_X_pow n a k]
  split_ifs with hk
  · exact ha_coeff k hk
  · exact I.zero_mem

end Polynomial
