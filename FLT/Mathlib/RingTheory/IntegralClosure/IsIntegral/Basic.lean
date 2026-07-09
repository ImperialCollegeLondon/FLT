/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# Integrality from explicit monic relations

Material for `Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic`: elements satisfying an
explicit monic quadratic or quartic relation are integral.
-/

@[expose] public section

/-- An element satisfying a monic quadratic relation with coefficients in `A` is integral. -/
theorem isIntegral_of_sq_add_mul_add_eq_zero {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {x : B} (a b : A) (h : x ^ 2 + algebraMap A B a * x + algebraMap A B b = 0) :
    _root_.IsIntegral A x := by
  refine ⟨Polynomial.X ^ 2 + (Polynomial.C a * Polynomial.X + Polynomial.C b), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    compute_degree!
  · rw [← Polynomial.aeval_def]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    linear_combination h

/-- An element satisfying a monic quartic relation (with no cubic term) with coefficients in `A`
is integral. -/
theorem isIntegral_of_pow_four_add_eq_zero {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {x : B} (a b c : A)
    (h : x ^ 4 + algebraMap A B a * x ^ 2 + algebraMap A B b * x + algebraMap A B c = 0) :
    _root_.IsIntegral A x := by
  refine ⟨Polynomial.X ^ 4 + (Polynomial.C a * Polynomial.X ^ 2 + Polynomial.C b * Polynomial.X
    + Polynomial.C c), ?_, ?_⟩
  · apply Polynomial.monic_X_pow_add
    compute_degree!
  · rw [← Polynomial.aeval_def]
    simp only [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    linear_combination h

end
