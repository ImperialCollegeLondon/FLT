import FLT.KnownIn1980s.EllipticCurves.TateCurveConstruction

/-!
# Low-order checks for the Tate curve identity

This file checks the identity in `TateCurve.weierstrass_equation` modulo `X ^ 3`,
where `X` is the power series variable, by comparing the coefficients of `1`, `X`
and `X ^ 2`.
-/

open scoped PowerSeries

open scoped ArithmeticFunction.sigma

noncomputable section

namespace TateCurve

abbrev K := RatFunc ℚ

local notation "u" => (RatFunc.X : K)

private def x0 : K := u / (1 - u) ^ 2
private def x1 : K := u + u⁻¹ - 2
private def x2 : K := x1 + 2 * (u ^ 2 + u⁻¹ ^ 2 - 2)

private def y0 : K := u ^ 2 / (1 - u) ^ 3
private def y1 : K := 1 - u⁻¹
private def y2 : K := y1 + (u ^ 2 - 3 * u⁻¹ ^ 2 + 2)

private lemma polynomial_one_sub_X_ne_zero : (1 : Polynomial ℚ) - Polynomial.X ≠ 0 := by
  intro h
  have h0 := congr_arg (fun p : Polynomial ℚ => p.coeff 1) h
  norm_num [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X] at h0

private lemma one_sub_u_ne_zero : (1 : K) - u ≠ 0 := by
  rw [← RatFunc.algebraMap_X]
  rw [← map_one (algebraMap (Polynomial ℚ) K), ← map_sub]
  exact fun h => polynomial_one_sub_X_ne_zero
    ((IsFractionRing.injective (Polynomial ℚ) K) (by simpa using h))

private lemma coeff_s (k n : ℕ) : (PowerSeries.coeff n) (s k) = ((σ k) n : K) := by
  simp [s]

private lemma natCast_eq_C (m : ℕ) : (m : K⟦X⟧) = PowerSeries.C (m : K) := by
  rw [show (m : K⟦X⟧) = algebraMap K K⟦X⟧ (m : K) by
    exact (map_natCast (algebraMap K K⟦X⟧) m).symm]
  rw [PowerSeries.algebraMap_apply]
  simp

private lemma intCast_eq_C (z : ℤ) : (z : K⟦X⟧) = PowerSeries.C (z : K) := by
  rw [show (z : K⟦X⟧) = algebraMap K K⟦X⟧ (z : K) by
    exact (map_intCast (algebraMap K K⟦X⟧) z).symm]
  rw [PowerSeries.algebraMap_apply]
  simp

private lemma coeff_five_mul_s (k n : ℕ) :
    (PowerSeries.coeff n) ((5 : K⟦X⟧) * s k) = (5 : K) * ((σ k) n : K) := by
  rw [show (5 : K⟦X⟧) = PowerSeries.C (5 : K) by exact natCast_eq_C 5]
  rw [PowerSeries.coeff_C_mul, coeff_s]

private lemma coeff_seven_mul_s (k n : ℕ) :
    (PowerSeries.coeff n) ((7 : K⟦X⟧) * s k) = (7 : K) * ((σ k) n : K) := by
  rw [show (7 : K⟦X⟧) = PowerSeries.C (7 : K) by exact natCast_eq_C 7]
  rw [PowerSeries.coeff_C_mul, coeff_s]

private lemma coeff_neg_five_mul_s (k n : ℕ) :
    (PowerSeries.coeff n) ((-5 : K⟦X⟧) * s k) = (-5 : K) * ((σ k) n : K) := by
  rw [show (-5 : K⟦X⟧) = PowerSeries.C (-5 : K) by exact intCast_eq_C (-5)]
  rw [PowerSeries.coeff_C_mul, coeff_s]

private lemma coeff_X_0 : (PowerSeries.coeff 0) X = x0 := by
  simp [X, x0]

private lemma coeff_X_1 : (PowerSeries.coeff 1) X = x1 := by
  simp [X, x1]

private lemma coeff_X_2 : (PowerSeries.coeff 2) X = x2 := by
  have hdiv : (2 : ℕ).divisors = ({1, 2} : Finset ℕ) := by decide
  simp [X, x2, x1, hdiv]

private lemma coeff_Y_0 : (PowerSeries.coeff 0) Y = y0 := by
  simp [Y, y0]

private lemma coeff_Y_1 : (PowerSeries.coeff 1) Y = y1 := by
  simp [Y, y1]
  ring_nf

private lemma coeff_Y_2 : (PowerSeries.coeff 2) Y = y2 := by
  have hdiv : (2 : ℕ).divisors = ({1, 2} : Finset ℕ) := by decide
  simp [Y, y2, y1, hdiv]
  ring_nf

private lemma coeff_a₄ (n : ℕ) : (PowerSeries.coeff n) a₄ = (-5 : K) * ((σ 3) n : K) := by
  rw [a₄, coeff_neg_five_mul_s]

private lemma coeff_a₆ (n : ℕ) :
    (PowerSeries.coeff n) a₆ =
      (12 : K)⁻¹ * -((5 : K) * ((σ 3) n : K) + (7 : K) * ((σ 5) n : K)) := by
  rw [a₆]
  simp only [PowerSeries.coeff_smul, map_neg, map_add]
  rw [coeff_five_mul_s, coeff_seven_mul_s]
  ring

private lemma coeff_a₄_0 : (PowerSeries.coeff 0) a₄ = (0 : K) := by
  rw [coeff_a₄]
  simp

private lemma coeff_a₄_1 : (PowerSeries.coeff 1) a₄ = (-5 : K) := by
  rw [coeff_a₄]
  simp [ArithmeticFunction.sigma_apply]

private lemma coeff_a₄_2 : (PowerSeries.coeff 2) a₄ = (-45 : K) := by
  have hdiv : (2 : ℕ).divisors = ({1, 2} : Finset ℕ) := by decide
  rw [coeff_a₄]
  simp [ArithmeticFunction.sigma_apply, hdiv]
  norm_num

private lemma coeff_a₆_0 : (PowerSeries.coeff 0) a₆ = (0 : K) := by
  rw [coeff_a₆]
  simp

private lemma coeff_a₆_1 : (PowerSeries.coeff 1) a₆ = (-1 : K) := by
  rw [coeff_a₆]
  simp [ArithmeticFunction.sigma_apply]
  norm_num

private lemma coeff_a₆_2 : (PowerSeries.coeff 2) a₆ = (-23 : K) := by
  have hdiv : (2 : ℕ).divisors = ({1, 2} : Finset ℕ) := by decide
  rw [coeff_a₆]
  simp [ArithmeticFunction.sigma_apply, hdiv]
  norm_num

private lemma coeff_weierstrass_0 :
    (PowerSeries.coeff 0) (Y ^ 2 + X * Y) =
      (PowerSeries.coeff 0) (X ^ 3 + a₄ * X + a₆) := by
  simp [X, Y, a₄, a₆, s]
  field_simp
  ring_nf

private lemma coeff_weierstrass_1 :
    (PowerSeries.coeff 1) (Y ^ 2 + X * Y) =
      (PowerSeries.coeff 1) (X ^ 3 + a₄ * X + a₆) := by
  have hanti0 : Finset.HasAntidiagonal.antidiagonal 0 = ({(0, 0)} : Finset (ℕ × ℕ)) := by
    decide
  have hanti1 : Finset.HasAntidiagonal.antidiagonal 1 =
      ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by
    decide
  simp [pow_succ, PowerSeries.coeff_mul, hanti0, hanti1, coeff_X_0, coeff_X_1,
    coeff_Y_0, coeff_Y_1, coeff_a₄_0, coeff_a₄_1, coeff_a₆_1]
  simp [x0, x1, y0, y1]
  field_simp [RatFunc.X_ne_zero, one_sub_u_ne_zero]
  ring_nf

private lemma coeff_weierstrass_2 :
    (PowerSeries.coeff 2) (Y ^ 2 + X * Y) =
      (PowerSeries.coeff 2) (X ^ 3 + a₄ * X + a₆) := by
  have hanti0 : Finset.HasAntidiagonal.antidiagonal 0 = ({(0, 0)} : Finset (ℕ × ℕ)) := by
    decide
  have hanti1 : Finset.HasAntidiagonal.antidiagonal 1 =
      ({(0, 1), (1, 0)} : Finset (ℕ × ℕ)) := by
    decide
  have hanti2 : Finset.HasAntidiagonal.antidiagonal 2 =
      ({(0, 2), (1, 1), (2, 0)} : Finset (ℕ × ℕ)) := by
    decide
  simp [pow_succ, PowerSeries.coeff_mul, hanti0, hanti1, hanti2, coeff_X_0, coeff_X_1,
    coeff_X_2, coeff_Y_0, coeff_Y_1, coeff_Y_2, coeff_a₄_0, coeff_a₄_1,
    coeff_a₄_2, coeff_a₆_2]
  simp [x0, x1, x2, y0, y1, y2]
  field_simp [RatFunc.X_ne_zero, one_sub_u_ne_zero]
  ring_nf

/-- The identity `Y ^ 2 + X * Y = X ^ 3 + a₄ * X + a₆` holds modulo `X ^ 3`. -/
theorem weierstrass_equation_mod_X3 (n : ℕ) (hn : n < 3) :
    (PowerSeries.coeff n) (Y ^ 2 + X * Y) =
      (PowerSeries.coeff n) (X ^ 3 + a₄ * X + a₆) := by
  interval_cases n
  · exact coeff_weierstrass_0
  · exact coeff_weierstrass_1
  · exact coeff_weierstrass_2

end TateCurve
