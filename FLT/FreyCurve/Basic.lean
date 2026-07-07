/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone
-/
module

public import FLT.FreyCurve.FreyPackage
/-!

# The Frey curve associated to a Frey package

Recall that a Frey package is a triple of nonzero integers `a`, `b`, `c`
and a prime `p` satisfying some conditions, most notably
that `a^p+b^p=c^p`.

In this file we define the elliptic curve `E : Y^2=X(X-a^p)(X+b^p)`
associated to the Frey package.

All the results in Section 4.1
of Serre's 1987 Duke paper [Serre] apply to this elliptic
curve `Y^2=X(X-a^p)(X+b^p)`.

# Main definition

* `FreyPackage.freyCurve` : The Frey curve associated to a Frey package.

# Main theorem

* `FreyCurve.j_valuation_of_bad_prime` : The q-adic valuation of the j-invariant of the Frey
curve is a multiple of q if 2 < q is a prime of bad reduction.

-/

@[expose] public section

namespace FreyPackage

/-- The Weierstrass curve over `ℤ` associated to a Frey package. The conditions imposed
upon a Frey package guarantee that the running hypotheses in
Section 4.1 of [Serre] all hold. We put the curve into the form where the
equation is semistable at 2, rather than the usual `Y^2=X(X-a^p)(X+b^p)` form.
The change of variables is `X=4x` and `Y=8y+4x`, and then divide through by 64.
The fact that p is odd, a=3 mod 4 and b is even are enough to show that
this new curve still has coefficients in `ℤ`.
-/
def freyCurveInt (P : FreyPackage) : WeierstrassCurve ℤ where
  a₁ := 1
  -- Note that the numerator of a₂ is a multiple of 4
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16 -- Note: numerator is multiple of 16
  a₆ := 0

/-- The elliptic curve over `ℚ` associated to a Frey package. The conditions imposed
upon a Frey package guarantee that the running hypotheses in
Section 4.1 of [Serre] all hold. We put the curve into the form where the
equation is semistable at 2, rather than the usual `Y^2=X(X-a^p)(X+b^p)` form.
The change of variables is `X=4x` and `Y=8y+4x`, and then divide through by 64. -/
def freyCurve (P : FreyPackage) : WeierstrassCurve ℚ where
  a₁ := 1
  -- a₂ is an integer because of the congruences assumed e.g. P.ha4
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16 -- this is also an integer
  a₆ := 0

end FreyPackage

namespace FreyCurve

open FreyPackage WeierstrassCurve

theorem map (P : FreyPackage) : (freyCurveInt P).map (algebraMap ℤ ℚ) = freyCurve P := by
  have two_dvd_b : 2 ∣ P.b := (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).1 P.hb2
  ext
  · rfl
  · change (((P.b ^ P.p - 1 - P.a ^ P.p) / 4 : ℤ) : ℚ) = (P.b ^ P.p - 1 - P.a ^ P.p) / 4
    rw [Rat.intCast_div]
    · norm_cast
    · rw [sub_sub]
      apply Int.dvd_sub
      · calc
          (4 : ℤ) = 2 ^ 2     := by norm_num
          _       ∣ P.b ^ 2   := pow_dvd_pow_of_dvd two_dvd_b 2
          _       ∣ P.b ^ P.p := pow_dvd_pow P.b (by linarith [P.hp5])
      · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1
        push_cast
        rw [P.ha4, show (3 : ZMod 4) = -1 from rfl, neg_one_pow_eq_ite, if_neg]
        · norm_num
        · rw [Nat.Prime.even_iff P.pp]
          linarith [P.hp5]
  · rfl
  · change ((-(P.a ^ P.p) * (P.b ^ P.p) / 16 : ℤ) : ℚ) = -(P.a ^ P.p) * (P.b ^ P.p) / 16
    rw [Rat.intCast_div]
    · norm_cast
    · calc
        (16 : ℤ) = 2 ^ 4     := by norm_num
        _        ∣ P.b ^ 4   := pow_dvd_pow_of_dvd two_dvd_b 4
        _        ∣ P.b ^ P.p := pow_dvd_pow P.b (by linarith [P.hp5])
        _        ∣ _         := Int.dvd_mul_left _ _
  · rfl

lemma Δ (P : FreyPackage) : P.freyCurve.Δ = (P.a*P.b*P.c)^(2*P.p) / 2 ^ 8 := by
  trans (P.a ^ P.p) ^ 2 * (P.b ^ P.p) ^ 2 * (P.c ^ P.p) ^ 2 / 2 ^ 8
  · field_simp
    norm_cast
    simp [← P.hFLT, WeierstrassCurve.Δ, freyCurve, b₂, b₄, b₆, b₈]
    ring
  · simp [← mul_pow, ← pow_mul, mul_comm 2]

instance (P : FreyPackage) : WeierstrassCurve.IsElliptic (freyCurve P) where
  isUnit := by
    rw [FreyCurve.Δ, isUnit_iff_ne_zero]
    apply div_ne_zero
    · norm_cast
      exact pow_ne_zero _ <| mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0
    · norm_num

lemma b₂ (P : FreyPackage) :
    P.freyCurve.b₂ = P.b ^ P.p - P.a ^ P.p := by
  simp [freyCurve, WeierstrassCurve.b₂]
  ring

lemma b₄ (P : FreyPackage) :
    P.freyCurve.b₄ = - (P.a * P.b) ^ P.p / 8 := by
  simp [freyCurve, WeierstrassCurve.b₄]
  ring

lemma c₄ (P : FreyPackage) :
    P.freyCurve.c₄ = (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2 := by
  simp [b₂, b₄, WeierstrassCurve.c₄]
  ring

lemma c₄' (P : FreyPackage) :
    P.freyCurve.c₄ = P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p := by
  rw [c₄]
  rw_mod_cast [pow_mul', ← hFLT]
  ring

lemma Δ'inv (P : FreyPackage) :
    (↑(P.freyCurve.Δ'⁻¹) : ℚ) = 2 ^ 8 / (P.a*P.b*P.c)^(2*P.p) := by
  simp [Δ]

lemma j (P : FreyPackage) :
    P.freyCurve.j = 2^8*(P.c^(2*P.p)-(P.a*P.b)^P.p) ^ 3 /(P.a*P.b*P.c)^(2*P.p) := by
  rw [mul_div_right_comm, WeierstrassCurve.j, FreyCurve.Δ'inv, FreyCurve.c₄']

private lemma j_pos_aux (a b : ℤ) (hb : b ≠ 0) : 0 < (a + b) ^ 2 - a * b := by
  rify
  calc
    (0 : ℝ) < (a ^ 2 + (a + b) ^ 2 + b ^ 2) / 2 := by positivity
    _ = (a + b) ^ 2 - a * b := by ring

/-- The q-adic valuation of the j-invariant of the Frey curve is a multiple of p if 2 < q is
a prime of bad reduction. -/
lemma j_valuation_of_bad_prime (P : FreyPackage) {q : ℕ} (hqPrime : q.Prime)
    (hqbad : (q : ℤ) ∣ P.a * P.b * P.c) (hqodd : 2 < q) :
    (P.p : ℤ) ∣ padicValRat q P.freyCurve.j := by
  have := Fact.mk hqPrime
  have hqPrime' := Nat.prime_iff_prime_int.mp hqPrime
  have h₀ : ((P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p) ^ 3 : ℚ) ≠ 0 := by
    rw_mod_cast [pow_mul', ← P.hFLT, mul_pow]
    exact pow_ne_zero _ <| ne_of_gt <| j_pos_aux _ _ (pow_ne_zero _ P.hb0)
  have h₁ : P.a * P.b * P.c ≠ 0 := mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0
  rw [FreyCurve.j, padicValRat.div (mul_ne_zero (by norm_num) h₀) (pow_ne_zero _ (mod_cast h₁)),
    padicValRat.mul (by norm_num) h₀, padicValRat.pow, ← Nat.cast_two,
    ← padicValRat_of_nat, padicValNat_primes hqodd.ne', Nat.cast_zero, mul_zero, zero_add]
  have : ¬ (q : ℤ) ∣ (P.c^(2*P.p)-(P.a*P.b)^P.p) ^ 3 := by
    rw [hqPrime'.dvd_pow_iff_dvd three_ne_zero]
    have hq' : Xor ((q : ℤ) ∣ P.a * P.b) ((q : ℤ) ∣ P.c) := by
      rw [xor_iff_not_iff, iff_iff_and_or_not_and_not]
      rintro (⟨hab, hc⟩ | ⟨hab, hc⟩)
      · rw [hqPrime'.dvd_mul] at hab
        apply hqPrime'.not_dvd_one
        cases hab with
        | inl ha => rw [← P.hgcdac]; exact dvd_gcd ha hc
        | inr hb => rw [← P.hgcdbc]; exact dvd_gcd hb hc
      · rw [hqPrime'.dvd_mul] at hqbad
        exact hqbad.rec hab hc
    have h2p0 := mul_ne_zero two_ne_zero P.hp0
    cases hq' with
    | inl h =>
      rw [dvd_sub_left (dvd_pow h.1 P.hp0), hqPrime'.dvd_pow_iff_dvd h2p0]
      exact h.2
    | inr h =>
      rw [dvd_sub_right (dvd_pow h.1 h2p0), hqPrime'.dvd_pow_iff_dvd P.hp0]
      exact h.2
  norm_cast
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd this, Nat.cast_zero, zero_sub,
    Int.cast_pow, padicValRat.pow, dvd_neg, Nat.cast_mul]
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

end FreyCurve
