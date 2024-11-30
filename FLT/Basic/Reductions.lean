import Mathlib.Data.PNat.Basic
import Mathlib.NumberTheory.FLT.Four
import Mathlib.NumberTheory.FLT.Three
import Mathlib.Tactic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.SimpleModule
import FLT.EllipticCurve.Torsion


/-!

# Preliminary reductions of FLT

This file proves some of the key results which reduce Fermat's Last Theorem
to Mazur's theorem and the Wiles/Taylor--Wiles theorem.

# Main definitions

* `FreyPackage` : A Frey Package is the data of nonzero coprime integers
$(a,b,c)$ and a prime $p \geq 5$ such that $a^p+b^p=c^p$ and furthermore
such that $a$ is 3 mod 4 and $b$ is 0 mod 2.

The motivation behind this definition is that then all the results in Section 4.1
of Serre's paper [Serre] apply to the elliptic curve $Y^2=X(X-a^p)(X+b^p).$

# Main theorems

* `FLT.FreyPackage.of_not_FermatLastTheorem_p_ge_5` : A counterexample
     to `FermatLastTheorem` with $p \geq 5$ gives a Frey Package.
* `FLT.FreyPackage.false`: There is no Frey Package.

The first of these theorems is not too hard; the second is the main content
of the proof of Fermat's Last Theorem.
-/

/-!

We start by reducing the version of Fermat's Last Theorem for positive naturals to
Lean's version `FermatLastTheorem` of the theorem.

-/

/-- Fermat's Last Theorem as stated in mathlib (a statement `FermatLastTheorem` about naturals)
implies Fermat's Last Theorem stated in terms of positive integers. -/
theorem PNat.pow_add_pow_ne_pow_of_FermatLastTheorem :
    FermatLastTheorem → ∀ (a b c : ℕ+) (n : ℕ) (_ : n > 2),
    a ^ n + b ^ n ≠ c ^ n := by
  intro h₁ a b c n h₂
  specialize h₁ n h₂ a b c (by simp) (by simp) (by simp)
  assumption_mod_cast

namespace FLT

/-- If Fermat's Last Theorem is true for primes `p ≥ 5`, then FLT is true. -/
lemma of_p_ge_5 (H : ∀ p ≥ 5, p.Prime → FermatLastTheoremFor p) : FermatLastTheorem := by
  apply FermatLastTheorem.of_odd_primes
  intro p pp p_odd
  if hp5 : 5 ≤ p then
    exact H _ hp5 pp
  else
    have hp2 := pp.two_le
    interval_cases p
    · contradiction
    · exact fermatLastTheoremThree
    · contradiction

/-

We continue with the reduction of Fermat's Last Theorem.

-/

/--
A *Frey Package* is a 4-tuple (a,b,c,p) of integers
satisfying $a^p+b^p=c^p$ and some other inequalities
and congruences. These facts guarantee that all of
the all the results in section 4.1 of Serre's paper [serre]
apply to the curve $Y^2=X(X-a^p)(X+b^p).$
-/
structure FreyPackage where
  a : ℤ
  b : ℤ
  c : ℤ
  ha0 : a ≠ 0
  hb0 : b ≠ 0
  hc0 : c ≠ 0
  p : ℕ
  pp : Nat.Prime p
  hp5 : 5 ≤ p
  hFLT : a ^ p + b ^ p = c ^ p
  hgcdab : gcd a b = 1 -- same as saying a,b,c pairwise coprime
  ha4 : (a : ZMod 4) = 3
  hb2 : (b : ZMod 2) = 0

namespace FreyPackage

lemma hppos (P : FreyPackage) : 0 < P.p := lt_of_lt_of_le (by omega) P.hp5
lemma hp0 (P : FreyPackage) : P.p ≠ 0 := P.hppos.ne'

lemma gcdab_eq_gcdac {a b c : ℤ} {p : ℕ} (hp : 0 < p) (h : a ^ p + b ^ p = c ^ p) :
    gcd a b = gcd a c := by
  have foo : gcd a b ∣ gcd a c := by
    apply dvd_gcd (gcd_dvd_left a b)
    rw [← Int.pow_dvd_pow_iff hp.ne', ← h]
    apply dvd_add <;> rw [Int.pow_dvd_pow_iff hp.ne']
    · exact gcd_dvd_left a b
    · exact gcd_dvd_right a b
  have bar : gcd a c ∣ gcd a b := by
    apply dvd_gcd (gcd_dvd_left a c)
    have h2 : b ^ p = c ^ p - a ^ p := eq_sub_of_add_eq' h
    rw [← Int.pow_dvd_pow_iff hp.ne', h2]
    apply dvd_add
    · rw [Int.pow_dvd_pow_iff hp.ne']
      exact gcd_dvd_right a c
    · rw [dvd_neg, Int.pow_dvd_pow_iff hp.ne']
      exact gcd_dvd_left a c
  change _ ∣ (Int.gcd a c : ℤ) at foo
  apply Int.ofNat_dvd.1 at bar
  apply Int.ofNat_dvd.1 at foo
  exact congr_arg ((↑) : ℕ → ℤ) <| Nat.dvd_antisymm foo bar

lemma hgcdac (P : FreyPackage) : gcd P.a P.c = 1 := by
  rw [← gcdab_eq_gcdac P.hppos P.hFLT, P.hgcdab]

lemma hgcdbc (P : FreyPackage) : gcd P.b P.c = 1 :=  by
  rw [← gcdab_eq_gcdac P.hppos, gcd_comm, P.hgcdab]
  rw [add_comm]
  exact P.hFLT

-- for mathlib? I thought I needed it but I got around it
-- lemma Int.dvd_div_iff {a b c : ℤ} (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b := by
--   constructor
--   · rintro ⟨x, hx⟩
--     use x
--     rcases hbc with ⟨y, rfl⟩
--     by_cases hc : c = 0
--     · simp [hc]
--     · rw [Int.mul_ediv_cancel_left _ hc] at hx
--       rw [hx, mul_assoc]
--   · rintro ⟨x, rfl⟩
--     rw [mul_assoc]
--     by_cases hc : c = 0
--     · simp [hc]
--     · simp [Int.mul_ediv_cancel_left _ hc]

/-- Given a counterexample a^p+b^p=c^p to Fermat's Last Theorem with p>=5, there exists a Frey package. -/
lemma of_not_FermatLastTheorem_p_ge_5 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    {p : ℕ} (pp : p.Prime) (hp5 : 5 ≤ p) (H : a^p + b^p = c^p) : Nonempty FreyPackage := by
  have p_odd := pp.odd_of_ne_two (by omega)
  -- First, show that we can make a,b coprime by dividing through by gcd a b
  have ⟨a, b, c, a0, b0, c0, ab, H⟩ :
      ∃ (a b c : ℤ), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ Int.gcd a b = 1 ∧ a^p + b^p = c^p := by
    obtain ⟨d, a', b', d0, cop, a_eq, b_eq⟩ :=
      Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left b ha)
    simp only [a_eq, mul_pow, b_eq] at H
    rw [← add_mul, mul_comm] at H
    obtain ⟨c', rfl⟩ := (Int.pow_dvd_pow_iff pp.ne_zero).1 ⟨_, H.symm⟩
    rw [mul_pow] at H
    have a0' := left_ne_zero_of_mul (a_eq ▸ ha)
    have b0' := left_ne_zero_of_mul (b_eq ▸ hb)
    have c0' := right_ne_zero_of_mul hc
    exact ⟨a', b', c', a0', b0', c0', cop, mul_left_cancel₀ (pow_ne_zero _ (mod_cast d0.ne')) H⟩
  -- Then show that WLOG we can take b to be even,
  -- because at least one of a,b,c is even and we can permute if needed
  have ⟨a, b, c, a0, b0, c0, ab, eb, H⟩ :
      ∃ (a b c : ℤ), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ Int.gcd a b = 1 ∧ Even b ∧ a^p + b^p = c^p := by
    if eb : Even b then
      exact ⟨a, b, c, a0, b0, c0, ab, eb, H⟩
    else if ea : Even a then
      exact ⟨b, a, c, b0, a0, c0, Int.gcd_comm a b ▸ ab, ea, by rwa [add_comm]⟩
    else
      refine ⟨a, -c, -b, a0, neg_ne_zero.2 c0, neg_ne_zero.2 b0, ?_, even_neg.2 ?_, ?_⟩
      · refine Int.gcd_neg.trans (.trans (.symm ?_) ab)
        exact Nat.cast_inj.1 (gcdab_eq_gcdac pp.pos H)
      · refine ((Int.even_pow (n := p)).1 (H.symm ▸ Int.even_add.2 (iff_of_false ?_ ?_))).1
        · exact fun h => ea (Int.even_pow.1 h).1
        · exact fun h => eb (Int.even_pow.1 h).1
      · simp [p_odd.neg_pow, ← H]
  -- We can ensure additionally that a ≡ 3 [ZMOD 4] by negating everything if necessary
  have ⟨a, b, c, ha0, hb0, hc0, ab, ha3, eb, hFLT⟩ :
      ∃ (a b c : ℤ), a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ Int.gcd a b = 1 ∧
        a ≡ 3 [ZMOD 4] ∧ Even b ∧ a^p + b^p = c^p := by
    -- Since b is even, a cannot also be even
    have a_odd' : ∀ {i}, a ≡ i [ZMOD 4] → ¬2 ∣ i := fun ai ei => by
      have ea := (dvd_sub_right ei).1 (.trans (by decide) (Int.modEq_iff_dvd.1 ai))
      simpa (config := {decide := true}) [gcd, ab] using dvd_gcd ea (even_iff_two_dvd.1 eb)
    mod_cases a_mod : a % 4
    · cases a_odd' a_mod (by decide)
    · exact ⟨-a, -b, -c, neg_ne_zero.2 a0, neg_ne_zero.2 b0, neg_ne_zero.2 c0,
        by rwa [Int.neg_gcd, Int.gcd_neg], a_mod.neg, eb.neg,
        by simp [p_odd.neg_pow, ← H, add_comm]⟩
    · cases a_odd' a_mod (by decide)
    · exact ⟨a, b, c, a0, b0, c0, ab, a_mod, eb, H⟩
  -- Build the Frey package from the assumptions
  exact ⟨{
    a, b, c, ha0, hb0, hc0, p, pp, hp5, hFLT
    hgcdab := by simp [gcd, ab]
    ha4 := (ZMod.intCast_eq_intCast_iff ..).2 ha3
    hb2 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).2 (even_iff_two_dvd.1 eb)
  }⟩

/-- The elliptic curve associated to a Frey package. The conditions imposed
upon a Frey package guarantee that the running hypotheses in
Section 4.1 of [Serre] all hold. We put the curve into the form where the
equation is semistable at 2, rather than the usual `Y^2=X(X-a^p)(X+b^p)` form.
The change of variables is `X=4x` and `Y=8y+4x`, and then divide through by 64. -/
def FreyCurve (P : FreyPackage) : WeierstrassCurve ℚ where
  a₁ := 1
  -- a₂ is (or should be) an integer because of the congruences assumed e.g. P.ha4
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16 -- this should also be an integer
  a₆ := 0

lemma FreyCurve.Δ (P : FreyPackage) : P.FreyCurve.Δ = (P.a*P.b*P.c)^(2*P.p) / 2 ^ 8 := by
  trans (P.a ^ P.p) ^ 2 * (P.b ^ P.p) ^ 2 * (P.c ^ P.p) ^ 2 / 2 ^ 8
  · field_simp
    norm_cast
    simp [← P.hFLT, WeierstrassCurve.Δ, FreyCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  · simp [← mul_pow, ← pow_mul, mul_comm 2]

instance (P : FreyPackage) : WeierstrassCurve.IsElliptic (FreyCurve P) where
  isUnit := by
    rw [FreyCurve.Δ, isUnit_iff_ne_zero]
    apply div_ne_zero
    · norm_cast
      exact pow_ne_zero _ <| mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0
    · norm_num

lemma FreyCurve.b₂ (P : FreyPackage) :
    P.FreyCurve.b₂ = P.b ^ P.p - P.a ^ P.p := by
  simp [FreyCurve, WeierstrassCurve.b₂]
  ring

lemma FreyCurve.b₄ (P : FreyPackage) :
    P.FreyCurve.b₄ = - (P.a * P.b) ^ P.p / 8 := by
  simp [FreyCurve, WeierstrassCurve.b₄]
  ring

lemma FreyCurve.c₄ (P : FreyPackage) :
    P.FreyCurve.c₄ = (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2 := by
  simp [FreyCurve.b₂, FreyCurve.b₄, WeierstrassCurve.c₄]
  ring

lemma FreyCurve.c₄' (P : FreyPackage) :
    P.FreyCurve.c₄ = P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p := by
  rw [FreyCurve.c₄]
  rw_mod_cast [pow_mul', ← hFLT]
  ring

lemma FreyCurve.Δ'inv (P : FreyPackage) :
    (↑(P.FreyCurve.Δ'⁻¹) : ℚ) = 2 ^ 8 / (P.a*P.b*P.c)^(2*P.p) := by
  simp [FreyCurve.Δ]

lemma FreyCurve.j (P : FreyPackage) :
    P.FreyCurve.j = 2^8*(P.c^(2*P.p)-(P.a*P.b)^P.p) ^ 3 /(P.a*P.b*P.c)^(2*P.p) := by
  rw [mul_div_right_comm, WeierstrassCurve.j, FreyCurve.Δ'inv, FreyCurve.c₄']

private lemma j_pos_aux (a b : ℤ) (hb : b ≠ 0) : 0 < (a + b) ^ 2 - a * b := by
  rify
  calc
    (0 : ℝ) < (a ^ 2 + (a + b) ^ 2 + b ^ 2) / 2 := by positivity
    _ = (a + b) ^ 2 - a * b := by ring

/-- The q-adic valuation of the j-invariant of the Frey curve is a multiple of p if 2 < q is
a prime of bad reduction. -/
lemma FreyCurve.j_valuation_of_bad_prime (P : FreyPackage) {q : ℕ} (hqPrime : q.Prime)
    (hqbad : (q : ℤ) ∣ P.a * P.b * P.c) (hqodd : 2 < q) :
    (P.p : ℤ) ∣ padicValRat q P.FreyCurve.j := by
  have := Fact.mk hqPrime
  have hqPrime' := Nat.prime_iff_prime_int.mp hqPrime
  have h₀ : ((P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p) ^ 3 : ℚ) ≠ 0 := by
    rw_mod_cast [pow_mul', ← P.hFLT, mul_pow]
    exact pow_ne_zero _ <| ne_of_gt <| j_pos_aux _ _ (pow_ne_zero _ P.hb0)
  have h₁ : P.a * P.b * P.c ≠ 0 := mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0
  rw [FreyCurve.j, padicValRat.div (mul_ne_zero (by norm_num) h₀) (pow_ne_zero _ (mod_cast h₁)),
    padicValRat.mul (by norm_num) h₀, padicValRat.pow two_ne_zero, ← Nat.cast_two,
    ← padicValRat_of_nat, padicValNat_primes hqodd.ne', Nat.cast_zero, mul_zero, zero_add]
  have : ¬ (q : ℤ) ∣ (P.c^(2*P.p)-(P.a*P.b)^P.p) ^ 3 := by
    rw [hqPrime'.dvd_pow_iff_dvd three_ne_zero]
    have hq' : Xor' ((q : ℤ) ∣ P.a * P.b) ((q : ℤ) ∣ P.c) := by
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
    Int.cast_pow, padicValRat.pow (mod_cast h₁), dvd_neg, Nat.cast_mul]
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

end FreyPackage

/-!

Given an elliptic curve over `ℚ`, the p-torsion points defined over an algebraic
closure of `ℚ` are a 2-dimensional Galois representation. What can we say about the Galois
representation attached to the p-torsion of the Frey curve attached to a Frey package?

It follows (after a little work!) from a profound theorem of Mazur that this representation
must be irreducible.

-/

abbrev Qbar := AlgebraicClosure ℚ

open WeierstrassCurve
theorem Mazur_Frey (P : FreyPackage) :
    IsSimpleModule (ZMod P.p) (P.FreyCurve.torsionGaloisRepresentation P.p Qbar).asModule := sorry

/-!

But it follows from a profound theorem of Ribet, and the even more profound theorem
(proved by Wiles) that the Frey Curve is modular, that the representation cannot be irreducible.

-/

theorem Wiles_Frey (P : FreyPackage) :
    ¬ IsSimpleModule (ZMod P.p) (P.FreyCurve.torsionGaloisRepresentation P.p Qbar).asModule := sorry

/-!

It follows that there is no Frey package.

-/

/-- There is no Frey package. This profound result is proved using
work of Mazur and Wiles/Ribet to rule out all possibilities for the
$p$-torsion in the corresponding Frey curve. -/
theorem FreyPackage.false (P : FreyPackage) : False := by
  -- by Wiles' result, the p-torsion is not irreducible
  apply Wiles_Frey P
  -- but by Mazur's result, the p-torsion is irreducible!
  exact Mazur_Frey P
  -- Contradiction!

-- Fermat's Last Theorem is true
theorem Wiles_Taylor_Wiles : FermatLastTheorem := by
  refine of_p_ge_5 fun p hp5 pp a b c ha hb _ h ↦  Nonempty.elim ?_ FreyPackage.false
  apply FreyPackage.of_not_FermatLastTheorem_p_ge_5 (a := a) (b := b) (c := c)
    <;> assumption_mod_cast
