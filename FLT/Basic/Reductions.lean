import Mathlib.Data.PNat.Basic
import Mathlib.NumberTheory.FLT.Four
import Mathlib

/-!
This results shows that Fermat's Last Theorem for positive integers,
as formulated in the main `FLT.lean` file, follows from the mathlib
formalisation of Fermat's Last Theorem.
-/

theorem PNat.pow_add_pow_ne_pow_of_FermatLastTheorem :
    FermatLastTheorem → ∀ (a b c : ℕ+) (n : ℕ) (_ : n > 2),
    a ^ n + b ^ n ≠ c ^ n := by
  intro h₁ a b c n h₂
  specialize h₁ n h₂ a b c (by simp) (by simp) (by simp)
  assumption_mod_cast

namespace FLT

/-!

A *Frey Package* is a 4-tuple (a,b,c,p) of integers
satisfying some axioms. The axioms imply that all of
the all the results in section 4.1 of Serre's paper "Sur les
représentations modulaire de degré 2 de
$$Gal(\overline{\mathbb{Q}}/\mathbb{Q})$$"
apply to the choice of solution $$A=a^p$$, $$B=b^p$$ and $$C=-c^p$$ to $$A+B+C=0.$$
-/
structure Frey_package where
  a : ℤ
  b : ℤ
  c : ℤ
  ha0 : a ≠ 0
  hb0 : b ≠ 0
  hc0 : c ≠ 0
  p : ℕ
  hp5 : 5 ≤ p
  hFLT : a ^ p + b ^ p = c ^ p
  hgcdab : gcd a b = 1 -- same as saying a,b,c pairwise coprime
  ha4 : (a : ZMod 4) = 3
  hb2 : (b : ZMod 2) = 0

namespace Frey_package

lemma hgcdac (P : Frey_package) : gcd P.a P.c = 1 := by
  sorry -- see below

lemma hgcdbc (P : Frey_package) : gcd P.b P.c = 1 := by
  sorry -- these should be one issue

/-- The elliptic curve associated to a Frey package. The conditions imposed
upon a Frey package guarantee that the running hypotheses in
Section 4.1 of [Serre] all hold. -/
def FreyCurve (P : Frey_package) : EllipticCurve ℚ := {
    a₁ := 1
    a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
    a₃ := 0
    a₄ := - (P.a ^ P.p) * (P.b ^ P.p) / 16
    a₆ := 0
    Δ' :=
    ⟨- (P.a ^ P.p) ^ 2 * (P.b ^ P.p) ^ 2 * (P.c ^ P.p) ^ 2 / 2 ^ 8, -- or whatever it comes out to be with Lean's conventions
           sorry, -- whatever 1 / the right answer is,
           sorry, sorry⟩
    coe_Δ' := sorry -- this should be an issue.
  }

/-- There is no Frey package. -/
theorem false (P : Frey_package) : False := by
  /- Let E be the global minimal model of the corresponding
    Frey curve. -/
  let E : EllipticCurve ℚ := FreyCurve P
  let G : Type := sorry -- Gal(Q-bar/Q)
  let i : Group G := sorry
  let V : Type := sorry -- E[p]
  let i : AddCommGroup V := sorry
  let i : Module (ZMod P.p) V := sorry
  let ρ : Representation (ZMod P.p) G V := sorry -- action of G on E[p]
  sorry -- case split on whether ρ is reducible or not.

end Frey_package

theorem FermatLastTheorem.of_prime_ge_5 (p : ℕ) (hp₁ : p.Prime) (hp₂ : p ≥ 5) :
    FermatLastTheoremFor p := by
  -- need to make a Frey package and then use no_Frey_package

  sorry

theorem Wiles_Taylor_Wiles : FermatLastTheorem := by
  apply FermatLastTheorem.of_odd_primes
  intros p hp₁ hp₂
  by_cases h : p = 3
  · cases h
    -- ⊢ FermatLastTheoremFor 3
    sorry -- issue
  · apply FermatLastTheorem.of_prime_ge_5 p hp₁
    by_contra h2
    push_neg at h2
    interval_cases p
    · aesop
    · aesop
    · aesop
    · aesop
    · simp [parity_simps] at hp₂
