import Mathlib.Data.PNat.Basic
import Mathlib.NumberTheory.FLT.Four
import Mathlib

/-!
This file proves many of the key results which reduce Fermat's Last Theorem
to Mazur's theorem and the Wiles-Taylor-Wiles theorem.

# Main definitions

* `FreyPackage` : A Frey Package is the data of nonzero coprime integers
$(a,b,c)$ and a prime $p \geq 5$ such that $a^p+b^p=c^p$ and furthermore
such that $a$ is 3 mod 4 and $b$ is 0 mod 2.

The motivation behind this definition is that then all the results in Section 4.1
of Serre's paper [Serre] apply to the elliptic curve curve $Y^2=X(X-a^p)(X+b^p).$

# Main theorems

* `FLT.FreyPackage.of_not_FermatLastTheorem` : A counterexample
     to `FermatLastTheorem` gives a Frey Package.
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

/-- Fermat's Last Theorem is true when n = 3. -/
lemma fermatLastTheoremThree : FermatLastTheoremFor 3 := sorry
-- This is proved in the FLT-regular project: see
-- https://github.com/leanprover-community/flt-regular/blob/861b7df057140b45b8bb7d30d33426ffbbdda52b/FltRegular/FltThree/FltThree.lean#L698
-- The way to turn this node green is to port that work to mathlib so we can use it here.

namespace FLT


/-- If Fermat's Last Theorem is false, there's a nontrivial solution to a^p+b^p=c^p with p>=5 prime. -/
lemma p_ge_5_counterexample_of_not_FermatLastTheorem (h : ¬ FermatLastTheorem) :
    ∃ (a b c : ℤ) (_ : a ≠ 0) (_ : b ≠ 0) (_ : c ≠ 0) (p : ℕ) (_ : p.Prime) (_ : 5 ≤ p),
    a^p + b^p = c^p := by
  apply (mt FermatLastTheorem.of_odd_primes) at h
  push_neg at h
  rcases h with ⟨p, hpprime, hpodd, (h : ¬ ∀ _, _)⟩
  push_neg at h
  rcases h with ⟨a, b, c, ha, hb, hc, h⟩
  have hp3 : p ≠ 3 := by
    rintro rfl
    revert h
    apply fermatLastTheoremThree <;> assumption
  refine ⟨a, b, c, by exact_mod_cast ha, by exact_mod_cast hb, by exact_mod_cast hc, p, hpprime, ?_, by exact_mod_cast h⟩
  -- now just need to prove that if p is an odd prime and p ≠ 3 then p ≥ 5
  by_contra hp5
  push_neg at hp5
  interval_cases p
  · exact Nat.not_prime_zero hpprime
  · exact Nat.not_prime_one hpprime
  · simp only [Nat.odd_iff_not_even, even_two, not_true_eq_false] at hpodd
  · norm_num at hp3
  · norm_num at hpprime

/--
A *Frey Package* is a 4-tuple (a,b,c,p) of integers
satisfying some axioms (including $a^p+b^p=c^p$).
The axioms imply that all of
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
  hp5 : 5 ≤ p
  hFLT : a ^ p + b ^ p = c ^ p
  hgcdab : gcd a b = 1 -- same as saying a,b,c pairwise coprime
  ha4 : (a : ZMod 4) = 3
  hb2 : (b : ZMod 2) = 0

namespace FreyPackage

namespace of_not_FermatLastTheorem

/-- This function will only be applied when the input integers $a$, $b$, $c$
are all nonzero, pairwise coprime, and satisfy $a^p+b^p=c^p$ with $p$ odd.
Under these hypotheses, it produces a possibly different Fermat counterexample
of the same form but which furthermore has $a\cong 3$ mod 4 and $b$ even. It does this
by possibly permuting a,b,c and changing signs. -/
def aux₁ (a₁ b₁ c₁ : ℤ) :
    ℤ × ℤ × ℤ :=
  match (b₁ : ZMod 2) with
  | 0 => -- b is even
    match (a₁ : ZMod 4) with
    | 3 => (a₁, b₁, c₁) -- answer if b is even and a is 3 mod 4
    | _ => (-a₁, -b₁, -c₁) -- answer if b is even and a is 1 mod 4
  | _ => -- b is odd
    match (a₁ : ZMod 2) with
    | 0 => -- b is odd and a is even
      match (b₁ : ZMod 4) with
      | 3 => (b₁, a₁, c₁) -- answer if b is 3 mod 4 and a is even
      | _ => (-b₁,-a₁,-c₁) -- answer if b is 1 mod 4 and a is even
    | _ => -- b and a are both odd
      match (a₁ : ZMod 4) with
      | 3 => (a₁, -c₁, -b₁) -- answer if a is 3 mod 4 and b is odd
      | _ => (-a₁, c₁, b₁) -- answer if a is 1 mod 4 and b is odd

variable {a : ℤ} (b c : ℤ)
variable {a₁ : ℤ} (b₁ c₁ : ℤ)

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

-- couldn't get `fin_cases` to wotk with a general term
lemma ZMod4cases (q : ZMod 4) : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by
    fin_cases q <;> tauto

-- more of these lemmas should be proved, to shorten the proof of aux₁.ha4
lemma aux {b} (hd : gcd a b = 1) (h1 : 2 ∣ a) (h2 : 2 ∣ b) : False := by
  have := dvd_gcd h1 h2
  rw [hd] at this
  norm_num at this

-- this is pretty long. I should pull out more lemmas like the above,
-- e.g. proofs of things like "if x is odd and x mod 4 isn't 3 then it's 1"
lemma aux₁.ha4 (hab : gcd a₁ b₁ = 1) : ((aux₁ a₁ b₁ c₁).1 : ZMod 4) = 3 := by
  simp only [aux₁]
  split
  · rename_i _ b_even
    split
    · rename_i _ a3mod4
      exact a3mod4
    · rename_i _ a1mod4
      have foo : 2 ∣ b₁ := by
        exact (ZMod.int_cast_zmod_eq_zero_iff_dvd b₁ 2).mp b_even
      have bar : ¬ 2 ∣ a₁ := by
        intro h
        apply aux _ h foo
        rename_i x x_1
        simp_all only [ne_eq, Fin.zero_eta, gcd_eq_zero_iff, false_and, not_false_eq_true]
      -- want to do fin_cases on (-a₁ : ZMod 4)
      rcases ZMod4cases (-a₁ : ℤ) with (h | h | h | h)
      · rw [ZMod.int_cast_zmod_eq_zero_iff_dvd] at h
        simp only [Nat.cast_ofNat, dvd_neg] at h
        exfalso
        apply bar
        refine dvd_trans ?_ h
        norm_num
      · exfalso
        apply a1mod4
        simp only [Int.cast_neg, neg_eq_iff_eq_neg] at h
        rw [h]
        decide
      · exfalso
        apply bar
        simp only [Int.cast_neg, ← add_eq_zero_iff_neg_eq] at h
        have foo : ((a₁ + 2 : ℤ) : ZMod 4) = 0 := by assumption_mod_cast
        rw [ZMod.int_cast_zmod_eq_zero_iff_dvd] at foo
        rw [← dvd_add_left (c := 2) (by norm_num)]
        refine dvd_trans ?_ foo
        norm_num
      · exact h
  · rename_i hb1
    split
    · split
      · rename_i _ b3mod4
        exact b3mod4
      · rename_i _ b1mod4
        -- now need to check a
        rcases ZMod4cases b₁ with (h | h | h | h)
        · rw [ZMod.int_cast_zmod_eq_zero_iff_dvd] at h
          simp only [Nat.cast_ofNat, dvd_neg] at h
          exfalso
          apply hb1
          simp only [Fin.zero_eta, ZMod.int_cast_zmod_eq_zero_iff_dvd]
          refine dvd_trans ?_ h
          norm_num
        · simp [h]
          decide
        · rw [← sub_eq_zero] at h
          have foo : ((b₁ - 2 : ℤ) : ZMod 4) = 0 := by assumption_mod_cast
          exfalso
          apply hb1
          rw [ZMod.int_cast_zmod_eq_zero_iff_dvd] at foo
          apply (ZMod.int_cast_zmod_eq_zero_iff_dvd _ 2).2
          rw [← dvd_sub_left (c := 2) (by norm_num)]
          refine dvd_trans ?_ foo
          norm_num
        · contradiction
    · rename_i _ a_odd
      split
      · rename_i _ a3mod4
        exact a3mod4
      · rename_i _ a1mod4
        rcases ZMod4cases a₁ with (h | h | h | h)
        · exfalso
          apply a_odd
          change _ = 0
          rw [ZMod.int_cast_zmod_eq_zero_iff_dvd] at h ⊢
          refine dvd_trans ?_ h
          norm_num
        · simp [h]
          decide
        · exfalso
          apply a_odd
          change _ = 0
          rw [ZMod.int_cast_zmod_eq_zero_iff_dvd]
          rw [← dvd_sub_left (c := 2) (by norm_num)]
          rw [← sub_eq_zero] at h
          have foo : ((a₁ - 2 : ℤ) : ZMod 4) = 0 := by assumption_mod_cast
          rw [ZMod.int_cast_zmod_eq_zero_iff_dvd] at foo
          refine dvd_trans ?_ foo
          norm_num
        · exfalso
          apply a1mod4
          exact h
  done

end of_not_FermatLastTheorem

-- these sorries below are quite long and tedious to fill in. See for example the
-- proof of `ha4` above.

/-- Given a counterexample to Fermat's Last Theorem with a,b,c coprime and p ≥ 5, we can make
a Frey package. -/
def of_not_FermatLastTheorem_coprime_p_ge_5 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
  (hab : gcd a b = 1) (p : ℕ) (hpprime : p.Prime)
  (hp : 5 ≤ p) (h : a^p + b^p = c^p) : FreyPackage where
    a := (of_not_FermatLastTheorem.aux₁ a b c).1
    b := (of_not_FermatLastTheorem.aux₁ a b c).2.1
    c := (of_not_FermatLastTheorem.aux₁ a b c).2.2
    ha0 := sorry
    hb0 := sorry
    hc0 := sorry
    p := p
    hp5 := hp
    hFLT := sorry
    hgcdab := sorry
    ha4 := of_not_FermatLastTheorem.aux₁.ha4 b c hab
    hb2 := sorry

lemma gcdab_eq_gcdac {a b c : ℤ} {p : ℕ} (hp : 0 < p) (h : a ^ p + b ^ p = c ^ p) :
    gcd a b = gcd a c := by
  have foo : gcd a b ∣ gcd a c := by
    apply dvd_gcd (gcd_dvd_left a b)
    rw [← Int.pow_dvd_pow_iff hp, ← h]
    apply dvd_add
    · rw [Int.pow_dvd_pow_iff hp]
      exact gcd_dvd_left a b
    · rw [Int.pow_dvd_pow_iff hp]
      exact gcd_dvd_right a b
  have bar : gcd a c ∣ gcd a b := by
    apply dvd_gcd (gcd_dvd_left a c)
    have h2 : b ^ p = c ^ p - a ^ p := eq_sub_of_add_eq' h
    rw [← Int.pow_dvd_pow_iff hp, h2]
    apply dvd_add
    · rw [Int.pow_dvd_pow_iff hp]
      exact gcd_dvd_right a c
    · rw [dvd_neg]
      rw [Int.pow_dvd_pow_iff hp]
      exact gcd_dvd_left a c
  change _ ∣ (Int.gcd a c : ℤ) at foo
  apply Int.ofNat_dvd.1 at bar
  apply Int.ofNat_dvd.1 at foo
  exact congr_arg ((↑) : ℕ → ℤ) <| Nat.dvd_antisymm foo bar
  done

/-- Given a counterexample a^p+b^p=c^p to Fermat's Last Theorem with p>=5, there exists a Frey package. -/
def of_not_FermatLastTheorem_p_ge_5 {a b c : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    {p : ℕ} (hpprime : p.Prime) (hp : 5 ≤ p) (h : a^p + b^p = c^p) : FreyPackage :=
  let d := gcd a b
  have hd : d ≠ 0 := by aesop
  of_not_FermatLastTheorem_coprime_p_ge_5
    (show a / d ≠ 0 by exact left_div_gcd_ne_zero ha)
    (show b / d ≠ 0 by exact right_div_gcd_ne_zero hb)
    (show c / gcd a b ≠ 0 by
      rw [gcdab_eq_gcdac _ h]
      · exact right_div_gcd_ne_zero hc
      · linarith)
    (by
      simp [gcd]
      rw [Int.gcd_div_gcd_div_gcd]
      apply Int.gcd_pos_of_ne_zero_left _ ha)
    p hpprime hp <| by
  obtain ⟨a₁, (ha : a = d * a₁)⟩ := gcd_dvd_left a b
  rw [gcdab_eq_gcdac (by linarith) h]
  nth_rewrite 1 [ha]
  rw [Int.mul_ediv_cancel_left _ hd]
  obtain ⟨b₁, (hb : b = d * b₁)⟩ := gcd_dvd_right a b
  rw [hb]
  rw [Int.mul_ediv_cancel_left _ hd]
  obtain ⟨c₁, hc⟩ : gcd a c ∣ c := gcd_dvd_right a c
  rw [← gcdab_eq_gcdac (by linarith) h] at hc
  nth_rewrite 1 [hc]
  rw [gcdab_eq_gcdac (by linarith) h]
  rw [Int.mul_ediv_cancel_left _ (by rwa [← gcdab_eq_gcdac (by linarith) h])]
  change c = d * c₁ at hc
  rw [ha, hb, hc, mul_pow, mul_pow, mul_pow] at h
  have help : d ^ p ≠ 0 := pow_ne_zero _ hd
  rw [← mul_add] at h
  exact (Int.mul_eq_mul_left_iff help).mp h

/-- If Fermat's Last Theorem is false, there exists a Frey package. -/
lemma of_not_FermatLastTheorem (h : ¬ FermatLastTheorem) : Nonempty (FreyPackage) :=
  let ⟨a, b, c, ha, hb, hc, p, hpprime, hp, h⟩ := p_ge_5_counterexample_of_not_FermatLastTheorem h
  ⟨of_not_FermatLastTheorem_p_ge_5 ha hb hc hpprime hp h⟩

end FreyPackage

/-- The elliptic curve associated to a Frey package. The conditions imposed
upon a Frey package guarantee that the running hypotheses in
Section 4.1 of [Serre] all hold. -/
def FreyCurve (P : FreyPackage) : EllipticCurve ℚ := {
    a₁ := 1
    a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
    a₃ := 0
    a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16
    a₆ := 0
    Δ' := ⟨- (P.a ^ P.p) ^ 2 * (P.b ^ P.p) ^ 2 * (P.c ^ P.p) ^ 2 / 2 ^ 8, -- or whatever it comes out to be with Lean's conventions
      sorry, -- whatever 1 / the right answer is,
      sorry, sorry⟩ -- unwise to embark on these until `coe_Δ'` is proved
    coe_Δ' := sorry -- check that the discriminant is correctly computed.
  }

namespace FreyCurve

abbrev Qbar := AlgebraicClosure ℚ

open WeierstrassCurve

def p_torsion (P : FreyPackage) : Type := sorry -- (FreyCurve P)⟮Qbar⟯[p]

variable (P : FreyPackage)

instance : AddCommGroup (FreyCurve.p_torsion P) := sorry
instance : Module (ZMod P.p) (FreyCurve.p_torsion P) := sorry

def mod_p_Galois_representation (P : FreyPackage) :
    Representation (ZMod P.p) (Qbar ≃ₗ[ℚ] Qbar) (FreyCurve.p_torsion P) := sorry

/-!

What can we say about this representation? It follows from a profound theorem
of Mazur (and much other work) that this representation must be irreducible.

-/

theorem Mazur_Frey (P : FreyPackage) :
    IsSimpleModule (ZMod P.p) (mod_p_Galois_representation P).asModule := sorry

/-!

But it follows from a profound theorem of Ribet, and fact (proved by Wiles) that the Frey Curve
is modular, that the representation cannot be irreducible.

-/

theorem Wiles_Frey (P : FreyPackage) :
    ¬ IsSimpleModule (ZMod P.p) (mod_p_Galois_representation P).asModule := sorry

end FreyCurve

/-!

It follows that there is no Frey package.

-/

/-- There is no Frey package. This profound result is proved using
work of Mazur and Wiles/Ribet to rule out all possibilities for the
$p$-torsion in the corresponding Frey curve. -/
theorem FreyPackage.false (P : FreyPackage) : False := by
  apply FreyCurve.Wiles_Frey P
  exact FreyCurve.Mazur_Frey P


theorem Wiles_Taylor_Wiles : FermatLastTheorem := by
  -- assume FLT is false
  by_contra h
  -- get the Frey package
  obtain ⟨P⟩ := FreyPackage.of_not_FermatLastTheorem h
  -- But there is no Frey package
  exact P.false
