import Mathlib.Tactic

open NumberField

variable {K : Type} [Field K] [NumberField K]

/-A maximal ideal and a prime number `p` are associated if the characteristic
of the residue field is equal to `p`-/
def IsAssociated (P : Ideal (𝓞 K)) [Ideal.IsMaximal P] (p : Nat.Primes) : Prop :=
  CharP ((𝓞 K) ⧸ P) p

--previously this was p ∈ P

lemma IsAssociated_iff_char (P : Ideal (𝓞 K)) [Ideal.IsMaximal P] (p : Nat.Primes) :
    IsAssociated P p ↔ CharP ((𝓞 K) ⧸ P) p := Iff.rfl

instance (p : Nat.Primes) : Fact (Nat.Prime p) := by
  cases' p with p hp
  constructor
  exact hp

lemma Residue_Finite (P : Ideal (𝓞 K)) [Ideal.IsMaximal P] [Fintype ((𝓞 K) ⧸ P)] :
    Finite ((𝓞 K) ⧸ P) := by
  have h : Fintype ((𝓞 K) ⧸ P) := by infer_instance
  exact Fintype.finite h

lemma residue_char_ne_zero (P : Ideal (𝓞 K)) [Ideal.IsMaximal P] [Fintype ((𝓞 K) ⧸ P)] :
    ringChar ((𝓞 K) ⧸ P) ≠ 0 := by
    have h1 : CharP ((𝓞 K) ⧸ P) (ringChar ((𝓞 K) ⧸ P)) := ringChar.charP ((𝓞 K) ⧸ P)
    have h2 : Finite ((𝓞 K) ⧸ P) := Residue_Finite P
    exact CharP.char_ne_zero_of_finite ((𝓞 K) ⧸ P) (ringChar ((𝓞 K) ⧸ P))

/-hahaha `IsAssociated_Nat_Prime_unique` works unchanges after changing the definition of
`IsAssociated` all these proofs could probably be simplified because they were written for
a different definition. But if its not broken...-/

set_option synthInstance.maxHeartbeats 40000 in
lemma IsAssociated_Nat_Prime_unique (P : Ideal (𝓞 K))
    [Ideal.IsMaximal P] [Fintype ((𝓞 K) ⧸ P)] : ∃! (p : Nat.Primes), IsAssociated P p := by
  have h : ∃! (p : ℕ), CharP ((𝓞 K) ⧸ P) p := CharP.exists_unique ((𝓞 K) ⧸ P)
  cases' h with p hp
  dsimp only at hp
  cases' hp with hchar hU
  have h1 : Nat.Prime p ∨ p = 0 := CharP.char_is_prime_or_zero ((𝓞 K) ⧸ P) p
  have h2 : p ≠ 0 := by
    have h : p = ringChar ((𝓞 K) ⧸ P) := (ringChar.eq ((𝓞 K) ⧸ P) p).symm
    rw [h]
    exact residue_char_ne_zero P
  have h3 : Nat.Prime p := by
    cases' h1 with h' h''
    · exact h'
    · exfalso
      apply h2
      exact h''
  let p : Nat.Primes := by
    rw [Nat.Primes]
    exact { val := p, property := h3 }
  use p
  dsimp
  constructor
  · exact (IsAssociated_iff_char P { val := p, property := h3 }).mpr hchar
  · intro y hIsA
    rw [IsAssociated_iff_char] at hIsA
    specialize hU y
    apply hU at hIsA
    exact (Nat.Primes.coe_nat_inj y { val := p, property := h3 }).mp hIsA
/-The prime number that a maximal ideal lies over-/
noncomputable def PrimeLyingAbove (P : Ideal (𝓞 K)) [Ideal.IsMaximal P]
    [Fintype ((𝓞 K) ⧸ P)]: Nat.Primes :=
  Classical.choose (IsAssociated_Nat_Prime_unique P)
