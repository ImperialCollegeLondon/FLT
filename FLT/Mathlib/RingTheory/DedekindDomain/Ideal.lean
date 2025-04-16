import Mathlib
import Mathlib.RingTheory.DedekindDomain.Ideal

universe u v

namespace Polynomial

variable {K : Type u} [Field K] [DecidableEq K]
  [DecidableEq (Ideal K[X])]
  {P : Multiset (K[X])}
  (prime : ∀ p ∈ P, Prime (p))
  (non_zero : ∀ p ∈ P, p ≠ 0)

noncomputable def ringEquiv_chineseReminder :
    K[X] ⧸ Ideal.span {∏ᶠ p ∈ P, (p ^ (P.count p))} ≃+* Π p : P.toFinset, K[X] ⧸ Ideal.span {p.1} ^ (P.count p.1) := by
  let 𝓟 := ∏ᶠ p ∈ P, (p ^ (P.count p))
  have h𝓟 : 𝓟 ≠ 0 := sorry
  let I := (Multiset.map (fun p ↦ Ideal.span {p}) P)
  let 𝓘 := Ideal.span { 𝓟 }
  have h𝓘 : 𝓘 ≠ ⊥ := by
    by_contra h
    rw [Ideal.span_singleton_eq_bot] at h
    exact h𝓟 h
  have h𝓘_fact : UniqueFactorizationMonoid.factors 𝓘 = I :=
    sorry
  let φ := IsDedekindDomain.quotientEquivPiFactors h𝓘
  rw [h𝓘_fact] at φ
  have : ((J : { x // x ∈ I.toFinset }) → K[X] ⧸ J.1 ^ I.count J.1) =
      ((p : { x // x ∈ P.toFinset }) → K[X] ⧸ Ideal.span { p.1 } ^ P.count (p.1)) := by
    unfold I
    sorry -- exact fails, so there is a missing lemma with prod indexed by multiset and Multiset.map
  exact φ.trans sorry

end Polynomial
