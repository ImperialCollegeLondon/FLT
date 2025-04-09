import Mathlib
import Mathlib.RingTheory.DedekindDomain.Ideal

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
  {ι : Type v} {s : Finset ι}
  (P : ι → Ideal R)
  (coprime : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (P i) (P j))

namespace IsDedekindDomain

-- I think that making this into a R-AlgEquiv discovers a diamond. When trying to synth
-- that the RHS is a R-algebra it ends up needed that the Ideal quotienting by is a semiring,
-- which it might not be
noncomputable def ringEquiv_chineseReminder
  (coprime : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (P i) (P j)) :
    R ⧸ ∏ᶠ i : s, (P i) ≃+* Π i : s, R ⧸ (P i) where
  toFun := Pi.ringHom (fun (j : s) ↦
    have h : ∏ᶠ i : s, (P i) ≤ (P j) := by
      apply Ideal.le_of_dvd
      use ∏ᶠ (k : s) (hk : k ≠ j), P k
      rw [mul_finprod_cond_ne (α := s) (a := j) (f := fun t ↦ (P t))]
      exact Finite.Set.subset ⊤ le_top
    Ideal.Quotient.factor h
  )
  invFun := sorry
  left_inv := sorry
  right_inv := sorry
  map_mul' x y := by simp
  map_add' x y := by simp

end IsDedekindDomain

namespace Polynomial

variable {R : Type u} [Field R]
  {ι : Type v} {s : Finset ι}
  (P : ι → R[X])
  (e : ι → ℕ)
  (prime : ∀ i ∈ s, Prime (P i) ∧ P i ≠ 0)
  (coprime : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (P i) (P j))

noncomputable def ringEquiv_chineseReminder :
    R[X] ⧸ Ideal.span {∏ᶠ i : s, ((P i) ^ (e i))} ≃+* Π i : s, R[X] ⧸ Ideal.span {(P i) ^ (e i)} := by
  let φ := IsDedekindDomain.ringEquiv_chineseReminder
    (fun i ↦ Ideal.span {P i})
    e
    (by
      intro i hi
      have := Ideal.span_singleton_prime (prime i hi).2
      have := this.mpr (prime i hi).1
      simp only
      obtain bot | prime := Ideal.isPrime_iff_bot_or_prime.mp this
      . by_contra
        rw [Ideal.span_singleton_eq_bot] at bot
        exact (prime i hi).2 bot
      . exact prime
    )
    (by
      intro i hi j hj hij
      by_contra h
      simp only at h
      have := (Ideal.isCoprime_span_singleton_iff (P i) (P j)).mpr (coprime i hi j hj hij)
      rw [h] at this
      rw [isCoprime_self] at this
      sorry
    )
  sorry
  --rw [Ideal.prod_span_singleton] at φ
  --exact φ

end Polynomial
