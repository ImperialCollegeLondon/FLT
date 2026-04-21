module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

open IsDedekindDomain
open scoped NumberField

/-- Pulling back elements of `HeightOneSpectrum` along a ring isomorphism. -/
def RingEquiv.heightOneSpectrum_comap {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (P : HeightOneSpectrum B) : HeightOneSpectrum A :=
  {
    asIdeal := .comap e P.asIdeal
    isPrime := P.asIdeal.comap_isPrime e
    ne_bot h := P.ne_bot <| Ideal.comap_injective_of_surjective e e.surjective <| by
      rw [h, Ideal.comap_bot_of_injective e e.injective]
  }

open IsDedekindDomain in
/-- The bijection `HeightOneSpectrum A ≃ HeightOneSpectrum B` induced by a ring isomorphism
between `A` and `B`. -/
def RingEquiv.heightOneSpectrum {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    HeightOneSpectrum A ≃ HeightOneSpectrum B where
      toFun := e.symm.heightOneSpectrum_comap
      invFun := e.heightOneSpectrum_comap
      left_inv P := by
        ext1
        convert Ideal.comap_comap e.toRingHom e.symm.toRingHom
        simp
      right_inv Q := by
        ext1
        convert Ideal.comap_comap e.symm.toRingHom e.toRingHom
        simp

/-- The element of `HeightOneSpectrum ℤ` associated to a prime number. -/
def Nat.Prime.toHeightOneSpectrumInt {p : ℕ} (hp : p.Prime) : HeightOneSpectrum ℤ where
  asIdeal := .span {(p : ℤ)}
  isPrime := by
    rwa [Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hp.ne_zero), ← prime_iff_prime_int]
  ne_bot := mt Submodule.span_singleton_eq_bot.mp (Int.ofNat_ne_zero.mpr hp.ne_zero)

/-- The element of `HeightOneSpectrum (𝓞 ℚ)` associated to a prime number. -/
noncomputable def Nat.Prime.toHeightOneSpectrumRingOfIntegersRat {p : ℕ} (hp : p.Prime) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
  Rat.ringOfIntegersEquiv.symm.heightOneSpectrum <| hp.toHeightOneSpectrumInt
