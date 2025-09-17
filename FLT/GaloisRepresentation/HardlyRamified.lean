/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.Deformations.Categories
import FLT.Deformations.RepresentationTheory.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal

/-

# Hardly ramified representations

Say `ℓ ≥ 3` is a prime, `k` is an algebraic extension of `ZMod ℓ` and `R` is a projective
limit of Artin local rings with residue field `k`, equipped with the projective limit
topology. Let `V` be an `R`-module, free of rank 2 and with the product topology
(i.e., the `R`-module topology). A representation `ρ : G_Q → GL_R(V)` is said to be
*hardly ramified* if

1) `det ρ` is the mod `ℓ` cyclotomic character;
2) `ρ` is unramified outside `2ℓ`;
3) `ρ|_{G_ℓ}` is flat (by which I mean all quotients `G_Q → GL_(R/I)(V/I)` with `I` open
   come from finite flat group schemes); and
4) there is a `G_2`-stable exact sequence `0 → K → V → W → 0` with `K` and `W` `R`-free of
rank 1, and where `ρ` acts on `W` via an unramified character whose square is trivial.

It is standard (although the full proof is long and needs the theory of the Tate curve, as
well as many standard facts about elliptic curves such as the Weil pairing) that the `ℓ`-torsion
in the Frey curve is hardly ramified. It is a deep theorem (originally due to Wiles, but now
it follows from the proof of Serre's conjecture) that any hardly ramified
Galois representation to `GL_2(k)` must be reducible, as Serre's predicted weight is 2 and
the predicted level is 1 or 2.

**TODO** did Andrew define flatness correctly in the case `R=k[[eps1,eps2,eps3,...]]`?

**TODO** make definition
-/

open IsDedekindDomain
open scoped NumberField

def RingEquiv.heightOneSpectrum_comap {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (P : HeightOneSpectrum B) : HeightOneSpectrum A :=
  {
    asIdeal := .comap e P.asIdeal
    isPrime := P.asIdeal.comap_isPrime e
    ne_bot h := P.ne_bot <| Ideal.comap_injective_of_surjective e e.surjective <| by
      rw [h, Ideal.comap_bot_of_injective e e.injective]
  }

open IsDedekindDomain in
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

def Nat.Prime.toHeightOneSpectrumInt {p : ℕ} (hp : p.Prime) : HeightOneSpectrum ℤ where
  asIdeal := .span {(p : ℤ)}
  isPrime := by
    rwa [Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hp.ne_zero), ← prime_iff_prime_int]
  ne_bot := mt Submodule.span_singleton_eq_bot.mp (Int.ofNat_ne_zero.mpr hp.ne_zero)

noncomputable def Nat.Prime.toHeightOneSpectrumRingOfIntegersRat {p : ℕ} (hp : p.Prime) :
    IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
  Rat.ringOfIntegersEquiv.symm.heightOneSpectrum <| hp.toHeightOneSpectrumInt

namespace GaloisRepresentation

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "𝔪" => IsLocalRing.maximalIdeal

universe u

/-- A hardly ramified representation is a 2-dimensional representation of the absolute
Galois group of `ℚ` over quite a general "coefficient ring" with residue characteristig `ℓ > 2`,
which has cyclotomic determinant, is unramified outside `2ℓ`, flat at `ℓ` and upper-triangular
at 2 with a 1-dimensional quotient which is unramified and whose square is trivial. -/
structure IsHardlyRamified {ℓ : ℕ} [Fact ℓ.Prime] (hℓOdd : Odd ℓ)
    (𝒪 : Type u) [CommRing 𝒪] [Algebra ℤ_[ℓ] 𝒪] [IsLocalHom (algebraMap ℤ_[ℓ] 𝒪)]
    (R : Type u) [CommRing R] [TopologicalSpace R]
    [Algebra 𝒪 R] [Algebra ℤ_[ℓ] R] [IsScalarTower ℤ_[ℓ] 𝒪 R]
    [Deformation.IsLocalProartinianAlgebra 𝒪 R]
    {V : Type*} [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Free R V] (hdim : Module.rank R V = 2)
    (ρ : GaloisRep ℚ R V) : Prop where
  det : ∀ g, ρ.det g = algebraMap ℤ_[ℓ] R (cyclotomicCharacter (ℚ ᵃˡᵍ) ℓ g.toRingEquiv)
  isUnramified : ∀ p (hp : p.Prime), p ≠ 2 ∧ p ≠ ℓ →
    ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat
  isFlat : ρ.IsFlatAt (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime))
  isTameAtTwo : ∃ (π : V →ₗ[R] R) (hπ : Function.Surjective π) (δ : GaloisRep ℚ_[2] R R),
    -- δ is unramified and
    (sorry ≤ δ.ker) ∧
    (∀ g : Γ ℚ_[2], δ g * δ g = 1) ∧
    ∀ g : Γ ℚ_[2], ∀ v : V, π (ρ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v)

end GaloisRepresentation

  /-

  TODO

  2) Define tame at 2
  -/
