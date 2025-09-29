/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.Deformations.Categories
import FLT.Deformations.RepresentationTheory.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
/-

# Hardly ramified representations

Let `R` be a complete local Noetherian ring with residue charactestic `p>2` (or a slightly
more general class of topological ring) and let
$\rho:Gal(\overline{\mathbb{Q}}/\mathbb{Q})\to GL_2(R)$ be a continuous Galois
representation. We say that `ρ` is *hardly ramified* if it has cyclotomic determinant, is
unramified outside `2p`, is flat at `p` and (possibly after conjugation) is
upper-triangular at 2 with unramified quotient of order 1 or 2.

The reason this definition is useful to us is that the `p`-torsion in the Frey
curve is hardly ramified (this is standard, although the full proof is long and needs the
theory of the Tate curve, as well as many standard facts about elliptic curves such as the
Weil pairing). Serre's conjecture says that such a representation cannot be irreducible
(as it should be modular of weight 2 and level 2).

Furthermore, mod `p` hardly ramified representations can be lifted to characteristic zero,
and `p`-adic hardly ramified representations can be put into compatible families (these are
hard theorems). Finally, 3-adic hardly ramified representations can be classified
(this is also a hard theorem).

## More details

Say `ℓ ≥ 3` is a prime, `k` is a finite field of characteristic `ℓ` and `R` is a projective
limit of Artin local rings with residue field `k` along local ring maps which induce
the identity on `k`. Give the Artin local rings the discrete topology and `R` the
projective limit topology, so that `R` is profinite.

Let `V` be an `R`-module, free of rank 2 and with the product topology
(i.e., the `R`-module topology). A representation `ρ : G_Q → GL_R(V)` is said to be
*hardly ramified* if

1) `det ρ` is the mod `ℓ` cyclotomic character;
2) `ρ` is unramified outside `2ℓ`;
3) `ρ|_{G_ℓ}` is flat (this means that for every open ideal `I` of `R`, the representation
`G_Q → GL_(R/I)(V/I)` come from finite flat group schemes; note that `V/I` is a finite set); and
4) there is a `G_2`-stable exact sequence `0 → K → V → W → 0` with `K` and `W` `R`-free of
rank 1, and where `ρ` acts on `W` via an unramified character whose square is trivial.

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

noncomputable abbrev Z2bar : ValuationSubring (ℚ_[2]ᵃˡᵍ) := Valued.v.valuationSubring
noncomputable example : Z2bar →+ ℚ_[2]ᵃˡᵍ := by exact Z2bar.subtype.toAddMonoidHom

instance : MulAction (Γ ℚ_[2]) Z2bar where
  smul g z := ⟨g z, by
    obtain ⟨z, hz⟩ := z
    rw [Valuation.mem_valuationSubring_iff] at hz ⊢
    convert hz using 1
    apply NNReal.coe_injective
    exact (spectralNorm_eq_of_equiv g z).symm⟩
  one_smul z := rfl
  mul_smul g h z := rfl

/-- Let `R` be a "local pro-artinian algebra" (for example any complete Noetherian local ring
with the maximal ideal-adic topology) having finite residue field of characteristic `ℓ > 2`,
and let `ρ : Gal(Qbar/Q) → GL_2(R)` be a continuous 2-dimensional representation.
We say that `ρ` is *hardly ramified* if it has cyclotomic determinant, is unramified outside `2ℓ`,
flat at `ℓ` and upper-triangular at 2 with a 1-dimensional quotient which is unramified and
whose square is trivial. -/
structure IsHardlyRamified {ℓ : ℕ} [Fact ℓ.Prime] (hℓOdd : Odd ℓ)
    -- In applications `𝓞` will be the integers of a finite extension of `ℚ_[ℓ]`;
    -- we assume `𝓞` acts on the coefficient ring `R` as it is technically convenient
    -- to build in this extra action.
    (𝒪 : Type u) [CommRing 𝒪] [Algebra ℤ_[ℓ] 𝒪] [IsLocalHom (algebraMap ℤ_[ℓ] 𝒪)]
    (R : Type u) [CommRing R] [TopologicalSpace R]
    [Algebra 𝒪 R] [Algebra ℤ_[ℓ] R] [IsScalarTower ℤ_[ℓ] 𝒪 R]
    [Deformation.IsLocalProartinianAlgebra 𝒪 R]
    -- Rather than GL_2(R) we use the automorphisms of a finite free rank 2 `R`-module.
    {V : Type*} [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Free R V] (hdim : Module.rank R V = 2)
  -- Let `ρ` be a continuous action of the absolute Galois group of `ℚ` on V.
    (ρ : GaloisRep ℚ R V) : Prop where
  -- We define *IsHardlyRamified* to mean:
  -- det(ρ) is the ell-adic cyclotomic character;
  det : ∀ g, ρ.det g = algebraMap ℤ_[ℓ] R (cyclotomicCharacter (ℚ ᵃˡᵍ) ℓ g.toRingEquiv)
  -- ρ is unramified outside 2 and ℓ;
  isUnramified : ∀ p (hp : p.Prime), p ≠ 2 ∧ p ≠ ℓ →
    ρ.IsUnramifiedAt hp.toHeightOneSpectrumRingOfIntegersRat
  -- ρ is flat at ℓ;
  isFlat : ρ.IsFlatAt (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (Fact.out : ℓ.Prime))
  -- and ρ has a 1-dimensional quotient π : ρ → δ such that
  isTameAtTwo : ∃ (π : V →ₗ[R] R) (_ : Function.Surjective π) (δ : GaloisRep ℚ_[2] R R),
    ∀ g : Γ ℚ_[2], ∀ v : V, π (ρ.map (algebraMap ℚ ℚ_[2]) g v) = δ g (π v) ∧
    -- δ is unramified and
    (AddSubgroup.inertia ((𝔪 Z2bar).toAddSubgroup : AddSubgroup Z2bar) (Γ ℚ_[2]) ≤ δ.ker) ∧
    -- δ² = 1.
    (∀ g : Γ ℚ_[2], δ g * δ g = 1)

end GaloisRepresentation
