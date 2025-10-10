/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.Deformations.Categories
import FLT.Deformations.RepresentationTheory.Basic
import FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
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

namespace GaloisRepresentation

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K
local notation3 "𝔪" => IsLocalRing.maximalIdeal

universe u

/-- Z2bar is the ring of integers of `ℚ_[2]ᵃˡᵍ`. -/
noncomputable abbrev Z2bar : ValuationSubring (ℚ_[2]ᵃˡᵍ) := Valued.v.valuationSubring

instance : MulAction (Γ ℚ_[2]) Z2bar where
  smul g z := ⟨g z, by
    obtain ⟨z, hz⟩ := z
    rw [Valuation.mem_valuationSubring_iff] at hz ⊢
    convert hz using 1
    apply NNReal.coe_injective
    exact (spectralNorm_eq_of_equiv g z).symm⟩
  one_smul z := rfl
  mul_smul g h z := rfl

/-- Let `R` be a compact Hausdorff local toppologcal ring (for example any complete Noetherian
local ring with the maximal ideal-adic topology) having finite residue field of
characteristic `ℓ > 2`, and let `ρ : Gal(Qbar/Q) → GL_2(R)` be a continuous 2-dimensional
representation. We say that `ρ` is *hardly ramified* if it has cyclotomic determinant, is
unramified outside `2ℓ`, flat at `ℓ` and upper-triangular at 2 with a 1-dimensional quotient which
is unramified and whose square is trivial. -/
structure IsHardlyRamified {ℓ : ℕ} [Fact ℓ.Prime] (hℓOdd : Odd ℓ)
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [Algebra ℤ_[ℓ] R] --[IsLocalHom (algebraMap ℤ_[ℓ] R)] -- a convenient way of saying "residue
    -- field has char ell"
    -- Rather than GL_2(R) we use the automorphisms of a finite free rank 2 `R`-module `V`.
    {V : Type*} [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Free R V] (hdim : Module.rank R V = 2)
  -- Let `ρ` be a continuous action of the absolute Galois group of `ℚ` on `V`.
    (ρ : GaloisRep ℚ R V) : Prop where
  -- We define *IsHardlyRamified* to mean:
  -- `det(ρ)` is the ell-adic cyclotomic character;
  det : ∀ g, ρ.det g = algebraMap ℤ_[ℓ] R (cyclotomicCharacter (ℚ ᵃˡᵍ) ℓ g.toRingEquiv)
  -- `ρ` is unramified outside `2` and `ℓ`;
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

namespace IsHardlyRamified

section mod_p_rep_lifts

universe v

variable {k : Type u} [Fintype k] [Field k]
    [TopologicalSpace k] [DiscreteTopology k]
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    [Algebra ℤ_[p] k]
    [IsLocalHom (algebraMap ℤ_[p] k)]
    (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2)

open TensorProduct

/-- A mod p hardly ramified represntation lifts to a p-adic one.
-/
theorem lifts (ρ : GaloisRep ℚ k V) (hρirred : ρ.IsIrreducible)
    (hρ : IsHardlyRamified hpodd hV ρ) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsLocalRing R)
      (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : Algebra ℤ_[p] R) (_ : IsLocalHom (algebraMap ℤ_[p] R))
      (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R)
      (_ : Algebra R k) (_ : IsScalarTower ℤ_[p] R k) (_ : ContinuousSMul R k)
      (W : Type v) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
      (_ : Module.Free R W) (hW : Module.rank R W = 2)
      (σ : GaloisRep ℚ R W) (r : k ⊗[R] W ≃ₗ[k] V),
    IsHardlyRamified hpodd hW σ ∧ (σ.baseChange k).conj r = ρ := sorry

end mod_p_rep_lifts

section spreads_out

-- A p-adic hardly ramified extension spreads out into a compatible family
-- of ell-adic ones

end spreads_out

section three

-- A mod 3 hardly ramified representation is an extension of trivial by cyclo
theorem mod_three {k : Type u} [Fintype k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
    ∀ g : Γ ℚ, ∀ v : V, π (ρ g v) = π v := by
  sorry

--A 3-adic hardly ramified representation has trace(Frob_q)=1+q for all q!=2,3
theorem three_adic {R : Type u} [CommRing R] [Algebra ℤ_[3] R] [Module.Finite ℤ_[3] R]
    [Module.Free ℤ_[3] R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsModuleTopology ℤ_[3] R]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V]
    (hV : Module.rank R V = 2) {ρ : GaloisRep ℚ R V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∀ p (_ : Nat.Prime p) (hp : 5 ≤ p), 2+2=4 := sorry

end three

end IsHardlyRamified

end GaloisRepresentation
