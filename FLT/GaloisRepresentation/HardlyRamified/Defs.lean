/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.Deformations.Categories
import FLT.Deformations.RepresentationTheory.GaloisRep
import FLT.Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import FLT.Assumptions.KnownIn1980s
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.Localization
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
open scoped NumberField TensorProduct

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

/-- Let `R` be a compact Hausdorff local topological ring (for example any complete Noetherian
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
  -- We say `ρ` is *hardly ramified* if
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

theorem baseChange_hardlyRamified {ℓ : ℕ} [Fact ℓ.Prime] (hℓOdd : Odd ℓ)
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [Algebra ℤ_[ℓ] R]
    (S : Type u) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [IsLocalRing S]
    [Algebra R S] [Algebra ℤ_[ℓ] S] [ContinuousSMul R S] [IsScalarTower ℤ_[ℓ] R S]
    {V : Type*} [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Free R V] (hdim : Module.rank R V = 2)
    (ρ : GaloisRep ℚ R V) : IsHardlyRamified hℓOdd hdim ρ →
      IsHardlyRamified hℓOdd (by rw [Module.rank_baseChange, hdim]; exact Cardinal.lift_two)
      (GaloisRep.baseChange S ρ) := sorry

theorem conj_hardlyRamified {ℓ : ℕ} [Fact ℓ.Prime] (hℓOdd : Odd ℓ)
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [Algebra ℤ_[ℓ] R] {V : Type*} [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Free R V] (hdimV : Module.rank R V = 2)
    {W : Type*} [AddCommGroup W] [Module R W]
    [Module.Finite R W] [Module.Free R W] (hdimW : Module.rank R W = 2)
    (e : V ≃ₗ[R] W) (ρ : GaloisRep ℚ R V) : IsHardlyRamified hℓOdd hdimV ρ ↔
    IsHardlyRamified hℓOdd hdimW (GaloisRep.conj ρ e) := sorry

instance {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsDomain R] : ContinuousSMul R (FractionRing R) := by
      apply continuousSMul_of_algebraMap R (FractionRing R)
      exact RingTopology.coinduced_continuous ⇑(algebraMap R (FractionRing R))

set_option linter.unusedVariables false in
theorem hardlyRamified_of_hardlyRamified_isogenous {ℓ : ℕ} [Fact ℓ.Prime] (hℓOdd : Odd ℓ)
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [IsDomain R] [Algebra ℤ_[ℓ] R]
    {V : Type*} [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Free R V] (hdimV : Module.rank R V = 2)
    {W : Type*} [AddCommGroup W] [Module R W]
    [Module.Finite R W] [Module.Free R W] (hdimW : Module.rank R W = 2)
    (ρ : GaloisRep ℚ R V) (σ : GaloisRep ℚ R W)
    (e : (FractionRing R) ⊗[R] V ≃ₗ[FractionRing R] (FractionRing R) ⊗[R] W)
    (he : GaloisRep.conj (GaloisRep.baseChange (FractionRing R) ρ) e =
      (GaloisRep.baseChange (FractionRing R) σ)) :
    IsHardlyRamified hℓOdd hdimV ρ ↔ IsHardlyRamified hℓOdd hdimW σ := knownin1980s


noncomputable def complexConjugationReal : Γ ℝ := sorry

theorem complexConjugationReal_order_two : orderOf complexConjugationReal = 2 := sorry

noncomputable def complexConjugation : Γ ℚ := (Field.absoluteGaloisGroup.mapAux (Rat.castHom ℝ))
  complexConjugationReal

theorem complexConjugation_order_two : orderOf complexConjugation = 2 := by
  rw [orderOf_eq_prime_iff]
  constructor
  · unfold complexConjugation
    rw [← map_pow, ← complexConjugationReal_order_two, pow_orderOf_eq_one, map_one]
  · sorry

theorem odd_of_hardlyRamified {ℓ : ℕ} [Fact ℓ.Prime] (hℓOdd : Odd ℓ)
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLocalRing R]
    [Algebra ℤ_[ℓ] R] {V : Type*} [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Free R V] (hdim : Module.rank R V = 2)
    (ρ : GaloisRep ℚ R V) (hρ : IsHardlyRamified hℓOdd hdim ρ) : GaloisRep.det ρ complexConjugation
    = -1 := sorry

theorem isAbsolutelyIrreducible_of_irreducible_odd {R : Type*} [TopologicalSpace R] [Field R]
    [IsTopologicalRing R] {V : Type*} [AddCommGroup V] [Module R V] [Module.Finite R V]
    (hV : Module.rank R V = 2) (ρ : GaloisRep ℚ R V) (ρodd : GaloisRep.det ρ complexConjugation
    = -1) (hρ : GaloisRep.IsIrreducible ρ) : GaloisRep.IsAbsolutelyIrreducible ρ := sorry

end GaloisRepresentation
