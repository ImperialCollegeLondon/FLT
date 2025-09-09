/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import FLT.Deformations.LiftFunctor
import FLT.Deformations.RepresentationTheory.Basic


/-

# Hardly ramified representations

Say `ℓ ≥ 3` is a prime, `k` is am algebraic extension of `ZMod ℓ` and `R` is a projective
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

namespace GaloisRepresentation

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

/-- A hardly ramified representation is a 2-dimensional representation of the absolute
Galois group of `ℚ` over quite a general local base with residue characteristig `ℓ > 2`,
which has cyclotomic determinant, is unramified outside `2ℓ`, flat at `ℓ` and upper-triangular
at 2 with a 1-dimensional quotient which is unramified and whose square is trivial. -/
structure IsHardlyRamified {ℓ : ℕ} [Fact ℓ.Prime] (hp : Odd ℓ)
    {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [IsLocalRing R] (hl : (ℓ : R) ∈ IsLocalRing.maximalIdeal R)
    {V : Type*} [AddCommGroup V] [Module R V]
    [Module.Finite R V] [Module.Free R V] (hdim : Module.rank R V = 2)
    (ρ : GaloisRep ℚ R V) : Prop where
  det : (sorry : Prop) --
    -- ∀ g v, ρ.det g v = PadicInt.toZMod (cyclotomicCharacter Qbar ℓ (g.toRingEquiv))
  isUnramified : ∀ p, p ≠ 2 ∧ p ≠ ℓ → (sorry : Prop)
  isFlat : (sorry : Prop) -- ρ.IsFlatAt (ℓ : IsDedekindDomain.HeightOneSpectrum _)
  isTameAtTwo : (sorry : Prop)

end GaloisRepresentation
#min_imports
