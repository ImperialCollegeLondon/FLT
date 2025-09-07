/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib
import FLT.Deformations.LiftFunctor

/-

# Hardly ramified representations

Say `ℓ ≥ 3` is a prime, `k` is am algebraic extension of `ZMod ℓ` and `R` is a projective
limit of Artin local rings with residue field `k`, equipped with the projective limit
topology. A representation `ρ : G_Q → GL_2(R)` is said to be *hardly ramified* if

1) `det ρ` is the mod `ℓ` cyclotomic character;
2) `ρ` is unramified outside 2ℓ;
3) `ρ|_{G_ℓ}` is flat (by which I mean all quotients `G_Q → GL_2(R/I)` with `I` open
   come from finite flat group schemes, ); and
4) `ρ|_{G_2}` has a 1-dimensional unramified quotient.

NB we might strengthen (4) to "1-dimensional quotient on which Galois acts
by an unramified character whose square is trivial".

It is standard (although the full proof is long and needs the theory of the Tate curve, as
well as many standard facts about elliptic curves such as the Weil pairing) that the `ℓ`-torsion
in the Frey curve is hardly ramified. It is a deep theorem (originally due to Wiles, but now
it follows from the proof of Serre's conjecture) that any hardly ramified
Galois representation must be reducible.

**TODO** did Andrew define flatness correctly in the case `R=k[[eps1,eps2,eps3,...]]`?
-/

namespace GaloisRepresentation

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

structure IsHardlyRamified {ℓ : ℕ} [Fact ℓ.Prime] (hp : Odd ℓ)
    {V : Type*} [AddCommGroup V] [Module (ZMod ℓ) V]
    [Module.Finite (ZMod ℓ) V] (hdim : Module.rank (ZMod ℓ) V = 2)
    (ρ : GaloisRep ℚ (ZMod ℓ) V) : Prop where
  det : (sorry : Prop) --∀ g v, ρ.det g v = PadicInt.toZMod (cyclotomicCharacter Qbar ℓ (g.toRingEquiv))
  isUnramified : ∀ p, p ≠ 2 ∧ p ≠ ℓ → (sorry : Prop)
  isFlat : ρ.IsFlatAt (ℓ : IsDedekindDomain.HeightOneSpectrum _)
  isTameAtTwo : (sorry : Prop)

end GaloisRepresentation
