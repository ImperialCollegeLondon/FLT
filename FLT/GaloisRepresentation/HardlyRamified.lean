/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import Mathlib
import FLT.Deformations.LiftFunctor

/-

# Hardly ramified representations

Say `ℓ ≥ 3` is a prime. A representation `ρ : G_Q → GL_2(F_ℓ)` is said to be
*hardly ramified* if

1) `det ρ` is the mod `ℓ` cyclotomic character;
2) `ρ` is unramified outside 2ℓ;
3) `ρ|_{G_ℓ}` is flat; and
4) `ρ|_{G_2}^ss` is unramified.

It is relatively straightforward that the `ℓ`-torsion in the Frey curve is
hardly ramified. It is a deep theorem (originally due to Wiles, but now
it follows from the proof of Serre's conjecture) that any hardly ramified
Galois representation must be reducible.
-/

namespace GaloisRepresentation

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

structure IsHardlyRamified {ℓ : ℕ} [Fact ℓ.Prime] (hp : Odd ℓ)
    {V : Type*} [AddCommGroup V] [Module (ZMod ℓ) V]
    [Module.Finite (ZMod ℓ) V] (hdim : Module.rank (ZMod ℓ) V = 2)
    (ρ : GaloisRep ℚ (ZMod ℓ) V) : Prop where
  det : 2+2=4--∀ g v, ρ.det g v = PadicInt.toZMod (cyclotomicCharacter Qbar ℓ (g.toRingEquiv))
  isUnramified : ∀ p, p ≠ 2 ∧ p ≠ ℓ → 2+2=4
  isFlat : ρ.IsFlatAt (ℓ : IsDedekindDomain.HeightOneSpectrum _)
  isTameAtTwo : 2+2=4

end GaloisRepresentation
