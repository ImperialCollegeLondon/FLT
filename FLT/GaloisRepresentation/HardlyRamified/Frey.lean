/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import FLT.Basic.FreyPackage
public import FLT.EllipticCurve.Torsion
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# The Frey curve gives a hardly ramified representation

We prove that the `ℓ`-torsion of the Frey curve attached to a Frey package
is a hardly ramified Galois representation, and that this representation is
irreducible.
-/

@[expose] public section

variable (P : FreyPackage)

open GaloisRepresentation

/-- The natural `ℤ_p`-algebra structure on `ℤ/pℤ`. -/
noncomputable local instance (p : ℕ) [Fact p.Prime] : Algebra ℤ_[p] (ZMod p) :=
  RingHom.toAlgebra PadicInt.toZMod

/-- We cannot hope to make a constructive decidable equality on `AlgebraicClosure ℚ` because
it is defined in a completely nonconstructive way, so we add the classical instance. -/
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

theorem FreyCurve.torsion_isHardlyRamified :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    IsHardlyRamified P.hp_odd sorry
      (P.freyCurve.galoisRep P.p (show 0 < P.p from P.hppos)) :=
  sorry

theorem FreyCurve.torsion_not_isIrreducible :
    haveI : Fact (P.p.Prime) := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) :=
  sorry -- TODO prove this
