/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone
-/
module

public import FLT.Basic.FreyPackage
public import FLT.EllipticCurve.Torsion
import FLT.GaloisRepresentation.HardlyRamified.Frey
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.NumberTheory.ArithmeticFunction.Misc
/-!

# Preliminary reductions of FLT

This file reduces Fermat's Last Theorem
to Mazur's theorem and the Wiles/Taylor--Wiles theorem.

# Main theorems

* `FLT.FreyPackage.false`: There is no Frey Package.
* `Wiles_Taylor_Wiles` : Fermat's Last Theorem is true.

-/

@[expose] public section

/-!

Given an elliptic curve over `ℚ`, the p-torsion points defined over an algebraic
closure of `ℚ` are a 2-dimensional Galois representation.

What can we say about the Galois
representation attached to the p-torsion of the Frey curve attached to a Frey package?

It follows (after a little work!) from a profound theorem of Mazur that this representation
must be irreducible.

-/

/-- A classical decidable instance on `AlgebraicClosure ℚ`, given that there is
no hope of a constructive one with the current definition of algebraic closure. -/
noncomputable local instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

open WeierstrassCurve

theorem Mazur_Frey (P : FreyPackage) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) :=
  sorry

/-!

But it follows from a profound theorem of Ribet, and the even more profound theorem
(proved by Wiles) that the representation cannot be irreducible.

-/

theorem Wiles_Frey (P : FreyPackage) :
    haveI : Fact P.p.Prime := ⟨P.pp⟩
    ¬ GaloisRep.IsIrreducible (P.freyCurve.galoisRep P.p P.hppos) :=
  FreyCurve.torsion_not_isIrreducible P

/-!

It follows that there is no Frey package.

-/

/-- There is no Frey package. This profound result is proved using
work of Mazur and Wiles/Ribet to rule out all possibilities for the
$p$-torsion in the corresponding Frey curve. -/
theorem FreyPackage.false (P : FreyPackage) : False := by
  -- by Wiles' result, the p-torsion is not irreducible
  apply Wiles_Frey P
  -- but by Mazur's result, the p-torsion is irreducible!
  exact Mazur_Frey P
  -- Contradiction!

/-- Fermat's Last Theorem is true -/
theorem Wiles_Taylor_Wiles : FermatLastTheorem := by
  -- Suppose Fermat's Last Theorem is false
  by_contra h
  -- then there exists a Frey package
  obtain ⟨P : FreyPackage⟩ := FreyPackage.of_not_FermatLastTheorem h
  -- but there is no Frey package
  exact P.false
