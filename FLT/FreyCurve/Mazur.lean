/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone
-/
module

public import FLT.FreyCurve.Basic
public import FLT.EllipticCurve.Torsion
import FLT.GaloisRepresentation.HardlyRamified.Frey
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import FLT.Assumptions.KnownIn1980s
/-!

# Irreducibility of the p-torsion of the Frey curve

A deep result of Mazur implies that the Frey curve is irreducible.

-/

@[expose] public section

open WeierstrassCurve

/--
The p-torsion in the Frey curve associated to a counterexample to FLT is irreducible.
-/
theorem FreyPackage.mazur (P : FreyPackage) :
    let E := P.freyCurve
    let p := P.p
    have : Fact p.Prime := ⟨P.pp⟩
    GaloisRep.IsIrreducible (E.galoisRep p P.hppos) := by
  -- this is in Serre's 1987 Duke paper.
  knownin1980s
