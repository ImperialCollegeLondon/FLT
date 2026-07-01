/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Basic.Lemmas
public import FLT.FreyCurve.Basic
public import FLT.EllipticCurve.Torsion
public import FLT.FreyCurve.Mazur

/-!
# The proof of Fermat's Last Theorem

This file contains the "main spine" of the proof of Fermat's
Last Theorem.

-/

@[expose] public section

theorem flt : FermatLastTheorem := by
  -- Fermat's Last Theorem is implied by FLT for p>=5 prime
  apply FermatLastTheorem.of_p_ge_5
  -- FLT for p>=5 prime is implied by the fact that there
  -- is no Frey package.
  apply FreyPackage.fermatLastTheoremFor_p_ge_5
  -- So assume for a contradiction that a Frey package `P` exists, and let
  -- `E : Y^2=X(X-a^p)(X+b^p)` be the corresponding Frey curve.
  rw [isEmpty_iff]
  intro P
  let E := P.freyCurve
  let p := P.p
  have : Fact p.Prime := ⟨P.pp⟩
  -- Now let `ρbar` be the Galois representation on the p-torsion of the curve.
  let ρbar := (E.galoisRep p P.hppos)
  -- Deep work of Mazur from the 1970s implies that `ρbar` is an irreducible
  -- Galois representation;
  have ρbar_irred : GaloisRep.IsIrreducible ρbar := P.mazur
  -- But deep work of Wiles, Ribet and others shows that this cannot hold,
  -- the contraction we seek.
  sorry

/-

** TODO **

Mazur => E[p] irreducible?
-/
