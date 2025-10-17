import FLT.GaloisRepresentation.HardlyRamified.Frey
/-!

# Preliminary reductions of FLT

This file reduces Fermat's Last Theorem
to Mazur's theorem and the Wiles/Taylor--Wiles theorem.

# Main theorems

* `FLT.FreyPackage.false`: There is no Frey Package.
* `Wiles_Taylor_Wiles` : Fermat's Last Theorem is true.

-/

/-!

Given an elliptic curve over `ℚ`, the p-torsion points defined over an algebraic
closure of `ℚ` are a 2-dimensional Galois representation.

What can we say about the Galois
representation attached to the p-torsion of the Frey curve attached to a Frey package?

It follows (after a little work!) from a profound theorem of Mazur that this representation
must be irreducible.

-/

abbrev Qbar := AlgebraicClosure ℚ
noncomputable local instance : DecidableEq Qbar := Classical.typeDecidableEq Qbar

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
  FLT.FreyPackage.FreyCurve.torsion_not_isIrreducible P

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

-- Fermat's Last Theorem is true
theorem Wiles_Taylor_Wiles : FermatLastTheorem := by
  refine FermatLastTheorem.of_p_ge_5
    fun p hp5 pp a b c ha hb _ h ↦ Nonempty.elim ?_ FreyPackage.false
  apply FreyPackage.of_not_FermatLastTheorem_p_ge_5 (a := a) (b := b) (c := c)
    <;> assumption_mod_cast
