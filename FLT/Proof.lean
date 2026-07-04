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

The strategy of the proof is to prove the theorem via a series
of reductions. In other words, we will define mathematical statements
B_1=FLT, B_2, B_3, B_4, ..., up to around B_{12}, and then prove
that B_2 implies B_1, B_3 implies B_2, B_4 implies B_3 etc etc,
and then ultimately that B_{12} is true.

-/

@[expose] public section

namespace FLT.Bosses

/-

## Statements of the intermediate "Boss theorems"

Important note: because verso does not allow me a chapter 0, all
these labels are off-by-one from the 2026 course notes.
-/

/-- B1 is the statement of FLT. -/
def B1 : Prop := FermatLastTheorem

/-- B2 is the statement that FLT is true for primes p ≥ 5. -/
def B2 : Prop := ∀ p ≥ 5, Nat.Prime p → FermatLastTheoremFor p

/-- B3 is the statement that there is no Frey Package.
A Frey package is 4 integers a,b,c,p satisfying a^p+b^p=c^p and
some other conditions (for example p is prime and at least 5,
a,b,c are pairwise coprime etc). These conditions guarantee that the
associated Frey curve Y^2=X(X-a^p)(X+b^p) is semistable. -/
def B3 : Prop := IsEmpty FreyPackage

/-- B4 is the statement that if E is the Frey curve attached
to a Frey package (a,b,c,p), then E[p] is a reducible Galois representation. -/
def B4 : Prop :=
  ∀ P : FreyPackage,
  let E := P.freyCurve
  let p := P.p
  have : Fact p.Prime := ⟨P.pp⟩
  let ρbar := (E.galoisRep p P.hppos)
  ¬ GaloisRep.IsIrreducible ρbar

/-
B5 : If ell>=5 and rhobar:G_Q->GL_2(Z/ell Z) is continuous
and hardly ramified then rhobar is reducible.

B6:
a) If rhobar:G_Q->GL_2(Z/ell Z) is irreducible and hardly ramified
then rhobar lifts to rho:G_Q->GL_2(O_K) hardly ramified and
whose base extension to K is irreducible
b) The rho constructed in (a) is part of a weakly compatible
family of hardly ramified representations
c) Any haardly ramified 3-adic representation is an extension
of trivial by cyclotomic


-/

theorem B2_implies_B1 : B2 → B1 := FermatLastTheorem.of_p_ge_5

theorem B3_implies_B2 : B3 → B2 :=
  FreyPackage.fermatLastTheoremFor_p_ge_5

theorem B4_implies_B3 : B4 → B3 := by
  unfold B3 B4
  intro h
  rw [isEmpty_iff]
  intro P
  let E := P.freyCurve
  let p := P.p
  have : Fact p.Prime := ⟨P.pp⟩
  -- Now let `ρbar` be the Galois representation on the p-torsion of the curve.
  let ρbar := (E.galoisRep p P.hppos)
  -- Deep work of Mazur from the 1970s implies that `ρbar` is an irreducible
  -- Galois representation;
  apply h P
  exact P.mazur

theorem B4_proof : B4 :=
  sorry

theorem B3_proof : B3 := B4_implies_B3 B4_proof

theorem B2_proof : B2 := B3_implies_B2 B3_proof

theorem B1_proof : B1 := B2_implies_B1 B2_proof

end FLT.Bosses

open FLT.Bosses

theorem flt : FermatLastTheorem :=
  B1_proof
