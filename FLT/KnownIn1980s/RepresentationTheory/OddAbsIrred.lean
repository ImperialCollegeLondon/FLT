/-
<<<<<<< HEAD
Irreducible ↔ absolutely irreducible, given a 1-dimensional fixed space
=======
Copyright (c) 2026 YOUR NAME HERE. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: YOUR NAME HERE
>>>>>>> 1f2c3dbb599cf63c40fb56ffd5bfa3d037a4914b
-/
module

public import Mathlib

public import FLT.Slop.RepresentationTheory.OddAbsIrredSlop

/-!
# Irreducible ↔ absolutely irreducible, given a one-dimensional fixed space

Let `ρ` be a finite-dimensional representation of a monoid `G` over a field
`k`, and suppose that some `g : G` has a one-dimensional fixed subspace
`V^g = {v | ρ g v = v}`.  The main result of this file,
`OddRep.isIrreducible_iff_isAbsolutelyIrreducible`, asserts that `ρ` is
irreducible if and only if it is absolutely irreducible, that is, irreducible
after base change to an algebraic closure of `k`
(`OddRep.IsAbsolutelyIrreducible`).

A typical application is to an odd two-dimensional Galois representation in
characteristic `≠ 2`, where complex conjugation has eigenvalues `1` and `-1`
and hence a one-dimensional fixed space.

The definitions `OddRep.fixedSpace`, `OddRep.baseChange` and
`OddRep.IsAbsolutelyIrreducible`, together with the proof and all supporting
lemmas, are in `FLT.Slop.RepresentationTheory.OddAbsIrredSlop`.
-/

public section

open Module

namespace OddRep

variable {k : Type*} [Field k]
variable {G : Type*} [Monoid G]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- **Proposition 1.2 / Theorem 1.3.** Let `V` be a finite-dimensional vector
space over `k` and `ρ : G →* GL(V)` a representation.  If some `g : G` has a
one-dimensional fixed subspace `V^g`, then `V` is irreducible if and only if it
is absolutely irreducible. -/
theorem isIrreducible_iff_isAbsolutelyIrreducible
    (ρ : Representation k G V) [FiniteDimensional k V]
    {g : G} (hg : finrank k (fixedSpace ρ g) = 1) :
    ρ.IsIrreducible ↔ IsAbsolutelyIrreducible ρ :=
  isIrreducible_iff_isAbsolutelyIrreducible_slop ρ hg

end OddRep

end
