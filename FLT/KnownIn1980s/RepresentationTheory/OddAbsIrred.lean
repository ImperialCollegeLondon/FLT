/-
Irreducible ↔ absolutely irreducible, given a 1-dimensional fixed space
-/

module

import Mathlib

public import FLT.Slop.RepresentationTheory.OddAbsIrredSlop

open scoped TensorProduct

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
    [FiniteDimensional k V]
    {g : G} (hg : finrank k (fixedSpace ρ g) = 1) :
    ρ.IsIrreducible ↔ IsAbsolutelyIrreducible ρ :=
  isIrreducible_iff_isAbsolutelyIrreducible_slop ρ hg
