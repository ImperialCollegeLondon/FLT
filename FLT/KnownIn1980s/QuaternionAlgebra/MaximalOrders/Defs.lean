/-
Copyright (c) 2026 Jack McCarthy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McCarthy
-/
module

public import Mathlib

/-!
# Orders in quaternion algebras

Definitions used to state Voight's maximal-order theorem for quaternion algebras over
number fields.
-/

@[expose] public section

namespace VoightMaximalOrder

/-! ### `R`-lattices -/

section RLattice

variable (R F V : Type*)
  [CommRing R] [Field F] [Algebra R F] [IsFractionRing R F]
  [AddCommGroup V] [Module R V] [Module F V] [IsScalarTower R F V]

/-- **Voight, *Quaternion Algebras*, Definition 9.3.1.** An `R`-lattice in a
finite-dimensional `F`-vector space `V`, where `F = Frac R`, is a finitely generated
`R`-submodule `M` whose `F`-span is all of `V`. -/
structure IsRLattice (M : Submodule R V) : Prop where
  /-- `M` is finitely generated as an `R`-module. -/
  moduleFinite : Module.Finite R M
  /-- The `F`-span of `M` is all of `V`. -/
  spans : Submodule.span F (M : Set V) = ⊤

end RLattice

/-! ### `R`-orders in an `F`-algebra -/

section Order

variable (R F B : Type*)
  [CommRing R] [Field F] [Algebra R F] [IsFractionRing R F]
  [Ring B] [Algebra R B] [Algebra F B] [IsScalarTower R F B] [FiniteDimensional F B]

/-- An `R`-order in a finite-dimensional `F`-algebra `B`, with `F = Frac R`.
Since `O : Subalgebra R B` is already a subring containing `R`, being an order is exactly
that its underlying `R`-submodule is an `R`-lattice in `B`. -/
def IsOrder (O : Subalgebra R B) : Prop :=
  IsRLattice R F B O.toSubmodule

/-- A maximal `R`-order in `B`: an order maximal under inclusion among orders. -/
def IsMaximalOrder (O : Subalgebra R B) : Prop :=
  Maximal (IsOrder R F B) O

end Order

end VoightMaximalOrder
