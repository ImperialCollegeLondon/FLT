/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Topology.Algebra.Constructions
import Mathlib.Tactic.Bound.Init

/-!
# Units

Material destined for Mathlib.
-/

@[expose] public section

lemma Submonoid.units_isOpen {M : Type*} [TopologicalSpace M] [Monoid M]
  {U : Submonoid M} (hU : IsOpen (U : Set M)) : IsOpen (U.units : Set Mˣ) :=
  (hU.preimage Units.continuous_val).inter (hU.preimage Units.continuous_coe_inv)
