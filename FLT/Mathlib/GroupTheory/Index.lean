/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kevin Buzzard
-/
module

public meta import Mathlib.Tactic.ToDual
import Mathlib.Data.Finset.Attr
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.ScopedNS
import Mathlib.Tactic.SetLike

/-!
# TODO

* Rename `relindex` to `relIndex`
* Rename `FiniteIndex.finiteIndex` to `FiniteIndex.index_ne_zero`
-/

@[expose] public section

open Function
open scoped Pointwise

-- This is cool notation. Should mathlib have it? And what should the `relindex` version be?
/-- Notation `[G : H]` for the (additive) index of a subgroup `H ≤ G`. -/
scoped[GroupTheory] notation "[" G ":" H "]" => @AddSubgroup.index G _ H
